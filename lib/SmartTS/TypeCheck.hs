-- | Bidirectional type checking for SmartTS (annotated locals, parameters, returns).
-- Designed to grow: judgments live here; surface 'Type' stays in "AST" until we add variables/schemes.
module SmartTS.TypeCheck
  ( typeCheckContract
  ) where

import Control.Monad.State
import Data.List (nub)
import qualified Data.Map.Strict as M
import SmartTS.AST

data Signature = Signature
  { formalArgs :: [Type]
  , returnType :: Type
  } deriving (Eq, Show)

data BindingKind = Param | LocalMutable | LocalImmutable
  deriving (Eq, Show)

data TcBinding = TcBinding
  { bindingKind :: BindingKind
  , bindingType :: Type
  }
  deriving (Eq, Show)

data TcEnv = TcEnv
  { envStorageType :: Type
  , envBindings :: M.Map Name TcBinding
  , envFunctionSignatures :: M.Map Name Signature
  , envReturnType :: Type
  }
  deriving (Eq, Show)

type TcM = StateT TcEnv (Either String)

tcError :: String -> TcM a
tcError = lift . Left

-- | Run an action in a child scope: state changes (new locals) do not escape.
withSavedEnv :: TcM a -> TcM a
withSavedEnv action = do
  saved <- get
  r <- action
  put saved
  return r

typeCheckContract :: Contract -> Either String ()
typeCheckContract c = do
  checkDuplicateStorage (contractStorage c)
  mapM_ (checkDuplicateParams . methodArgs) (contractMethods c)
  mapM_ (checkMethod c) (contractMethods c)

checkDuplicateStorage :: Storage -> Either String ()
checkDuplicateStorage fields =
  let names = map fst fields
   in if length names == length (nub names)
        then Right ()
        else Left "Duplicate field name in contract storage."

checkDuplicateParams :: [FormalParameter] -> Either String ()
checkDuplicateParams params =
  let names = map (\(FormalParameter n _) -> n) params
   in if length names == length (nub names)
        then Right ()
        else Left "Duplicate parameter name in method."

buildSigMap :: Contract -> M.Map Name Signature
buildSigMap c =
  M.fromList
    [ (methodName m, Signature
        { formalArgs = [t | FormalParameter _ t <- methodArgs m]
        , returnType = methodReturnType m
        })
    | m <- contractMethods c
    , methodKind m == Private
    ]

checkMethod :: Contract -> MethodDecl -> Either String ()
checkMethod c m =
  let storageT = TRecord (contractStorage c)
      paramMap =
        M.fromList
          [ (n, TcBinding Param t)
          | FormalParameter n t <- methodArgs m
          ]
      env0 =
        TcEnv
          { envStorageType = storageT
          , envBindings = paramMap
          , envFunctionSignatures = buildSigMap c
          , envReturnType = methodReturnType m
          }
   in case runStateT (checkStmt (methodBody m)) env0 of
        Left err -> Left err
        Right _ -> Right ()

-- | Check a statement; new locals are accumulated in the State.
checkStmt :: Stmt -> TcM ()
checkStmt (SequenceStmt ss) = mapM_ checkStmt ss
checkStmt (ReturnStmt e) = do
  t <- inferExpr e
  expected <- gets envReturnType
  lift $ expectType "return value" t expected
checkStmt (VarDeclStmt n typ e) = do
  noDuplicateLocal n
  t <- inferExpr e
  lift $ expectType ("initializer of var `" ++ n ++ "`") t typ
  modify $ insertLocal n LocalMutable typ
checkStmt (ValDeclStmt n typ e) = do
  noDuplicateLocal n
  t <- inferExpr e
  lift $ expectType ("initializer of val `" ++ n ++ "`") t typ
  modify $ insertLocal n LocalImmutable typ
checkStmt (AssignmentStmt lv e) = do
  checkAssignable lv
  tl <- typeOfLValue lv
  te <- inferExpr e
  lift $ expectType "assignment" te tl
checkStmt (IfStmt cond thn mel) = do
  tc <- inferExpr cond
  lift $ expectType "if condition" tc TBool
  withSavedEnv (checkStmt thn)
  case mel of
    Nothing -> return ()
    Just els -> withSavedEnv (checkStmt els)
checkStmt (WhileStmt cond body) = do
  tc <- inferExpr cond
  lift $ expectType "while condition" tc TBool
  withSavedEnv (checkStmt body)

noDuplicateLocal :: Name -> TcM ()
noDuplicateLocal n = do
  env <- get
  case M.lookup n (envBindings env) of
    Just (TcBinding LocalMutable _) ->
      tcError $ "Duplicate local `" ++ n ++ "` in the same block."
    Just (TcBinding LocalImmutable _) ->
      tcError $ "Duplicate local `" ++ n ++ "` in the same block."
    _ -> return ()

insertLocal :: Name -> BindingKind -> Type -> TcEnv -> TcEnv
insertLocal n k t env =
  env {envBindings = M.insert n (TcBinding k t) (envBindings env)}

checkAssignable :: LValue -> TcM ()
checkAssignable lv = do
  env <- get
  case rootOf lv of
    LStorage -> return ()
    LVar n ->
      case M.lookup n (envBindings env) of
        Nothing -> tcError $ "Unknown assignment target: `" ++ n ++ "`."
        Just (TcBinding Param _) ->
          tcError $ "Cannot assign to method parameter `" ++ n ++ "` (or through it for field updates)."
        Just (TcBinding LocalImmutable _) ->
          tcError $ "Cannot assign to immutable val `" ++ n ++ "` (or through it for field updates)."
        Just (TcBinding LocalMutable _) -> return ()
    LField {} -> return ()

rootOf :: LValue -> LValue
rootOf LStorage = LStorage
rootOf (LVar n) = LVar n
rootOf (LField p _) = rootOf p

typeOfLValue :: LValue -> TcM Type
typeOfLValue LStorage = gets envStorageType
typeOfLValue (LVar n) = do
  env <- get
  case M.lookup n (envBindings env) of
    Nothing -> tcError $ "Unknown variable `" ++ n ++ "`."
    Just b -> return (bindingType b)
typeOfLValue (LField root fld) = do
  tRoot <- typeOfLValue root
  case tRoot of
    TRecord fields ->
      case lookup fld fields of
        Nothing -> tcError $ "Record has no field `" ++ fld ++ "`."
        Just t -> return t
    _ -> tcError "Field access requires a record value (or typed storage)."

inferExpr :: Expr -> TcM Type
inferExpr (CInt _) = return TInt
inferExpr (CBool _) = return TBool
inferExpr Unit = return TUnit
inferExpr StorageExpr = gets envStorageType
inferExpr (Var n) = do
  env <- get
  case M.lookup n (envBindings env) of
    Nothing -> tcError $ "Unknown variable `" ++ n ++ "`."
    Just b -> return (bindingType b)
inferExpr (FieldAccess e fld) = do
  t <- inferExpr e
  case t of
    TRecord fields ->
      case lookup fld fields of
        Nothing -> tcError $ "Record has no field `" ++ fld ++ "`."
        Just ft -> return ft
    _ -> tcError "Field access requires a record-typed expression."
inferExpr (Not e) = do
  t <- inferExpr e
  lift $ expectType "operand of !" t TBool
  return TBool
inferExpr (And a b) = inferBoolBin a b
inferExpr (Or a b) = inferBoolBin a b
inferExpr (Add a b) = inferIntBin a b
inferExpr (Sub a b) = inferIntBin a b
inferExpr (Mul a b) = inferIntBin a b
inferExpr (Div a b) = inferIntBin a b
inferExpr (Mod a b) = inferIntBin a b
inferExpr (Eq a b) = inferEq a b
inferExpr (Neq a b) = inferEq a b
inferExpr (Lt a b) = inferIntCmp a b
inferExpr (Lte a b) = inferIntCmp a b
inferExpr (Gt a b) = inferIntCmp a b
inferExpr (Gte a b) = inferIntCmp a b
inferExpr (Record pairs) = do
  ts <- mapM (\(k, e) -> (,) k <$> inferExpr e) pairs
  return $ TRecord [(k, t) | (k, t) <- ts]
inferExpr (Call name args) = do
  env <- get
  case M.lookup name (envFunctionSignatures env) of
    Nothing -> tcError $ "Unknown function `" ++ name ++ "`."
    Just sig -> do
      let expected = formalArgs sig
      when (length args /= length expected) $
        tcError $
          "Function `" ++ name ++ "` expects " ++ show (length expected)
            ++ " argument(s) but got " ++ show (length args) ++ "."
      argTypes <- mapM inferExpr args
      zipWithM_
        (\t ex -> lift $ expectType ("argument to `" ++ name ++ "`") t ex)
        argTypes
        expected
      return (returnType sig)

inferBoolBin :: Expr -> Expr -> TcM Type
inferBoolBin a b = do
  ta <- inferExpr a
  tb <- inferExpr b
  lift $ expectType "left operand of boolean operator" ta TBool
  lift $ expectType "right operand of boolean operator" tb TBool
  return TBool

inferIntBin :: Expr -> Expr -> TcM Type
inferIntBin a b = do
  ta <- inferExpr a
  tb <- inferExpr b
  lift $ expectType "left operand of arithmetic operator" ta TInt
  lift $ expectType "right operand of arithmetic operator" tb TInt
  return TInt

inferIntCmp :: Expr -> Expr -> TcM Type
inferIntCmp a b = do
  ta <- inferExpr a
  tb <- inferExpr b
  lift $ expectType "left operand of comparison" ta TInt
  lift $ expectType "right operand of comparison" tb TInt
  return TBool

inferEq :: Expr -> Expr -> TcM Type
inferEq a b = do
  ta <- inferExpr a
  tb <- inferExpr b
  if typesEqual ta tb
    then return TBool
    else
      tcError $
        "Equality requires operands of the same type (got "
          ++ prettyType ta
          ++ " and "
          ++ prettyType tb
          ++ ")."

expectType :: String -> Type -> Type -> Either String ()
expectType ctx got expected =
  if typesEqual got expected
    then Right ()
    else
      Left $
        ctx ++ " has wrong type: expected " ++ prettyType expected ++ ", inferred " ++ prettyType got ++ "."

typesEqual :: Type -> Type -> Bool
typesEqual TInt TInt = True
typesEqual TBool TBool = True
typesEqual TUnit TUnit = True
typesEqual (TRecord as) (TRecord bs) = length as == length bs && and (zipWith fieldEq as bs)
  where
    fieldEq (n1, t1) (n2, t2) = n1 == n2 && typesEqual t1 t2
typesEqual _ _ = False

prettyType :: Type -> String
prettyType TInt = "int"
prettyType TBool = "bool"
prettyType TUnit = "unit"
prettyType (TRecord fs) =
  "{"
    ++ concat
      [ n ++ ": " ++ prettyType t ++ if i < lastI then ", " else ""
      | (i, (n, t)) <- zip [0 :: Int ..] fs
      , let lastI = length fs - 1
      ]
    ++ "}"
