-- | Bidirectional type checking for SmartTS (annotated locals, parameters, returns).
-- Designed to grow: judgments live here; surface 'Type' stays in "AST" until we add variables/schemes.
module SmartTS.TypeCheck
  ( typeCheckContract
  ) where

import Control.Monad (foldM, void)
import Data.List (nub)
import qualified Data.Map.Strict as M
import SmartTS.AST

data BindingKind = Param | LocalMutable | LocalImmutable
  deriving (Eq, Show)

data TcBinding = TcBinding
  { bindingKind :: BindingKind
  , bindingType :: Type
  }
  deriving (Eq, Show)

-- | Environment for checking one method body.
data TcEnv = TcEnv
  { envStorageType :: Type
  , envBindings :: M.Map Name TcBinding
  , envReturnType :: Type
  }
  deriving (Eq, Show)

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
          , envReturnType = methodReturnType m
          }
   in void (checkStmt env0 (methodBody m))

-- | Check a statement; returns updated environment (bindings from @var@/@val@).
checkStmt :: TcEnv -> Stmt -> Either String TcEnv
checkStmt env (SequenceStmt ss) = foldM checkStmt env ss
checkStmt env (ReturnStmt e) = do
  t <- inferExprWithExpected env (Just (envReturnType env)) e
  expectType "return value" t (envReturnType env)
  return env
checkStmt env (VarDeclStmt n typ e) = do
  noDuplicateLocal n env
  t <- inferExprWithExpected env (Just typ) e
  expectType ("initializer of var `" ++ n ++ "`") t typ
  return $ insertLocal n LocalMutable typ env
checkStmt env (ValDeclStmt n typ e) = do
  noDuplicateLocal n env
  t <- inferExprWithExpected env (Just typ) e
  expectType ("initializer of val `" ++ n ++ "`") t typ
  return $ insertLocal n LocalImmutable typ env
checkStmt env (AssignmentStmt lv e) = do
  checkAssignable env lv
  tl <- typeOfLValue env lv
  te <- inferExprWithExpected env (Just tl) e
  expectType "assignment" te tl
  return env
checkStmt env (IfStmt cond thn mel) = do
  tc <- inferExpr env cond
  expectType "if condition" tc TBool
  void (checkStmt env thn)
  case mel of
    Nothing -> return ()
    Just els -> void (checkStmt env els)
  return env
checkStmt env (WhileStmt cond body) = do
  tc <- inferExpr env cond
  expectType "while condition" tc TBool
  void (checkStmt env body)
  return env

noDuplicateLocal :: Name -> TcEnv -> Either String ()
noDuplicateLocal n env =
  case M.lookup n (envBindings env) of
    Just (TcBinding LocalMutable _) ->
      Left $ "Duplicate local `" ++ n ++ "` in the same block."
    Just (TcBinding LocalImmutable _) ->
      Left $ "Duplicate local `" ++ n ++ "` in the same block."
    _ -> Right ()

insertLocal :: Name -> BindingKind -> Type -> TcEnv -> TcEnv
insertLocal n k t env =
  env {envBindings = M.insert n (TcBinding k t) (envBindings env)}

-- | @storage@ is always assignable; locals must be mutable. Parameters and @val@ are not.
checkAssignable :: TcEnv -> LValue -> Either String ()
checkAssignable env lv =
  case rootOf lv of
    LStorage -> Right ()
    LVar n ->
      case M.lookup n (envBindings env) of
        Nothing -> Left $ "Unknown assignment target: `" ++ n ++ "`."
        Just (TcBinding Param _) ->
          Left $ "Cannot assign to method parameter `" ++ n ++ "` (or through it for field updates)."
        Just (TcBinding LocalImmutable _) ->
          Left $ "Cannot assign to immutable val `" ++ n ++ "` (or through it for field updates)."
        Just (TcBinding LocalMutable _) -> Right ()
    LField {} -> Right ()
    LMapAccess {} -> Right ()

rootOf :: LValue -> LValue
rootOf LStorage = LStorage
rootOf (LVar n) = LVar n
rootOf (LField p _) = rootOf p
rootOf (LMapAccess p _) = rootOf p

typeOfLValue :: TcEnv -> LValue -> Either String Type
typeOfLValue env LStorage = pure (envStorageType env)
typeOfLValue env (LVar n) =
  case M.lookup n (envBindings env) of
    Nothing -> Left $ "Unknown variable `" ++ n ++ "`."
    Just b -> Right (bindingType b)
typeOfLValue env (LField root fld) = do
  tRoot <- typeOfLValue env root
  case tRoot of
    TRecord fields ->
      case lookup fld fields of
        Nothing -> Left $ "Record has no field `" ++ fld ++ "`."
        Just t -> Right t
    _ -> Left "Field access requires a record value (or typed storage)."
typeOfLValue env (LMapAccess base key) = do
  tBase <- typeOfLValue env base
  case tBase of
    TMap k v -> do
      ensureComparableKeyType "map assignment" k
      tk <- inferExpr env key
      expectType "map assignment key" tk k
      Right v
    _ -> Left "Map index assignment requires a map-typed left-hand side."

inferExpr :: TcEnv -> Expr -> Either String Type
inferExpr _ (CInt _) = Right TInt
inferExpr _ (CBool _) = Right TBool
inferExpr _ Unit = Right TUnit
inferExpr _ MapEmpty = Left "Cannot infer type of empty_map without a contextual map type."
inferExpr env StorageExpr = pure (envStorageType env)
inferExpr env (Var n) =
  case M.lookup n (envBindings env) of
    Nothing -> Left $ "Unknown variable `" ++ n ++ "`."
    Just b -> Right (bindingType b)
inferExpr env (FieldAccess e fld) = do
  t <- inferExpr env e
  case t of
    TRecord fields ->
      case lookup fld fields of
        Nothing -> Left $ "Record has no field `" ++ fld ++ "`."
        Just ft -> Right ft
    _ -> Left "Field access requires a record-typed expression."
inferExpr env (Not e) = do
  t <- inferExpr env e
  expectType "operand of !" t TBool
  return TBool
inferExpr env (And a b) = inferBoolBin env a b
inferExpr env (Or a b) = inferBoolBin env a b
inferExpr env (Add a b) = inferIntBin env a b
inferExpr env (Sub a b) = inferIntBin env a b
inferExpr env (Mul a b) = inferIntBin env a b
inferExpr env (Div a b) = inferIntBin env a b
inferExpr env (Mod a b) = inferIntBin env a b
inferExpr env (Eq a b) = inferEq env a b
inferExpr env (Neq a b) = inferEq env a b
inferExpr env (Lt a b) = inferIntCmp env a b
inferExpr env (Lte a b) = inferIntCmp env a b
inferExpr env (Gt a b) = inferIntCmp env a b
inferExpr env (Gte a b) = inferIntCmp env a b
inferExpr env (Record pairs) = do
  ts <- mapM (\(k, e) -> (,) k <$> inferExpr env e) pairs
  Right (TRecord [(k, t) | (k, t) <- ts])
inferExpr env (MapAccess mapExpr keyExpr) = do
  tm <- inferExpr env mapExpr
  case tm of
    TMap k v -> do
      ensureComparableKeyType "map access" k
      tk <- inferExpr env keyExpr
      expectType "map access key" tk k
      Right v
    _ -> Left "Map access requires a map-typed expression."
inferExpr env (MapMemCheck mapExpr keyExpr) = do
  tm <- inferExpr env mapExpr
  case tm of
    TMap k _ -> do
      ensureComparableKeyType "mem(map, key)" k
      tk <- inferExpr env keyExpr
      expectType "mem(map, key) key" tk k
      Right TBool
    _ -> Left "mem(map, key) requires the first argument to be a map."
inferExpr env (MapRem mapExpr keyExpr) = do
  tm <- inferExpr env mapExpr
  case tm of
    TMap k v -> do
      ensureComparableKeyType "remove(map, key)" k
      tk <- inferExpr env keyExpr
      expectType "remove(map, key) key" tk k
      Right (TMap k v)
    _ -> Left "remove(map, key) requires the first argument to be a map."

inferExprWithExpected :: TcEnv -> Maybe Type -> Expr -> Either String Type
inferExprWithExpected env expected expr =
  case expr of
    MapEmpty -> inferMapEmpty expected
    _ -> inferExpr env expr

inferMapEmpty :: Maybe Type -> Either String Type
inferMapEmpty Nothing = Left "Cannot infer type of empty_map without a contextual map type."
inferMapEmpty (Just t) =
  case t of
    TMap k v -> do
      ensureComparableKeyType "empty_map" k
      Right (TMap k v)
    _ -> Left "empty_map requires an expected map type (map<K, V>)."

isComparable :: Type -> Bool
isComparable TInt = True
isComparable TBool = True
isComparable _ = False

ensureComparableKeyType :: String -> Type -> Either String ()
ensureComparableKeyType ctx t =
  if isComparable t
    then Right ()
    else Left $ ctx ++ " requires a comparable map key type (int or bool), got " ++ prettyType t ++ "."

inferBoolBin :: TcEnv -> Expr -> Expr -> Either String Type
inferBoolBin env a b = do
  ta <- inferExpr env a
  tb <- inferExpr env b
  expectType "left operand of boolean operator" ta TBool
  expectType "right operand of boolean operator" tb TBool
  return TBool

inferIntBin :: TcEnv -> Expr -> Expr -> Either String Type
inferIntBin env a b = do
  ta <- inferExpr env a
  tb <- inferExpr env b
  expectType "left operand of arithmetic operator" ta TInt
  expectType "right operand of arithmetic operator" tb TInt
  return TInt

inferIntCmp :: TcEnv -> Expr -> Expr -> Either String Type
inferIntCmp env a b = do
  ta <- inferExpr env a
  tb <- inferExpr env b
  expectType "left operand of comparison" ta TInt
  expectType "right operand of comparison" tb TInt
  return TBool

inferEq :: TcEnv -> Expr -> Expr -> Either String Type
inferEq env a b = do
  ta <- inferExpr env a
  tb <- inferExpr env b
  if typesEqual ta tb
    then Right TBool
    else
      Left $
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
typesEqual (TMap k1 v1) (TMap k2 v2) = typesEqual k1 k2 && typesEqual v1 v2
typesEqual (TRecord as) (TRecord bs) = length as == length bs && and (zipWith fieldEq as bs)
  where
    fieldEq (n1, t1) (n2, t2) = n1 == n2 && typesEqual t1 t2
typesEqual _ _ = False

prettyType :: Type -> String
prettyType TInt = "int"
prettyType TBool = "bool"
prettyType TUnit = "unit"
prettyType (TMap k v) = "map<" ++ prettyType k ++ ", " ++ prettyType v ++ ">"
prettyType (TRecord fs) =
  "{"
    ++ concat
      [ n ++ ": " ++ prettyType t ++ if i < lastI then ", " else ""
      | (i, (n, t)) <- zip [0 :: Int ..] fs
      , let lastI = length fs - 1
      ]
    ++ "}"
