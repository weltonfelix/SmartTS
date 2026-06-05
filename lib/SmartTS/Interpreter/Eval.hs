-- | Expression evaluation and statement execution.
-- Both live in the same module so that the 'Call' expression can invoke 'execStmt'
-- without creating a circular import with "SmartTS.Interpreter.Contract".
module SmartTS.Interpreter.Eval where

import Control.Monad.State
import qualified Data.Map.Strict as M
import SmartTS.AST
import SmartTS.Interpreter.Runtime

-- ---------------------------------------------------------------------------
-- Expression evaluation
-- ---------------------------------------------------------------------------

evalExpr :: Expr -> EvalM Expr
evalExpr (CInt n) = return (CInt n)
evalExpr (CBool b) = return (CBool b)
evalExpr Unit = return Unit
evalExpr StorageExpr = do
  rt <- get
  case rtStorage rt of
    Nothing -> return Unit
    Just s -> return s
evalExpr (Var n) = do
  rt <- get
  case M.lookup n (rtLocals rt) of
    Just b -> return (bindingValue b)
    Nothing ->
      case M.lookup n (rtParams rt) of
        Just v -> return v
        Nothing -> interpretBug ("unknown variable `" ++ n ++ "` after type check")
evalExpr (Record fields) = do
  fs <- mapM (\(k, e) -> (,) k <$> evalExpr e) fields
  return (Record fs)
evalExpr (FieldAccess base fld) = do
  b <- evalExpr base
  case b of
    Record fs ->
      case lookup fld fs of
        Just v -> return v
        Nothing -> interpretBug ("missing record field `" ++ fld ++ "` after type check")
    _ -> interpretBug "field access on non-record after type check"
evalExpr (Not e) = do
  v <- evalExpr e
  case v of
    CBool b -> return (CBool (not b))
    _ -> interpretBug "operand of ! was not bool after type check"
evalExpr (And a b) = boolBin a b (&&)
evalExpr (Or a b) = boolBin a b (||)
evalExpr (Add a b) = intBin a b (+)
evalExpr (Sub a b) = intBin a b (-)
evalExpr (Mul a b) = intBin a b (*)
evalExpr (Div a b) = do
  x <- evalInt a
  y <- evalInt b
  if y == 0 then lift (Left "Division by zero.") else return (CInt (x `div` y))
evalExpr (Mod a b) = do
  x <- evalInt a
  y <- evalInt b
  if y == 0 then lift (Left "Modulo by zero.") else return (CInt (x `mod` y))
evalExpr (Eq a b) = CBool <$> ((==) <$> evalExpr a <*> evalExpr b)
evalExpr (Neq a b) = CBool <$> ((/=) <$> evalExpr a <*> evalExpr b)
evalExpr (Lt a b) = intCmp a b (<)
evalExpr (Lte a b) = intCmp a b (<=)
evalExpr (Gt a b) = intCmp a b (>)
evalExpr (Gte a b) = intCmp a b (>=)
evalExpr (Call name args) = do
  rt <- get
  m <- case M.lookup name (rtMethods rt) of
    Nothing -> interpretBug ("unknown method `" ++ name ++ "` after type check")
    Just m' -> return m'
  argVals <- mapM evalExpr args
  outerRt <- get
  let paramNames = [n | FormalParameter n _ <- methodArgs m]
      params = M.fromList (zip paramNames argVals)
      innerRt = outerRt {rtParams = params, rtLocals = M.empty}
  (mRet, innerRt') <- lift $ runStateT (execStmt (methodBody m)) innerRt
  -- Propagate storage mutations from the called method back to the caller.
  modify $ \r -> r {rtStorage = rtStorage innerRt'}
  case mRet of
    Nothing -> interpretBug ("method `" ++ name ++ "` did not return a value after type check")
    Just v -> return v
evalExpr (MapVal m) = return (MapVal m)
evalExpr MapEmpty = return (MapVal M.empty)
evalExpr (MapAccess base key) = do
  baseVal <- evalExpr base
  keyVal <- evalExpr key
  case baseVal of
    MapVal m ->
        case M.lookup keyVal m of
          Just v -> return v
          Nothing -> lift (Left "Runtime Error: Key not found in map.")
    _ -> interpretBug "map access on non-map after type check"
evalExpr (MapMemCheck base key) = do
  baseVal <- evalExpr base
  keyVal <- evalExpr key
  case baseVal of
    MapVal m -> return (CBool (M.member keyVal m))
    _ -> interpretBug "mem check on non-map after type check"
evalExpr (MapRem base key) = do
  baseVal <- evalExpr base
  keyVal <- evalExpr key
  case baseVal of
    MapVal m -> return (MapVal (M.delete keyVal m))
    _ -> interpretBug "map remove on non-map after type check"

-- ---------------------------------------------------------------------------
-- Statement execution
-- ---------------------------------------------------------------------------

execStmt :: Stmt -> EvalM (Maybe Expr)
execStmt (SequenceStmt ss) = execSequence ss
execStmt (ReturnStmt e) = Just <$> evalExpr e
execStmt (VarDeclStmt n _ e) = do
  v <- evalExpr e
  modify $ \rt -> rt {rtLocals = M.insert n (Binding True v) (rtLocals rt)}
  return Nothing
execStmt (ValDeclStmt n _ e) = do
  v <- evalExpr e
  modify $ \rt -> rt {rtLocals = M.insert n (Binding False v) (rtLocals rt)}
  return Nothing
execStmt (AssignmentStmt lv e) = do
  v <- evalExpr e
  assignLValue lv v
  return Nothing
execStmt (IfStmt cond thenS elseS) = do
  c <- evalExpr cond
  case c of
    CBool True -> execStmt thenS
    CBool False ->
      case elseS of
        Nothing -> return Nothing
        Just es -> execStmt es
    _ -> interpretBug "if condition was not bool after type check"
execStmt (WhileStmt cond body) = loop
  where
    loop = do
      c <- evalExpr cond
      case c of
        CBool False -> return Nothing
        CBool True -> do
          ret <- execStmt body
          case ret of
            Just v -> return (Just v)
            Nothing -> loop
        _ -> interpretBug "while condition was not bool after type check"

execSequence :: [Stmt] -> EvalM (Maybe Expr)
execSequence [] = return Nothing
execSequence (s : ss) = do
  ret <- execStmt s
  case ret of
    Just v -> return (Just v)
    Nothing -> execSequence ss

-- ---------------------------------------------------------------------------
-- LValue assignment helpers
-- ---------------------------------------------------------------------------

assignLValue :: LValue -> Expr -> EvalM ()
assignLValue LStorage v =
  modify $ \rt -> rt {rtStorage = Just v}
assignLValue (LVar n) v = do
  rt <- get
  case M.lookup n (rtLocals rt) of
    Just b ->
      if bindingMutable b
        then modify $ \r -> r {rtLocals = M.insert n (Binding True v) (rtLocals r)}
        else interpretBug ("assignment to immutable val `" ++ n ++ "` after type check")
    Nothing ->
      if M.member n (rtParams rt)
        then interpretBug ("assignment to parameter `" ++ n ++ "` after type check")
        else interpretBug ("unknown assignment target `" ++ n ++ "` after type check")
assignLValue (LField lv fld) v = do
  rt <- get
  let (root, path) = flattenLValue lv [fld]
  rootExpr <- lift $ resolveRootExpr rt root
  updated <- lift $ setFieldPath rootExpr path v
  assignLValue root updated
assignLValue (LMapAccess lv key) v = do
  keyVal <- evalExpr key
  baseVal <- evalExpr (lValueToExpr lv)
  case baseVal of
    MapVal m -> assignLValue lv (MapVal (M.insert keyVal v m))
    _ -> interpretBug "map assignment on non-map after type check"

lValueToExpr :: LValue -> Expr
lValueToExpr LStorage = StorageExpr
lValueToExpr (LVar name) = Var name
lValueToExpr (LField lv name) = FieldAccess (lValueToExpr lv) name
lValueToExpr (LMapAccess lv key) = MapAccess (lValueToExpr lv) key

flattenLValue :: LValue -> [Name] -> (LValue, [Name])
flattenLValue LStorage acc = (LStorage, acc)
flattenLValue (LVar n) acc = (LVar n, acc)
flattenLValue (LField parent fld) acc = flattenLValue parent (fld : acc)
flattenLValue (LMapAccess _ _) _ = error "Map updates must be handled by assignLValue directly, not flattened."

resolveRootExpr :: Runtime -> LValue -> Either String Expr
resolveRootExpr rt LStorage =
  case rtStorage rt of
    Nothing -> Right (Record [])
    Just s -> Right s
resolveRootExpr rt (LVar n) =
  case M.lookup n (rtLocals rt) of
    Just b -> Right (bindingValue b)
    Nothing ->
      case M.lookup n (rtParams rt) of
        Just _ -> interpretBug ("field update through parameter `" ++ n ++ "` after type check")
        Nothing -> interpretBug ("unknown root for field update `" ++ n ++ "` after type check")
resolveRootExpr _ _ = interpretBug "invalid root for field update"

setFieldPath :: Expr -> [Name] -> Expr -> Either String Expr
setFieldPath _ [] _ = interpretBug "empty field path in assignment"
setFieldPath base [f] v = setField base f v
setFieldPath base (f : fs) v = do
  child <- getOrCreateField base f
  child' <- setFieldPath child fs v
  setField base f child'

getOrCreateField :: Expr -> Name -> Either String Expr
getOrCreateField (Record fields) f =
  case lookup f fields of
    Just v -> Right v
    Nothing -> Right (Record [])
getOrCreateField Unit _ = Right (Record [])
getOrCreateField _ _ = interpretBug "field path through non-record value after type check"

setField :: Expr -> Name -> Expr -> Either String Expr
setField (Record fields) f v = Right (Record (insertOrReplace f v fields))
setField Unit f v = Right (Record [(f, v)])
setField _ _ _ = interpretBug "setField on non-record after type check"

insertOrReplace :: Name -> Expr -> [(Name, Expr)] -> [(Name, Expr)]
insertOrReplace k v [] = [(k, v)]
insertOrReplace k v ((k0, v0) : rest)
  | k == k0 = (k, v) : rest
  | otherwise = (k0, v0) : insertOrReplace k v rest

-- ---------------------------------------------------------------------------
-- Internal helpers
-- ---------------------------------------------------------------------------

evalInt :: Expr -> EvalM Int
evalInt e = do
  v <- evalExpr e
  case v of
    CInt n -> return n
    _ -> interpretBug "expected int subexpression after type check"

intBin :: Expr -> Expr -> (Int -> Int -> Int) -> EvalM Expr
intBin a b op = CInt <$> (op <$> evalInt a <*> evalInt b)

boolBin :: Expr -> Expr -> (Bool -> Bool -> Bool) -> EvalM Expr
boolBin a b op = do
  x <- evalExpr a
  y <- evalExpr b
  case (x, y) of
    (CBool bx, CBool by) -> return (CBool (op bx by))
    _ -> interpretBug "boolean operator on non-bool after type check"

intCmp :: Expr -> Expr -> (Int -> Int -> Bool) -> EvalM Expr
intCmp a b op = CBool <$> (op <$> evalInt a <*> evalInt b)
