-- | Contract origination and entrypoint invocation.
--
-- The CLI runs "SmartTS.TypeCheck.typeCheckContract" on source before interpretation.
-- Persisted storage is decoded with "SmartTS.Interpreter.Codec.jsonToExprByType".
-- After those steps, expression shapes that contradict the static types are treated as
-- internal bugs ("interpretBug") rather than user-facing "Left" errors.
module SmartTS.Interpreter.Contract where

import Control.Monad.State (runStateT)
import Data.Aeson (Value (..))
import qualified Data.Map.Strict as M
import SmartTS.AST
import SmartTS.Interpreter.Codec
import SmartTS.Interpreter.Eval
import SmartTS.Interpreter.Runtime

-- | Build the map of callable private methods for a contract.
buildMethodMap :: Contract -> M.Map Name MethodDecl
buildMethodMap c =
  M.fromList [(methodName m, m) | m <- contractMethods c, methodKind m == Private]

execMethod :: Contract -> MethodDecl -> M.Map Name Expr -> Either String Runtime
execMethod c m params = do
  let initialRt =
        Runtime
          { rtStorage = Nothing
          , rtParams = params
          , rtLocals = M.empty
          , rtMethods = buildMethodMap c
          }
  (_, rt') <- runStateT (execStmt (methodBody m)) initialRt
  return rt'

execMethodWithInitialStorage ::
  Contract ->
  Expr ->
  MethodDecl ->
  M.Map Name Expr ->
  Either String (Maybe Expr, Runtime)
execMethodWithInitialStorage c initialStorage m params =
  let initialRt =
        Runtime
          { rtStorage = Just initialStorage
          , rtParams = params
          , rtLocals = M.empty
          , rtMethods = buildMethodMap c
          }
   in runStateT (execStmt (methodBody m)) initialRt

findEntryPointByName :: Contract -> Name -> Either String MethodDecl
findEntryPointByName c name =
  case filter (\m -> isEntryPointMethod m && methodName m == name) (contractMethods c) of
    [] -> Left $ "No @entrypoint named \"" ++ name ++ "\"."
    [m] -> Right m
    _ -> Left $ "Multiple @entrypoint methods named \"" ++ name ++ "\"."

originateWithJsonArgs ::
  RepositoryState ->
  Contract ->
  String ->
  Value ->
  Either String (Address, RepositoryState)
originateWithJsonArgs repo c sourceText argsJson = do
  m <- case findMethods Originate c of
    [] -> Left "Contract must have exactly one @originate method."
    [mm] -> Right mm
    _ -> Left "Contract must have exactly one @originate method."
  params <- bindArgsByName (methodArgs m) argsJson
  rt <- execMethod c m params
  storageExpr <-
    case rtStorage rt of
      Nothing -> Left "Originate method did not initialize `storage`."
      Just s -> Right s
  let address = generateAddress sourceText (M.size repo)
      repo' =
        M.insert
          address
          (ContractInstance (contractName c) storageExpr)
          repo
  Right (address, repo')

callEntrypointWithJsonArgs ::
  RepositoryState ->
  Contract ->
  Address ->
  Name ->
  String ->
  Value ->
  Either String (Maybe Expr, RepositoryState)
callEntrypointWithJsonArgs repo c addr entryName sourceText argsJson = do
  ci <-
    case M.lookup addr repo of
      Nothing -> Left $ "Unknown address: " ++ addr
      Just x -> Right x
  assertAddressMatchesSource addr sourceText
  if instanceContractName ci /= contractName c
    then
      Left $
        "Contract name mismatch: instance is "
          ++ instanceContractName ci
          ++ " but loaded source is "
          ++ contractName c
          ++ "."
    else do
      m <- findEntryPointByName c entryName
      params <- bindArgsByName (methodArgs m) argsJson
      (ret, rt') <- execMethodWithInitialStorage c (instanceStorage ci) m params
      newStorage <-
        case rtStorage rt' of
          Nothing -> Left "Entrypoint cleared `storage`; not allowed."
          Just s -> Right s
      let ci' = ci {instanceStorage = newStorage}
          repo' = M.insert addr ci' repo
      Right (ret, repo')
