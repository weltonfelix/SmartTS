{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Test.Tasty
import Test.Tasty.HUnit
import SmartTS.IR.AST
import SmartTS.Parser
import Data.Aeson (Value (..), object, (.=))
import qualified Data.Map.Strict as M
import qualified Data.Vector as V
import SmartTS.Interpreter
  ( ContractInstance (..)
  , contractInstanceFromStorageValue
  , exprToJson
  , jsonToExprByType
  , originateWithJsonArgs
  , callEntrypointWithJsonArgs
  )
import SmartTS.TypeCheck (typeCheckContract)
import qualified SmartTS.IR.LLTZ as L
import SmartTS.CodeGen.CompileLLTZ (translateExpression)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "SmartTS"
    [ codegenTests
      ,testGroup
        "Parser Tests"
        [ contractTests
        , storageTests
        , methodTests
        , expressionTests
        , statementTests
        , errorTests
        ]
    , typeCheckTests
    , codecTests
    , e2eTests
    ]

codegenTests :: TestTree
codegenTests = testGroup "CodeGen: CompileLLTZ"
  [ testCase "MapMemCheck traduz para PrimMem com ordem [key, map]" $
      let typed = MapMemCheck TBool (Var (TMap TInt TBool) "m") (Var TInt "k")
          result = translateExpression typed
      in case L.exprDesc result of
           L.Prim L.PrimMem [L.Expr (L.Variable (L.Var "k")) _, L.Expr (L.Variable (L.Var "m")) _] ->
             return ()
           other -> assertFailure $ "Esperado Prim PrimMem [key, map], obtido: " ++ show other

  , testCase "MapAccess traduz para IfNone com PrimGet e falha com FAILWITH não-vazio" $
    let typed = MapAccess TInt (Var (TMap TInt TInt) "m") (Var TInt "k")
        result = translateExpression typed
    in case L.exprDesc result of
         L.IfNone
           (L.Expr (L.Prim L.PrimGet [keyArg, mapArg]) (L.TOption L.TInt))
           (L.Expr (L.Prim L.PrimFailwith failArgs) _)
           (L.LambdaBinder (L.Var "__value", L.TInt) (L.Expr (L.Variable (L.Var "__value")) L.TInt)) -> do
             -- ordem [key, map] no GET
             case (keyArg, mapArg) of
               (L.Expr (L.Variable (L.Var "k")) _, L.Expr (L.Variable (L.Var "m")) _) -> return ()
               _ -> assertFailure "PrimGet deveria receber [key, map] nessa ordem"
             -- FAILWITH precisa de exatamente um argumento (valor a empurrar antes da instrução)
             case failArgs of
               [L.Expr (L.Const (L.CString _)) L.TString] -> return ()
               _ -> assertFailure $ "FAILWITH deveria receber exatamente um argumento CString, obtido: " ++ show failArgs
         other -> assertFailure $ "Estrutura inesperada para MapAccess: " ++ show other
         
  , testCase "MapAccess preserva o tipo do valor no resultado final" $
      let typed = MapAccess TBool (Var (TMap TInt TBool) "m") (Var TInt "k")
          result = translateExpression typed
      in L.exprType result @?= L.TBool
  ]

-- Helper function to parse and assert success
parseSuccess :: String -> (ParsedContract -> Assertion) -> Assertion
parseSuccess input assertion = case parseContractFromString input of
  Left err      -> assertFailure $ "Parse failed: " ++ show err
  Right contract -> assertion contract

-- Helper function to parse and assert failure
parseFailure :: String -> Assertion
parseFailure input = case parseContractFromString input of
  Left _  -> return ()  -- Expected failure
  Right _ -> assertFailure "Expected parse failure but got success"

typeCheckSuccess :: String -> Assertion
typeCheckSuccess input = case parseContractFromString input of
  Left err -> assertFailure $ "Parse failed: " ++ show err
  Right c ->
    case typeCheckContract c of
      Left err -> assertFailure $ "Type check failed: " ++ err
      Right _  -> return ()

typeCheckFailure :: String -> Assertion
typeCheckFailure input = case parseContractFromString input of
  Left err -> assertFailure $ "Parse failed (need valid parse for type test): " ++ show err
  Right c ->
    case typeCheckContract c of
      Left _  -> return ()
      Right _ -> assertFailure "Expected type error but checking succeeded"

contractTests :: TestTree
contractTests = testGroup "Contract Parsing"
  [ testCase "Simple contract with storage and method" $
      parseSuccess "contract MyContract { storage: { x: int }; @originate init(): int { return 0; } }" $ \contract ->
        case contract of
          Contract "MyContract" [( "x", TInt)] [MethodDecl Originate "init" [] TInt (SequenceStmt [ReturnStmt (CInt _ 0)])] ->
            return ()
          _ -> assertFailure $ "Unexpected contract structure: " ++ show contract

  , testCase "Contract with multiple storage fields" $
      parseSuccess "contract Test { storage: { x: int, y: int }; @entrypoint test(): int { return 1; } }" $ \contract ->
        case contract of
          Contract "Test" storage _ ->
            assertEqual "Storage should have 2 fields" 2 (length storage)
          _ -> assertFailure "Unexpected contract name"

  , testCase "Contract with multiple methods" $
      parseSuccess "contract Test { storage: { x: int }; @originate init(): int { return 0; } @entrypoint inc(): int { return 1; } }" $ \contract ->
        case contract of
          Contract _ _ methods ->
            assertEqual "Should have 2 methods" 2 (length methods)
  ]

storageTests :: TestTree
storageTests = testGroup "Storage Parsing"
  [ testCase "Single storage field" $
      parseSuccess "contract Test { storage: { x: int }; @originate init(): int { return 0; } }" $ \contract ->
        case contract of
          Contract _ [(name, typ)] _ -> do
            assertEqual "Storage field name" "x" name
            assertEqual "Storage field type" TInt typ
          _ -> assertFailure "Unexpected storage structure"

  , testCase "Multiple storage fields" $
      parseSuccess "contract Test { storage: { x: int, y: int, z: int }; @originate init(): int { return 0; } }" $ \contract ->
        case contract of
          Contract _ storage _ ->
            assertEqual "Should have 3 storage fields" 3 (length storage)

  , testCase "Storage with single field (no comma)" $
      parseSuccess "contract Test { storage: { x: int }; @originate init(): int { return 0; } }" $ \contract ->
        case contract of
          Contract _ storage _ ->
            assertEqual "Should have 1 storage field" 1 (length storage)
  ]

methodTests :: TestTree
methodTests = testGroup "Method Parsing"
  [ testCase "Method with @originate decorator" $
      parseSuccess "contract Test { storage: { x: int }; @originate init(): int { return 0; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl Originate "init" [] TInt _] ->
            return ()
          _ -> assertFailure "Expected @originate method"

  , testCase "Method with @entrypoint decorator" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { return 0; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl EntryPoint "test" [] TInt _] ->
            return ()
          _ -> assertFailure "Expected @entrypoint method"

  , testCase "Method with @private decorator" $
      parseSuccess "contract Test { storage: { x: int }; @private helper(): int { return 0; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl Private "helper" [] TInt _] ->
            return ()
          _ -> assertFailure "Expected @private method"

  , testCase "Method with parameters" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint add(a: int, b: int): int { return a + b; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl EntryPoint "add" params TInt _] -> do
            assertEqual "Should have 2 parameters" 2 (length params)
            case params of
              [FormalParameter "a" TInt, FormalParameter "b" TInt] ->
                return ()
              _ -> assertFailure "Unexpected parameter structure"
          _ -> assertFailure "Unexpected method structure"

  , testCase "Method with single parameter" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint inc(x: int): int { return x + 1; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ params _ _] ->
            assertEqual "Should have 1 parameter" 1 (length params)
          _ -> assertFailure "Unexpected method structure"

  , testCase "Method with empty parameter list" $
      parseSuccess "contract Test { storage: { x: int }; @originate init(): int { return 0; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ params _ _] ->
            assertEqual "Should have 0 parameters" 0 (length params)
          _ -> assertFailure "Unexpected method structure"
  ]

expressionTests :: TestTree
expressionTests = testGroup "Expression Parsing"
  [ testCase "Integer literal" $
      parseSuccess "contract Test { storage: { x: int }; @originate init(): int { return 42; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (CInt _ 42)])] ->
            return ()
          _ -> assertFailure $ "Expected integer literal 42, got: " ++ show contract

  , testCase "Variable reference" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { return x; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (Var _ "x")])] ->
            return ()
          _ -> assertFailure $ "Expected variable reference, got: " ++ show contract

  , testCase "Addition expression" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { return 1 + 2; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (Add _ (CInt _ 1) (CInt _ 2))])] ->
            return ()
          _ -> assertFailure $ "Expected addition expression, got: " ++ show contract

  , testCase "Subtraction expression" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { return 5 - 3; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (Sub _ (CInt _ 5) (CInt _ 3))])] ->
            return ()
          _ -> assertFailure $ "Expected subtraction expression, got: " ++ show contract

  , testCase "Chained addition" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { return 1 + 2 + 3; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt expr])] -> do
            -- Should parse as (1 + 2) + 3 due to left associativity
            case expr of
              Add _ (Add _ (CInt _ 1) (CInt _ 2)) (CInt _ 3) ->
                return ()
              _ -> assertFailure $ "Expected left-associative addition, got: " ++ show expr
          _ -> assertFailure $ "Unexpected expression structure: " ++ show contract

  , testCase "Mixed addition and subtraction" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { return 10 - 2 + 3; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt expr])] -> do
            -- Should parse as (10 - 2) + 3 due to left associativity
            case expr of
              Add _ (Sub _ (CInt _ 10) (CInt _ 2)) (CInt _ 3) ->
                return ()
              _ -> assertFailure $ "Expected left-associative mixed operations, got: " ++ show expr
          _ -> assertFailure $ "Unexpected expression structure: " ++ show contract

  , testCase "Parenthesized expression" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { return (1 + 2); } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (Add _ (CInt _ 1) (CInt _ 2))])] ->
            return ()
          _ -> assertFailure $ "Expected parenthesized addition, got: " ++ show contract

  , testCase "Unit expression" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { return (); } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (Unit _)])] ->
            return ()
          _ -> assertFailure $ "Expected unit expression, got: " ++ show contract

  , testCase "Boolean expression (&&) and boolean type" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint check(): bool { return true && false; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ "check" [] TBool (SequenceStmt [ReturnStmt (And _ (CBool _ True) (CBool _ False))])] ->
            return ()
          _ -> assertFailure $ "Expected boolean && expression, got: " ++ show contract

  , testCase "Not expression" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint notit(): bool { return !false; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ "notit" [] TBool (SequenceStmt [ReturnStmt (Not _ (CBool _ False))])] ->
            return ()
          _ -> assertFailure $ "Expected !false, got: " ++ show contract

  , testCase "Relational expression (==)" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint eq(): bool { return 1 == 2; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ "eq" [] TBool (SequenceStmt [ReturnStmt (Eq _ (CInt _ 1) (CInt _ 2))])] ->
            return ()
          _ -> assertFailure $ "Expected 1 == 2, got: " ++ show contract

  , testCase "Mul/Div/Mod expressions" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint arith(): int { return 6 * 7; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ "arith" [] TInt (SequenceStmt [ReturnStmt (Mul _ (CInt _ 6) (CInt _ 7))])] ->
            return ()
          _ -> assertFailure $ "Expected 6 * 7, got: " ++ show contract

  , testCase "Record type and record literal" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint get(): { a: int, b: bool } { return { a: 1, b: true }; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ "get" [] (TRecord [("a", TInt), ("b", TBool)]) (SequenceStmt [ReturnStmt (Record _ [("a", CInt _ 1), ("b", CBool _ True)])])] ->
            return ()
          _ -> assertFailure $ "Expected record type/literal, got: " ++ show contract

  , testCase "Record field access (x.f)" $
      parseSuccess "contract Test { storage: { x: { a: int, b: bool } }; @entrypoint proj(): int { return x.a; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "proj" [] TInt
                (SequenceStmt [ReturnStmt (FieldAccess _ (Var _ "x") "a")])
            ] ->
              return ()
          _ -> assertFailure $ "Expected projection x.a, got: " ++ show contract

  , testCase "Chained field access (x.a.b)" $
      parseSuccess "contract Test { storage: { x: { a: { b: int } } }; @entrypoint proj2(): int { return x.a.b; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "proj2" [] TInt
                (SequenceStmt
                  [ReturnStmt (FieldAccess _ (FieldAccess _ (Var _ "x") "a") "b")])]
            -> return ()
          _ -> assertFailure $ "Expected chained projection x.a.b, got: " ++ show contract

  , testCase "Chained field access on record literal (..a.b)" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint litproj2(): int { return { a: { b: 1 } }.a.b; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "litproj2" [] TInt
                (SequenceStmt
                  [ReturnStmt
                    (FieldAccess _
                      (FieldAccess _
                        (Record _ [("a", Record _ [("b", CInt _ 1)])])
                        "a")
                      "b")])]
            -> return ()
          _ -> assertFailure $ "Expected chained projection on record literal, got: " ++ show contract

  , testCase "Field access on record literal" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint litproj(): int { return { a: 1, b: true }.a; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "litproj" [] TInt
                (SequenceStmt [ReturnStmt (FieldAccess _ (Record _ [("a", CInt _ 1), ("b", CBool _ True)]) "a")])
            ] ->
              return ()
          _ -> assertFailure $ "Expected projection on record literal, got: " ++ show contract

  , testCase "Map type in return type (map<int, bool>)" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint get(): map<int, bool> { return empty_map; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ "get" [] (TMap TInt TBool) (SequenceStmt [ReturnStmt (MapEmpty _)])] ->
            return ()
          _ -> assertFailure $ "Expected map<int, bool> return type with empty_map, got: " ++ show contract

  , testCase "empty_map expression" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint get(): map<int, int> { return empty_map; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ "get" [] (TMap TInt TInt) (SequenceStmt [ReturnStmt (MapEmpty _)])] ->
            return ()
          _ -> assertFailure $ "Expected empty_map, got: " ++ show contract

  , testCase "Map index read (m[k])" $
      parseSuccess "contract Test { storage: { m: map<int, bool> }; @entrypoint get(k: int): bool { return m[k]; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "get" [FormalParameter "k" TInt] TBool
                (SequenceStmt [ReturnStmt (MapAccess _ (Var _ "m") (Var _ "k"))])
            ] ->
              return ()
          _ -> assertFailure $ "Expected m[k] map access, got: " ++ show contract

  , testCase "Map index read with literal key (m[0])" $
      parseSuccess "contract Test { storage: { m: map<int, bool> }; @entrypoint get(): bool { return m[0]; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "get" [] TBool
                (SequenceStmt [ReturnStmt (MapAccess _ (Var _ "m") (CInt _ 0))])
            ] ->
              return ()
          _ -> assertFailure $ "Expected m[0] map access, got: " ++ show contract

  , testCase "Nested storage map index read (storage.m[k])" $
      parseSuccess "contract Test { storage: { m: map<int, bool> }; @entrypoint get(k: int): bool { return storage.m[k]; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "get" [FormalParameter "k" TInt] TBool
                (SequenceStmt
                  [ReturnStmt (MapAccess _ (FieldAccess _ (StorageExpr _) "m") (Var _ "k"))])
            ] ->
              return ()
          _ -> assertFailure $ "Expected storage.m[k] map access, got: " ++ show contract

  , testCase "mem(map, key) expression" $
      parseSuccess "contract Test { storage: { m: map<int, bool> }; @entrypoint has(k: int): bool { return mem(storage.m, k); } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "has" [FormalParameter "k" TInt] TBool
                (SequenceStmt
                  [ReturnStmt (MapMemCheck _ (FieldAccess _ (StorageExpr _) "m") (Var _ "k"))])
            ] ->
              return ()
          _ -> assertFailure $ "Expected mem(storage.m, k), got: " ++ show contract

  , testCase "remove(map, key) expression" $
      parseSuccess "contract Test { storage: { m: map<int, bool> }; @entrypoint drop(k: int): map<int, bool> { return remove(storage.m, k); } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "drop" [FormalParameter "k" TInt] (TMap TInt TBool)
                (SequenceStmt
                  [ReturnStmt (MapRem _ (FieldAccess _ (StorageExpr _) "m") (Var _ "k"))])
            ] ->
              return ()
          _ -> assertFailure $ "Expected remove(storage.m, k), got: " ++ show contract
  ]

statementTests :: TestTree
statementTests = testGroup "Statement Parsing"
  [ testCase "Return statement" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { return 42; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (CInt _ 42)])] ->
            return ()
          _ -> assertFailure $ "Expected return statement, got: " ++ show contract

  , testCase "Assignment statement" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { x = 10; return x; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [AssignmentStmt (LVar "x") (CInt _ 10), ReturnStmt (Var _ "x")])] ->
            return ()
          _ -> assertFailure "Expected assignment and return statements"

  , testCase "Multiple statements in block" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { x = 1; x = 2; return x; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt stmts)] ->
            assertEqual "Should have 3 statements" 3 (length stmts)
          _ -> assertFailure "Unexpected statement structure"

  , testCase "Assignment with expression" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { x = 1 + 2; return x; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [AssignmentStmt (LVar "x") (Add _ (CInt _ 1) (CInt _ 2)), ReturnStmt (Var _ "x")])] ->
            return ()
          _ -> assertFailure "Expected assignment with expression"

  , testCase "If statement with else" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint f(): int { if (true) { return 1; } else { return 2; } } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ "f" [] TInt (SequenceStmt [IfStmt (CBool _ True) (SequenceStmt [ReturnStmt (CInt _ 1)]) (Just (SequenceStmt [ReturnStmt (CInt _ 2)]))])] ->
            return ()
          _ -> assertFailure $ "Expected if/else, got: " ++ show contract

  , testCase "While statement" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint loop(): int { while (false) { x = 1; } return x; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ "loop" [] TInt (SequenceStmt [WhileStmt (CBool _ False) (SequenceStmt [AssignmentStmt (LVar "x") (CInt _ 1)]) , ReturnStmt (Var _ "x")])] ->
            return ()
          _ -> assertFailure $ "Expected while statement, got: " ++ show contract

  , testCase "Field assignment statement (x.a = ...)" $
      parseSuccess "contract Test { storage: { x: { a: int } }; @entrypoint fa(): int { x.a = 3; return x.a; } }" $ \contract ->
        case contract of
          Contract _ _
            [MethodDecl _ "fa" [] TInt
              (SequenceStmt
                [ AssignmentStmt (LField (LVar "x") "a") (CInt _ 3)
                , ReturnStmt (FieldAccess _ (Var _ "x") "a")
                ])] ->
              return ()
          _ -> assertFailure $ "Expected x.a assignment, got: " ++ show contract

  , testCase "Field assignment statement (x.a.b = ...)" $
      parseSuccess "contract Test { storage: { x: { a: { b: int } } }; @entrypoint fab(): int { x.a.b = 3; return x.a.b; } }" $ \contract ->
        case contract of
          Contract _ _
            [MethodDecl _ "fab" [] TInt
              (SequenceStmt
                [ AssignmentStmt
                    (LField (LField (LVar "x") "a") "b")
                    (CInt _ 3)
                , ReturnStmt
                    (FieldAccess _ (FieldAccess _ (Var _ "x") "a") "b")
                ])] ->
              return ()
          _ -> assertFailure $ "Expected x.a.b assignment, got: " ++ show contract

  , testCase "Storage expression read (storage.x)" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint sr(): int { return storage.x; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "sr" [] TInt
                (SequenceStmt
                  [ReturnStmt (FieldAccess _ (StorageExpr _) "x")])
            ] ->
              return ()
          _ -> assertFailure $ "Expected storage read, got: " ++ show contract

  , testCase "Storage expression write (storage.x = ...)" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint sw(): int { storage.x = 10; return storage.x; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "sw" [] TInt
                (SequenceStmt
                  [ AssignmentStmt (LField LStorage "x") (CInt _ 10)
                  , ReturnStmt (FieldAccess _ (StorageExpr _) "x")
                  ])
            ] ->
              return ()
          _ -> assertFailure $ "Expected storage write, got: " ++ show contract

  , testCase "Var declaration + assignment to local var" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint v(): int { var y: int = 10; y = 11; return y; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "v" [] TInt
                (SequenceStmt
                  [ VarDeclStmt "y" TInt (CInt _ 10)
                  , AssignmentStmt (LVar "y") (CInt _ 11)
                  , ReturnStmt (Var _ "y")
                  ])
            ] ->
              return ()
          _ -> assertFailure $ "Expected var decl + assignment, got: " ++ show contract

  , testCase "Val declaration + returning local val" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint c(): int { val y: int = 10; return y; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "c" [] TInt
                (SequenceStmt
                  [ ValDeclStmt "y" TInt (CInt _ 10)
                  , ReturnStmt (Var _ "y")
                  ])
            ] ->
              return ()
          _ -> assertFailure $ "Expected val decl, got: " ++ show contract

  , testCase "Field assignment to local record (x.a = ... but local var)" $
      parseSuccess "contract Test { storage: { x: { a: int } }; @entrypoint fa2(): int { var t: { a: int } = x; t.a = 7; return t.a; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "fa2" [] TInt
                (SequenceStmt
                  [ VarDeclStmt "t" (TRecord [("a", TInt)]) (Var _ "x")
                  , AssignmentStmt (LField (LVar "t") "a") (CInt _ 7)
                  , ReturnStmt (FieldAccess _ (Var _ "t") "a")
                  ])
            ] ->
              return ()
          _ -> assertFailure $ "Expected local record field assignment, got: " ++ show contract

  , testCase "var declaration with empty_map initializer" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint f(): unit { var m: map<int, int> = empty_map; return (); } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "f" [] TUnit
                (SequenceStmt
                  [ VarDeclStmt "m" (TMap TInt TInt) (MapEmpty _)
                  , ReturnStmt (Unit _)
                  ])
            ] ->
              return ()
          _ -> assertFailure $ "Expected var m: map<int,int> = empty_map, got: " ++ show contract

  , testCase "Map index assignment (m[k] = v)" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint f(): unit { var m: map<int, bool> = empty_map; m[1] = true; return (); } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "f" [] TUnit
                (SequenceStmt
                  [ VarDeclStmt "m" (TMap TInt TBool) (MapEmpty _)
                  , AssignmentStmt (LMapAccess (LVar "m") (CInt _ 1)) (CBool _ True)
                  , ReturnStmt (Unit _)
                  ])
            ] ->
              return ()
          _ -> assertFailure $ "Expected m[1] = true assignment, got: " ++ show contract

  , testCase "Storage map index assignment (storage.m[k] = v)" $
      parseSuccess "contract Test { storage: { m: map<int, bool> }; @entrypoint f(k: int): unit { storage.m[k] = true; return (); } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "f" [FormalParameter "k" TInt] TUnit
                (SequenceStmt
                  [ AssignmentStmt (LMapAccess (LField LStorage "m") (Var _ "k")) (CBool _ True)
                  , ReturnStmt (Unit _)
                  ])
            ] ->
              return ()
          _ -> assertFailure $ "Expected storage.m[k] = true assignment, got: " ++ show contract
  ]

typeCheckTests :: TestTree
typeCheckTests =
  testGroup
    "Type checker"
    [ 
      testCase "Minimal well-typed contract" $
        typeCheckSuccess
          "contract C { storage: { x: int }; @originate init(): int { return 0; } }"
    , testCase "Return type mismatch" $
        typeCheckFailure
          "contract C { storage: { x: int }; @originate init(): int { return true; } }"
    , testCase "Arithmetic requires int" $
        typeCheckFailure
          "contract C { storage: { x: int }; @originate init(): int { return 1 + true; } }"
    , testCase "Cannot assign to val" $
        typeCheckFailure
          "contract C { storage: { x: int }; @originate init(): int { val v: int = 1; v = 2; return 0; } }"
    , testCase "Equality requires same types" $
        typeCheckFailure
          "contract C { storage: { x: int }; @originate init(): bool { return 1 == true; } }"
    , testCase "If condition must be bool" $
        typeCheckFailure
          "contract C { storage: { x: int }; @originate init(): int { if (1) { return 0; } else { return 1; } } }"
    , testCase "Storage field assignment matches storage type" $
        typeCheckSuccess
          "contract C { storage: { n: int }; @originate init(): unit { storage.n = 3; return (); } }"
    , testCase "Unknown storage field" $
        typeCheckFailure
          "contract C { storage: { n: int }; @originate init(): unit { storage.missing = 1; return (); } }"
    , testCase "Persisted storage decodes against contract storage type" $
        parseSuccess
          "contract C { storage: { n: int, b: bool }; @originate init(): unit { return (); } }"
          $ \c ->
            case contractInstanceFromStorageValue c (object ["n" .= (1 :: Int), "b" .= True]) of
              Left err -> assertFailure err
              Right (ContractInstance _ st) -> case st of
                Record _ [("n", CInt _ 1), ("b", CBool _ True)] -> return ()
                _ -> assertFailure $ "unexpected storage expr: " ++ show st

    -- map<K, V> - casos válidos

    , testCase "map<int, bool> é um tipo de storage válido" $
        typeCheckSuccess
          "contract C { storage: { m: map<int, bool> }; @originate init(): unit { return (); } }"

    , testCase "map<bool, int> é um tipo de storage válido" $
        typeCheckSuccess
          "contract C { storage: { m: map<bool, int> }; @originate init(): unit { return (); } }"

    , testCase "empty_map com contexto map<int, int> é aceito" $
        typeCheckSuccess
          "contract C { storage: { m: map<int, int> }; @originate init(): unit { storage.m = empty_map; return (); } }"

    , testCase "leitura de map via storage.m[k] retorna tipo do valor" $
        typeCheckSuccess
          "contract C { storage: { m: map<int, int> }; @entrypoint get(k: int): int { return storage.m[k]; } }"

    , testCase "escrita em storage.m[k] com tipos corretos" $
        typeCheckSuccess
          "contract C { storage: { m: map<int, bool> }; @originate init(): unit { storage.m[0] = true; return (); } }"

    , testCase "escrita em var local de mapa com tipos corretos" $
        typeCheckSuccess
          "contract C { storage: { x: int }; @entrypoint f(): unit { var m: map<int, int> = empty_map; m[1] = 42; return (); } }"

    , testCase "mem(map, key) retorna bool" $
        typeCheckSuccess
          "contract C { storage: { m: map<int, bool> }; @entrypoint f(k: int): bool { return mem(storage.m, k); } }"

    , testCase "remove(map, key) retorna map<K, V>" $
        typeCheckSuccess
          "contract C { storage: { m: map<int, bool> }; @entrypoint f(k: int): map<int, bool> { return remove(storage.m, k); } }"

    , testCase "map<int, map<int, bool>> - mapa de mapas (valor pode ser mapa)" $
        typeCheckSuccess
          "contract C { storage: { m: map<int, map<int, bool>> }; @originate init(): unit { return (); } }"
    
    -- map<K, V> - chave inválida (não comparável)
    
    , testCase "map<unit, int> - unit não é comparável como chave" $
        typeCheckFailure
          "contract C { storage: { m: map<unit, int> }; @originate init(): unit { storage.m[()] = 1; return (); } }"

    , testCase "map<map<int,int>, bool> - mapa como chave é rejeitado" $
        typeCheckFailure
          "contract C { storage: { m: map<int, int> }; @originate init(): unit { var k: map<int, int> = empty_map; storage.m[k] = 1; return (); } }"

    , testCase "empty_map com chave record é rejeitado" $
        typeCheckFailure
          "contract C { storage: { m: map<{ x: int }, bool> }; @originate init(): unit { storage.m = empty_map; return (); } }"

    , testCase "acesso storage.m[k] com tipo de chave errado é rejeitado" $
        typeCheckFailure
          "contract C { storage: { m: map<int, bool> }; @entrypoint f(k: bool): bool { return storage.m[k]; } }"

    , testCase "escrita storage.m[k] com tipo de valor errado é rejeitado" $
        typeCheckFailure
          "contract C { storage: { m: map<int, bool> }; @originate init(): unit { storage.m[0] = 42; return (); } }"

    , testCase "mem(map, key) com chave de tipo errado é rejeitado" $
        typeCheckFailure
          "contract C { storage: { m: map<int, bool> }; @entrypoint f(): bool { return mem(storage.m, true); } }"

    , testCase "remove(map, key) com chave de tipo errado é rejeitado" $
        typeCheckFailure
          "contract C { storage: { m: map<int, bool> }; @entrypoint f(): map<int, bool> { return remove(storage.m, true); } }"

    , testCase "empty_map sem contexto de tipo é rejeitado" $
        typeCheckFailure
          "contract C { storage: { x: int }; @originate init(): unit { var m: int = empty_map; return (); } }"

    , testCase "acesso de campo em não-mapa via [] é rejeitado" $
        typeCheckFailure
          "contract C { storage: { x: int }; @entrypoint f(): int { return storage.x[0]; } }"
    ]
  

errorTests :: TestTree
errorTests = testGroup "Error Cases"
  [ testCase "Missing contract keyword" $
      parseFailure "MyContract { storage: { x: int }; @originate init(): int { return 0; } }"

  , testCase "Missing storage declaration" $
      parseFailure "contract Test { @originate init(): int { return 0; } }"

  , testCase "Invalid storage syntax" $
      parseFailure "contract Test { storage x: int; @originate init(): int { return 0; } }"

  , testCase "Missing method decorator (defaults to Private)" $
      parseSuccess "contract Test { storage: { x: int }; init(): int { return 0; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl Private "init" [] TInt _] ->
            return ()
          _ -> assertFailure "Expected method without decorator to default to Private"

  , testCase "Missing return type" $
      parseFailure "contract Test { storage: { x: int }; @entrypoint test() { return 0; } }"

  , testCase "Missing semicolon after statement" $
      parseFailure "contract Test { storage: { x: int }; @entrypoint test(): int { return 0 } }"

  , testCase "Invalid expression syntax" $
      parseFailure "contract Test { storage: { x: int }; @entrypoint test(): int { return +; } }"
  ]

codecTests :: TestTree
codecTests =
  testGroup
    "Codec: map<K, V> JSON"
    [ testCase "exprToJson encodes empty map as empty array" $
        exprToJson (MapVal (TMap TInt TBool) M.empty) @?= Array V.empty

    , testCase "exprToJson encodes map<int, bool> as array of {key, value}" $
        let m = MapVal (TMap TInt TBool) (M.fromList [(CInt TInt 1, CBool TBool True)])
         in exprToJson m @?= Array (V.singleton (object ["key" .= (1 :: Int), "value" .= True]))

    , testCase "exprToJson encodes map<bool, int> as array of {key, value}" $
        let m = MapVal (TMap TBool TInt) (M.fromList [(CBool TBool False, CInt TInt 9)])
         in exprToJson m @?= Array (V.singleton (object ["key" .= False, "value" .= (9 :: Int)]))

    , testCase "jsonToExprByType decodes [] into an empty map<int, bool>" $
        case jsonToExprByType (TMap TInt TBool) (Array V.empty) of
          Left err -> assertFailure err
          Right (MapVal _ m) -> assertEqual "empty map" M.empty m
          Right other -> assertFailure $ "Expected MapVal, got: " ++ show other

    , testCase "jsonToExprByType decodes [{key,value}, ...] into map<int, bool>" $
        let json = Array $ V.fromList
              [ object ["key" .= (1 :: Int), "value" .= True]
              , object ["key" .= (2 :: Int), "value" .= False]
              ]
         in case jsonToExprByType (TMap TInt TBool) json of
              Left err -> assertFailure err
              Right (MapVal _ m) ->
                assertEqual
                  "decoded entries"
                  (M.fromList [(CInt TInt 1, CBool TBool True), (CInt TInt 2, CBool TBool False)])
                  m
              Right other -> assertFailure $ "Expected MapVal, got: " ++ show other

    , testCase "jsonToExprByType rejects a map entry missing \"value\"" $
        let json = Array (V.singleton (object ["key" .= (1 :: Int)]))
         in case jsonToExprByType (TMap TInt TBool) json of
              Left _  -> return ()
              Right _ -> assertFailure "Expected decoding failure for missing \"value\" field"

    , testCase "jsonToExprByType rejects a non-array for a map type" $
        case jsonToExprByType (TMap TInt TBool) (object ["1" .= True]) of
          Left _  -> return ()
          Right _ -> assertFailure "Expected decoding failure: a map must be a JSON array"

    , testCase "Round-trip: map<int, bool> survives exprToJson . jsonToExprByType" $
        let original = M.fromList [(CInt TInt 1, CBool TBool True), (CInt TInt 2, CBool TBool False)]
            json = exprToJson (MapVal (TMap TInt TBool) original)
         in case jsonToExprByType (TMap TInt TBool) json of
              Left err -> assertFailure err
              Right (MapVal _ m) -> assertEqual "round-tripped map" original m
              Right other -> assertFailure $ "Expected MapVal, got: " ++ show other

    , testCase "Storage with map field decodes via contractInstanceFromStorageValue" $
        parseSuccess
          "contract C { storage: { admin_id: int, members: map<int, bool> }; @originate init(): unit { return (); } }"
          $ \c ->
            let storageJson =
                  object
                    [ "admin_id" .= (7 :: Int)
                    , "members" .=
                        Array (V.singleton (object ["key" .= (1 :: Int), "value" .= True]))
                    ]
             in case contractInstanceFromStorageValue c storageJson of
                  Left err -> assertFailure err
                  Right (ContractInstance _ st) -> case st of
                    Record _ [("admin_id", CInt _ 7), ("members", MapVal _ m)] ->
                      assertEqual
                        "members map"
                        (M.fromList [(CInt TInt 1, CBool TBool True)])
                        m
                    _ -> assertFailure $ "unexpected storage expr: " ++ show st
    ]

membershipSource :: String
membershipSource =
  "contract Membership {\n\
  \  storage: {\n\
  \    admin_id: int,\n\
  \    members: map<int, bool>\n\
  \  };\n\
  \\n\
  \  @originate\n\
  \  init(admin: int): unit {\n\
  \    storage.admin_id = admin;\n\
  \    storage.members = empty_map;\n\
  \    return ();\n\
  \  }\n\
  \\n\
  \  @entrypoint\n\
  \  addMember(new_user: int): unit {\n\
  \    storage.members[new_user] = true;\n\
  \    return ();\n\
  \  }\n\
  \\n\
  \  @entrypoint\n\
  \  removeMember(user: int): bool {\n\
  \    if (mem(storage.members, user)) {\n\
  \      storage.members = remove(storage.members, user);\n\
  \      return true;\n\
  \    }\n\
  \    return false;\n\
  \  }\n\
  \}"

membershipTypedContract :: TypedContract
membershipTypedContract =
  case parseContractFromString membershipSource of
    Left err -> error ("Membership.smartts failed to parse: " ++ show err)
    Right c -> case typeCheckContract c of
      Left err -> error ("Membership.smartts failed to type-check: " ++ err)
      Right tc -> tc

e2eTests :: TestTree
e2eTests =
  testGroup
    "End-to-end: Membership.smartts"
    [ testCase "originate initializes storage with admin_id and an empty members map" $
        case originateWithJsonArgs M.empty membershipTypedContract membershipSource (object ["admin" .= (1 :: Int)]) of
          Left err -> assertFailure err
          Right (_, repo) -> case M.toList repo of
            [(_, ContractInstance "Membership" (Record _ [("admin_id", CInt _ 1), ("members", MapVal _ m)]))] ->
              assertEqual "members starts empty" M.empty m
            other -> assertFailure $ "Unexpected repository contents: " ++ show other

    , testCase "addMember inserts the new user into storage.members" $ do
        (addr, repo0) <-
          case originateWithJsonArgs M.empty membershipTypedContract membershipSource (object ["admin" .= (1 :: Int)]) of
            Left err -> assertFailure err >> error "unreachable"
            Right ok -> return ok
        case callEntrypointWithJsonArgs repo0 membershipTypedContract addr "addMember" membershipSource (object ["new_user" .= (42 :: Int)]) of
          Left err -> assertFailure err
          Right (_, repo1) -> case M.lookup addr repo1 of
            Just (ContractInstance _ (Record _ [("admin_id", _), ("members", MapVal _ m)])) ->
              assertEqual "members has the new user" (M.fromList [(CInt TInt 42, CBool TBool True)]) m
            other -> assertFailure $ "Unexpected instance: " ++ show other

    , testCase "removeMember(user) returns true and removes a present member" $ do
        (addr, repo0) <-
          case originateWithJsonArgs M.empty membershipTypedContract membershipSource (object ["admin" .= (1 :: Int)]) of
            Left err -> assertFailure err >> error "unreachable"
            Right ok -> return ok
        repo1 <-
          case callEntrypointWithJsonArgs repo0 membershipTypedContract addr "addMember" membershipSource (object ["new_user" .= (42 :: Int)]) of
            Left err -> assertFailure err >> error "unreachable"
            Right (_, r) -> return r
        case callEntrypointWithJsonArgs repo1 membershipTypedContract addr "removeMember" membershipSource (object ["user" .= (42 :: Int)]) of
          Left err -> assertFailure err
          Right (ret, repo2) -> do
            assertEqual "removeMember returns true" (Just (CBool TBool True)) ret
            case M.lookup addr repo2 of
              Just (ContractInstance _ (Record _ [("admin_id", _), ("members", MapVal _ m)])) ->
                assertEqual "members is empty after removal" M.empty m
              other -> assertFailure $ "Unexpected instance: " ++ show other

    , testCase "removeMember(user) returns false for an absent member" $ do
        (addr, repo0) <-
          case originateWithJsonArgs M.empty membershipTypedContract membershipSource (object ["admin" .= (1 :: Int)]) of
            Left err -> assertFailure err >> error "unreachable"
            Right ok -> return ok
        case callEntrypointWithJsonArgs repo0 membershipTypedContract addr "removeMember" membershipSource (object ["user" .= (99 :: Int)]) of
          Left err -> assertFailure err
          Right (ret, _) -> assertEqual "removeMember returns false" (Just (CBool TBool False)) ret

    , testCase "Full round-trip: originate, persist storage to JSON, reload, call entrypoint" $ do
        (addr, repo0) <-
          case originateWithJsonArgs M.empty membershipTypedContract membershipSource (object ["admin" .= (1 :: Int)]) of
            Left err -> assertFailure err >> error "unreachable"
            Right ok -> return ok
        repo1 <-
          case callEntrypointWithJsonArgs repo0 membershipTypedContract addr "addMember" membershipSource (object ["new_user" .= (7 :: Int)]) of
            Left err -> assertFailure err >> error "unreachable"
            Right (_, r) -> return r
        ci0 <- case M.lookup addr repo1 of
          Nothing -> assertFailure "Missing contract instance after addMember" >> error "unreachable"
          Just c  -> return c
        let storageJson = exprToJson (instanceStorage ci0)
        reloadedStorage <-
          case contractInstanceFromStorageValue membershipTypedContract storageJson of
            Left err -> assertFailure err >> error "unreachable"
            Right ci -> return ci
        let repo2 = M.insert addr reloadedStorage repo1
        case callEntrypointWithJsonArgs repo2 membershipTypedContract addr "removeMember" membershipSource (object ["user" .= (7 :: Int)]) of
          Left err -> assertFailure err
          Right (ret, _) -> assertEqual "removeMember finds the reloaded member" (Just (CBool TBool True)) ret
    ]
