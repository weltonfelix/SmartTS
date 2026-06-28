module SmartTS.CodeGen.CompileLLTZ where

import qualified SmartTS.IR.AST as A
import qualified SmartTS.IR.LLTZ as L
import qualified Data.Map.Strict as M

translateType :: A.Type -> L.Type
translateType A.TInt             = L.TInt
translateType A.TBool            = L.TBool
translateType A.TUnit            = L.TUnit
translateType (A.TRecord fields) = L.TTuple (L.RowNode (map toLeaf fields))
  where
    toLeaf (name, ty) = L.RowLeaf (Just (L.Label name)) (translateType ty)
translateType (A.TMap k v) = L.TMap (translateType k) (translateType v)

-- Basic Expressions
translateExpression :: A.TypedExpr -> L.Expr
translateExpression (A.CInt  ty value) = mkExpr (L.Const (L.CInt value)) ty
translateExpression (A.CBool ty value) = mkExpr (L.Const (L.CBool value)) ty
translateExpression (A.Var   ty name)  = mkExpr (L.Variable (L.Var name)) ty
-- Boolean Expressions
translateExpression (A.And ty e1 e2) = translateBinaryExpression e1 e2 ty L.PrimAnd
translateExpression (A.Or  ty e1 e2) = translateBinaryExpression e1 e2 ty L.PrimOr
translateExpression (A.Not ty e)     = translateUnaryExpression e ty L.PrimNot
translateExpression (A.MapEmpty ty) =
  let lt = translateType ty
   in case lt of
        L.TMap k v -> L.Expr (L.Prim (L.PrimEmptyMap k v) []) lt
        _ -> error "[Impossible] MapEmpty with non-map type after type checker."
translateExpression (A.MapVal ty m) =
  let lt = translateType ty
   in case lt of
        L.TMap k v ->
          foldr
            (\(kExpr, vExpr) acc ->
              let kExpr' = translateExpression kExpr
                  vExpr' = translateExpression vExpr
                  someV  = L.Expr (L.Prim L.PrimSome [vExpr']) (L.TOption v)
               in L.Expr (L.Prim L.PrimUpdate [kExpr', someV, acc]) lt)
            (L.Expr (L.Prim (L.PrimEmptyMap k v) []) lt)
            (M.toList m)
        _ -> error "[Impossible] MapVal with non-map type after type checker."

translateExpression (A.MapMemCheck ty mapExpr keyExpr) =
  L.Expr
    (L.Prim L.PrimMem
      [ translateExpression keyExpr
      , translateExpression mapExpr
      ])
    (translateType ty)   

-- TODO: Write here the translation of the remaining expressions.
translateExpression (A.MapRem ty mapExpr keyExpr) =
  let mapExpr' = translateExpression mapExpr
      keyExpr' = translateExpression keyExpr
      valTy = case translateType ty of
        L.TMap _ v -> v
        _ -> error "Cannot perform MapRem in a non-map type"
      noneExpr = L.Expr (L.Prim (L.PrimNone valTy) []) (L.TOption valTy)
   in mkExpr (L.Prim L.PrimUpdate [keyExpr', noneExpr, mapExpr']) ty

-- MapAccess 
translateExpression (A.MapAccess ty mapExpr keyExpr) =
  let
    mapExpr' = translateExpression mapExpr
    keyExpr' = translateExpression keyExpr

    optionExpr =
      L.Expr
        (L.Prim L.PrimGet [keyExpr', mapExpr'])
        (L.TOption (translateType ty))

    binder =
      L.LambdaBinder
        ( (L.Var "__value"), translateType ty )
        (L.Expr
          (L.Variable (L.Var "__value"))
          (translateType ty))

    failExpr =
      L.Expr
        (L.Prim L.PrimFailwith
          [L.Expr (L.Const (L.CString "MAP_ACCESS_KEY_NOT_FOUND")) L.TString])
        (translateType ty)

  in
    L.Expr
      (L.IfNone optionExpr failExpr binder)
      (translateType ty)

-- Translate an assignment to an LValue into an LLTZ expression.
compileAssignLValue :: A.TypedLValue -> L.Expr -> L.Expr
compileAssignLValue (A.LVar var) expr = L.Expr (L.Assign (L.MutVar var) expr) L.TUnit
compileAssignLValue (A.LMapAccess lv key) expr =
  let keyExpr' = translateExpression key
      valTy = L.exprType expr
      someExpr = L.Expr (L.Prim L.PrimSome [expr]) (L.TOption valTy)

      mapExpr' = translateExpression (lValueToExpr lv)

      mapTy = L.exprType mapExpr'
      updateExpr = L.Expr (L.Prim L.PrimUpdate [keyExpr', someExpr, mapExpr']) mapTy
   in compileAssignLValue lv updateExpr

-- Translate an LValue into an LLTZ expression. This is used to read from the LValue.
lValueToExpr :: A.TypedLValue -> A.TypedExpr
lValueToExpr A.LStorage = A.StorageExpr A.TUnit
lValueToExpr (A.LVar name) = A.Var A.TUnit name
lValueToExpr (A.LField lv name) = A.FieldAccess A.TUnit (lValueToExpr lv) name
lValueToExpr (A.LMapAccess lv key) = A.MapAccess A.TUnit (lValueToExpr lv) key

-- | Translate a SmartTS block (a list of statements) into a nested LLTZ let-expression.
--
-- LLTZ is an expression-based language derived from the Lambda calculus.
-- A statement sequence is encoded as a chain of LetIn / LetMutIn nodes where
-- each binding carries the rest of the block as its continuation.  The type of
-- the whole chain is propagated from the innermost expression, so a block that
-- ends in a ReturnStmt carries the return type all the way to the top.
--
-- TODO: Reason about the effect of 'return statements'
translateBlock :: [A.TypedStmt] -> L.Expr
translateBlock [] = L.Expr L.Skip L.TUnit
translateBlock (s:ss) =
  case s of
    (A.VarDeclStmt name _ty expr) -> L.Expr (L.LetMutIn (L.MutVar name) (translateExpression expr) block) ty
    (A.ValDeclStmt name _ty expr) -> L.Expr (L.LetIn    (L.Var  name)   (translateExpression expr) block) ty
    -- For effectful statements whose value is not bound, we sequence them by
    -- discarding the result via a wildcard binding.
    _                             -> L.Expr (L.LetIn (L.Var "_") (translateStatement s) block) ty
  where
    block = translateBlock ss
    ty    = L.exprType block

-- | Translate a single SmartTS statement into an LLTZ expression.
translateStatement :: A.TypedStmt -> L.Expr
-- Translate the variable assignment statement.
-- TODO: Deal with the remaining LValues (storage and record field).
translateStatement (A.AssignmentStmt lv expr) = compileAssignLValue lv (translateExpression expr)
-- Translate the if-then-else statement.
translateStatement (A.IfStmt cond s1 (Just s2)) =
  let cond' = translateExpression cond
      s1'   = translateStatement s1
      s2'   = translateStatement s2
  in
    -- Branch type equality is guaranteed by the type checker; the assert
      -- is a defensive check that catches any inconsistency in this pass.
      assert
        (L.exprType s1' == L.exprType s2')
        "[Impossible] Inconsistent branch types."
        (L.Expr (L.IfBool cond' s1' s2') (L.exprType s1'))
-- Translate the if-then statement (no else branch).
translateStatement (A.IfStmt cond s1 Nothing) =
  let cond' = translateExpression cond
      s1'   = translateStatement s1
   in L.Expr (L.IfBool cond' s1' (L.Expr L.Skip L.TUnit)) (L.exprType s1')
-- Translate the while statement.
-- The result type is TUnit because Michelson's LOOP instruction does not produce
-- a value: when the loop exits the stack is in the same state as before the
-- condition was first evaluated, so no value escapes the loop.
translateStatement (A.WhileStmt cond block) =
  let cond'  = translateExpression cond
      block' = translateStatement block
   in L.Expr (L.While cond' block') L.TUnit

translateStatement (A.VarDeclStmt name _ expr) =
  L.Expr
    (L.LetMutIn
      (L.MutVar name)
      (translateExpression expr)
      (L.Expr L.Skip L.TUnit))
    L.TUnit

translateStatement (A.ValDeclStmt name _ expr) =
  L.Expr
    (L.LetIn
      (L.Var name)
      (translateExpression expr)
      (L.Expr L.Skip L.TUnit))
    L.TUnit
-- In LLTZ (an expression-based IR) there is no explicit return construct:
-- the value of the last expression in a block is the return value.
translateStatement (A.ReturnStmt expr) = translateExpression expr
-- Translate mutable variable declaration.
-- Translate a nested block of statements.
translateStatement (A.SequenceStmt stmts) = translateBlock stmts

-- Auxiliary functions for translating expressions.
mkExpr :: L.ExprDesc -> A.Type -> L.Expr
mkExpr e t = L.Expr e $ translateType t

translateUnaryExpression :: A.TypedExpr -> A.Type -> L.Primitive -> L.Expr
translateUnaryExpression e ty prim = mkExpr (L.Prim prim [e']) ty
  where e' = translateExpression e

translateBinaryExpression :: A.TypedExpr -> A.TypedExpr -> A.Type -> L.Primitive -> L.Expr
translateBinaryExpression left right ty prim = mkExpr (L.Prim prim [left', right']) ty
  where
    left'  = translateExpression left
    right' = translateExpression right

assert :: Bool -> String -> a -> a
assert False msg _ = error msg
assert True  _   v = v
