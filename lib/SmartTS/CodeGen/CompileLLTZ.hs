module SmartTS.CodeGen.CompileLLTZ where

import qualified SmartTS.IR.AST as A
import qualified SmartTS.IR.LLTZ as L

translateType :: A.Type -> L.Type
translateType A.TInt             = L.TInt
translateType A.TBool            = L.TBool
translateType A.TUnit            = L.TUnit
translateType (A.TRecord fields) = L.TTuple (L.RowNode (map toLeaf fields))
  where
    toLeaf (name, ty) = L.RowLeaf (Just (L.Label name)) (translateType ty)

translateExpression :: A.TypedExpr -> L.Expr
translateExpression expr =
  let mkExpr e t = L.Expr e $ translateType t
  in case expr of
    (A.CInt ty value) -> mkExpr (L.Const (L.CInt value)) ty
    _ -> undefined
