Require Import Bedrock.Platform.Facade.
Require Import AutoDB.

Definition bedrock_test :=
  (ret (@Word.wmult 32
                    (Word.wplus  (IL.natToW 3) (IL.natToW 4))
                    (Word.wminus (IL.natToW 5) (IL.natToW 6)))).

Definition facade_test :=
  ret (SyntaxExpr.Binop
         IL.Times
         (SyntaxExpr.Var "$1")
         (SyntaxExpr.Var "$2")).

Eval compute in (eval (StringMap.StringMap.empty (Value nat)) (SyntaxExpr.Binop IL.Plus (SyntaxExpr.Const (IL.natToW 3)) (SyntaxExpr.Const (IL.natToW 3)))).
