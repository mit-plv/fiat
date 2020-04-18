Require Import Bedrock.Platform.Cito.SyntaxExpr.

(* The depth of stack actually used by compileExpr *)
Fixpoint depth expr :=
  match expr with
    | Var _ => 0
    | Const _ => 0
    | Binop _ a b => max (depth a) (S (depth b))
    | TestE _ a b => max (depth a) (S (depth b))
  end.
