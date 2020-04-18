Require Import Bedrock.Platform.Cito.SyntaxExpr Bedrock.Platform.Cito.SemanticsExpr.
Require Import Coq.Lists.List.

Fixpoint varsIn expr:=
match expr with
  | Var s => s :: nil
  | Const w => nil
  | SyntaxExpr.Binop op a b => varsIn a ++ varsIn b
  | SyntaxExpr.TestE op a b => varsIn a ++ varsIn b
end.
