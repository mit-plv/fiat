Require Import Bedrock.Platform.Cito.SyntaxExpr.
Require Import Bedrock.StringSet.
Import StringSet.

Set Implicit Arguments.

Fixpoint free_vars expr:=
  match expr with
    |Var s => singleton s
    |Const w => empty
    |Binop op a b => union (free_vars a) (free_vars b)
    |TestE te a b => union (free_vars a) (free_vars b)
  end.
