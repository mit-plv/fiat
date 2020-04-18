Require Import Bedrock.IL Bedrock.Memory Coq.Strings.String.
Require Import Bedrock.Platform.Cito.SyntaxExpr.

Set Implicit Arguments.

Fixpoint eval vs expr :=
  match expr with
    | Var str => vs str
    | Const w => w
    | Binop op a b => evalBinop op (eval vs a) (eval vs b)
    | TestE op a b =>  if evalTest op (eval vs a) (eval vs b) then $1 else $0
  end.
