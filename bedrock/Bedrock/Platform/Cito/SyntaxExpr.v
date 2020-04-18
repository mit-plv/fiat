Require Import Bedrock.IL Bedrock.Memory Coq.Strings.String.

Inductive Expr : Set :=
| Var : string -> Expr
| Const : W -> Expr
| Binop : binop -> Expr -> Expr -> Expr
| TestE : test -> Expr -> Expr -> Expr.
