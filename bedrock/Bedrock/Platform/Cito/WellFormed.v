Require Import Bedrock.Platform.Cito.Syntax.
Require Import Bedrock.IL.

Set Implicit Arguments.

Inductive args_not_too_long : Stmt -> Prop :=
  | CallCase : forall x f args, goodSize (2 + length args) -> args_not_too_long (Call x f args)
  | SkipCase : args_not_too_long Skip
  | SeqCase : forall a b, args_not_too_long a -> args_not_too_long b -> args_not_too_long (Seq a b)
  | IfCase : forall e t f, args_not_too_long t -> args_not_too_long f -> args_not_too_long (If e t f)
  | WhileCase : forall e s, args_not_too_long s -> args_not_too_long (While e s)
  | LabelCase : forall x l, args_not_too_long (Label x l)
  | AssignCase : forall x e, args_not_too_long (Syntax.Assign x e).

Definition wellformed := args_not_too_long.
