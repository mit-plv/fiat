Require Import Bedrock.Platform.Cito.Syntax.
Require Bedrock.Platform.Cito.DepthExpr.
Require Import Bedrock.Platform.Cito.Max.

Set Implicit Arguments.

Local Notation edepth := DepthExpr.depth.

Fixpoint depth statement :=
  match statement with
    | Syntax.Skip => 0
    | Syntax.Seq a b => max (depth a) (depth b)
    | Syntax.If cond t f => max (edepth cond) (max (depth t) (depth f))
    | While cond body => max (edepth cond) (depth body)
    | Syntax.Call _ f args => max (edepth f) (max_list 0 (List.map edepth args))
    | Syntax.Label _ _ => 0
    | Syntax.Assign _ e => edepth e
  end.
