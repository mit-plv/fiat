Require Export Fiat.Common.Coq__8_4__8_5__Compat.
(** find the head of the given expression *)
Ltac head expr :=
  match expr with
  | ?f _ => head f
  | _ => expr
  end.

Ltac head_hnf expr := let expr' := eval hnf in expr in head expr'.
