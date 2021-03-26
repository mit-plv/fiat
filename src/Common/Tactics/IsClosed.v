Require Export Fiat.Common.Coq__8_4__8_5__Compat.
(** Test that a term is ground/closed *)
Ltac is_closed x := let test := constr:(x) in idtac.
