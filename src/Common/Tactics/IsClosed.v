(** Test that a term is ground/closed *)
Ltac is_closed x := let test := constr:(x) in idtac.
