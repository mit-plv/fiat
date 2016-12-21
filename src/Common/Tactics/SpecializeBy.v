(** try to specialize all non-dependent hypotheses using [tac] *)
Ltac specialize_by' tac :=
  idtac;
  match goal with
  | [ H : ?A -> ?B |- _ ] => let H' := fresh in assert (H' : A) by tac; specialize (H H'); clear H'
  end.

Ltac specialize_by tac := repeat specialize_by' tac.
