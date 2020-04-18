Ltac copy h := generalize h; intro.

Ltac copy_as h h' := generalize h; intro h'.

Ltac inject h := injection h; intros; subst; clear h.

(* unify and get rid of b *)
Ltac unif b :=
  match goal with
    | H1 : ?L = Some _, H2 : ?L = Some b |- _ => rewrite H1 in H2; symmetry in H2; inject H2
  end.
