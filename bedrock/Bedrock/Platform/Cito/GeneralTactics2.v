Set Implicit Arguments.

Ltac not_not :=
  match goal with
    | H : ~ _ |- ~ _ => unfold not; intro; contradict H
  end.

Ltac nintro := unfold not; intros.
