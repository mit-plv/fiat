Ltac unfold_all :=
  repeat match goal with
           | H := _ |- _ => unfold H in *; clear H
         end.

Ltac inv_clear H :=
  inversion H; unfold_all; subst; clear H.

Ltac eapply_in_any t :=
  match goal with
      H : _ |- _ => eapply t in H
  end.
