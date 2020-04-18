Set Implicit Arguments.

Require Import Bedrock.Platform.AutoSep.

Lemma sel_upd_eq' : forall vs nm v nm', nm = nm' -> (upd vs nm v) nm' = v.
  intros; eapply sel_upd_eq; eauto.
Qed.

Lemma sel_upd_ne' : forall vs nm v nm', nm <> nm' -> (upd vs nm v) nm' = sel vs nm'.
  intros; eapply sel_upd_ne; eauto.
Qed.

Ltac sel_upd_simpl :=
  repeat
    match goal with
      | H : _ |- _ => rewrite sel_upd_eq in H by reflexivity
      | H : _ |- _ => rewrite sel_upd_ne in H by discriminate
      | |- _ => rewrite sel_upd_eq by reflexivity
      | |- _ => rewrite sel_upd_ne by discriminate
      | H : _ |- _ => rewrite sel_upd_eq' in H by reflexivity
      | H : _ |- _ => rewrite sel_upd_ne' in H by discriminate
      | |- _ => rewrite sel_upd_eq' by reflexivity
      | |- _ => rewrite sel_upd_ne' by discriminate
    end.
