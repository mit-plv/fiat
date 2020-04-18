Require Import Bedrock.Platform.AutoSep.
Require Import Coq.Lists.List.

Set Implicit Arguments.

Section TopSection.

  Definition array_to_locals ls p (_ : list string) := array ls p.

  Definition array_to_locals_ok (ls : list W) (vars : list string) := length vars = length ls /\ NoDup vars.

  Lemma materialize_locals : forall vars,
    NoDup vars
    -> forall ls, length vars = length ls
      -> exists vs, toArray vars vs = ls.
    induction 1; destruct ls; simpl; intros; try discriminate.
    exists (fun _ => $0); auto.
    injection H1; intros.
    apply IHNoDup in H2.
    destruct H2; subst.
    exists (upd x0 x w).
    f_equal.
    change (upd x0 x w x) with (sel (upd x0 x w) x).
    apply sel_upd_eq; auto.
    apply toArray_vals_eq.
    apply Forall_forall; intros.
    rewrite sel_upd_ne; congruence.
  Qed.

  Lemma array_to_locals_fwd : forall ls p vars, array_to_locals_ok ls vars -> array_to_locals ls p vars ===> Ex vs, locals vars vs 0 p * [| toArray vars vs = ls |].
    unfold array_to_locals_ok, array_to_locals; intuition.
    unfold locals.
    apply materialize_locals in H0; auto.
    destruct H0; subst.
    sepLemma.
  Qed.

  Definition hints_array_to_locals : TacPackage.
    prepare array_to_locals_fwd tt.
  Defined.

  Lemma replace_array_to_locals : forall ls p vars, array ls p = array_to_locals ls p vars.
    eauto.
  Qed.

End TopSection.
