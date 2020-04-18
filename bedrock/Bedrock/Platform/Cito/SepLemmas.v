(*
Lemma star_diff_ptrs : forall specs st p1 p2, interp specs (![p1 =?>1 * p2 =?> 1] st) -> p1 <> p2.
  rewrite sepFormula_eq.
  propxFo.
  subst.
  unfold smem_get_word in *.
  simpl in *.
  case_eq (smem_get p2 x1).
  intros.
  clear H4.
  case_eq (smem_get p2 x4).
  clear H7.
  intros.
  destruct H3.
  subst.
  destruct H1.
  destruct H2.
  subst.
  Require Import Bootstrap.
  eapply disjoint_get_fwd in H1.
  eauto.
  erewrite join_Some by eassumption.
  discriminate.
  erewrite join_Some by eassumption.
  discriminate.
  intros.
  rewrite H0 in H7.
  discriminate.
  intros.
  rewrite H in H4.
  discriminate.
Qed.
*)
