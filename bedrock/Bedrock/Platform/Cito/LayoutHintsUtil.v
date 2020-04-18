Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.ADT.
Require Import Bedrock.Platform.Cito.RepInv Bedrock.Platform.Cito.WordMap.
Require Import Bedrock.Platform.Cito.Inv.

Lemma starL_in : forall A P x (ls : list A),
  NoDup ls
  -> In x ls
  -> exists ls', (P x * Bags.starL P ls' ===> Bags.starL P ls)
    /\ NoDup ls'
    /\ (forall y, In y ls' <-> y <> x /\ In y ls).
  induction 1; simpl; intuition subst.

  eexists; intuition idtac.
  apply Himp_refl.
  auto.
  congruence.
  tauto.
  congruence.
  auto.

  destruct H1; intuition.
  exists (x0 :: x1); intuition idtac.
  simpl.
  eapply Himp_trans; [ | apply Himp_star_frame; [
    apply Himp_refl | apply H3 ] ].
  generalize dependent (Bags.starL P); intros.
  sepLemma.
  constructor; auto.
  intro.
  apply H5 in H4.
  tauto.
  subst; simpl in *; intuition subst.
  auto.
  apply H5 in H6; intuition.
  simpl in *; intuition subst.
  apply H5 in H6; intuition.
  subst; simpl; tauto.
  right; apply H5.
  auto.
Qed.

Lemma starL_out : forall A P x (ls : list A),
  NoDup ls
  -> In x ls
  -> exists ls', (Bags.starL P ls ===> P x * Bags.starL P ls')
    /\ NoDup ls'
    /\ (forall y, In y ls' <-> y <> x /\ In y ls).
  induction 1; simpl; intuition subst.

  eexists; intuition idtac.
  apply Himp_refl.
  auto.
  congruence.
  tauto.
  congruence.
  auto.

  destruct H1; intuition.
  exists (x0 :: x1); intuition idtac.
  simpl.
  eapply Himp_trans; [ apply Himp_star_frame; [
    apply Himp_refl | apply H3 ] | ].
  generalize dependent (Bags.starL P); intros.
  sepLemma.
  constructor; auto.
  intro.
  apply H5 in H4.
  tauto.
  subst; simpl in *; intuition subst.
  auto.
  apply H5 in H6; intuition.
  simpl in *; intuition subst.
  apply H5 in H6; intuition.
  subst; simpl; tauto.
  right; apply H5.
  auto.
Qed.

Lemma starL_permute : forall A P (ls1 : list A),
  NoDup ls1
  -> forall ls2, NoDup ls2
    -> (forall x, In x ls1 <-> In x ls2)
    -> Bags.starL P ls1 ===> Bags.starL P ls2.
  induction 1.

  inversion_clear 1; simpl; intros.
  apply Himp_refl.
  exfalso; eapply H; eauto.

  intros.
  eapply starL_in in H1.
  Focus 2.
  apply H2.
  simpl; eauto.

  destruct H1; intuition.
  simpl.
  eapply Himp_trans; [ | apply H3 ].
  apply Himp_star_frame; try apply Himp_refl.
  apply IHNoDup; auto.
  intuition.
  simpl in *.
  apply H5; intuition.
  apply H2; auto.
  apply H5 in H4; intuition.
  simpl in *.
  apply H2 in H7.
  intuition.
Qed.
