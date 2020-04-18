Set Implicit Arguments.

Require Import Coq.Lists.SetoidList.

Definition equiv_2 A B p1 p2 := forall (a : A) (b : B), p1 a b <-> p2 a b.

Lemma equiv_2_trans : forall A B a b c, @equiv_2 A B a b -> equiv_2 b c -> equiv_2 a c.
  unfold equiv_2; intros; split; intros.
  eapply H0; eapply H; eauto.
  eapply H; eapply H0; eauto.
Qed.

Lemma InA_eq_In_iff : forall elt (ls : list elt) (x : elt), InA eq x ls <-> List.In x ls.
  induction ls; simpl; intros.
  intuition.
  eapply InA_nil in H; eauto.
  split; intros.
  inversion H; subst.
  eauto.
  right.
  eapply IHls.
  eauto.
  destruct H.
  subst.
  econstructor 1.
  eauto.
  econstructor 2.
  eapply IHls.
  eauto.
Qed.

Lemma InA_weaken :
  forall A (P : A -> A -> Prop) (x : A) (ls : list A),
    InA P x ls ->
    forall (P' : A -> A -> Prop) x',
      (forall y, P x y -> P' x' y) ->
      InA P' x' ls.
  induction 1; simpl; intuition.
Qed.

Lemma equiv_InA : forall elt (eq1 eq2 : elt -> elt -> Prop), equiv_2 eq1 eq2 -> equiv_2 (InA eq1) (InA eq2).
  unfold equiv_2; split; intros; eapply InA_weaken; eauto; intros; eapply H; eauto.
Qed.

Lemma In_InA : forall A (x : A) ls,
  List.In x ls
  -> InA eq x ls.
  intros; eapply InA_eq_In_iff; eauto.
Qed.

Lemma InA_In : forall A (x : A) ls,
  InA eq x ls ->
  List.In x ls.
  intros; eapply InA_eq_In_iff; eauto.
Qed.

Local Hint Constructors List.NoDup NoDupA.

Lemma NoDupA_NoDup : forall A ls,
  @NoDupA A eq ls
  -> List.NoDup ls.
  induction 1; intuition auto using In_InA.
Qed.

Lemma NoDup_NoDupA : forall A ls,
  List.NoDup ls ->
  @NoDupA A eq ls.
  induction 1; intuition auto using InA_In.
Qed.
