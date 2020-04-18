Set Implicit Arguments.

Require Import Coq.Lists.List.

Section TopSection.

  Fixpoint app_all A (ls : list (list A)) :=
    match ls with
      | nil => nil
      | x :: xs => x ++ app_all xs
    end.

  Definition Disjoint A (ls1 ls2 : list A) := forall e : A, ~ (In e ls1 /\ In e ls2).

  Definition IsInjection A B (f : A -> B) := forall x y, x <> y -> f x <> f y.

  Definition Injective A B (f : A -> B) := forall x1 x2, f x1 = f x2 -> x1 = x2.

  Lemma Injective_IsInjection A B (f : A -> B) : Injective f -> IsInjection f.
  Proof.
    unfold Injective, IsInjection in *; intuition.
  Qed.

  Variable t : Type.
  Variable B : Type.

  Implicit Types ls : list t.
  Implicit Types f : t -> B.
  Implicit Types x y e a : t.

  Lemma map_app_all : forall f lsls, map f (app_all lsls) = app_all (map (fun ls => map f ls) lsls).
    induction lsls; simpl; intros; eauto.
    rewrite map_app; f_equal; eauto.
  Qed.

  Require Import Coq.Bool.Sumbool.
  Require Import Bedrock.Platform.Cito.GeneralTactics.

  Lemma find_spec : forall (f : t -> bool) ls a, find f ls = Some a -> f a = true /\ In a ls.
    induction ls; simpl; intuition; try discriminate;
    (destruct (sumbool_of_bool (f a));
     [rewrite e in H; injection H; intros; subst; eauto |
      rewrite e in H; eapply IHls in H; openhyp; eauto]).
  Qed.

  Lemma find_spec_None : forall (f : t -> bool) ls, List.find f ls = None -> ~ exists a, List.In a ls /\ f a = true.
    induction ls; simpl; intuition.
    openhyp; intuition.
    openhyp.
    subst.
    rewrite H1 in H.
    intuition.
    eapply IHls.
    discriminate.
    discriminate.
    destruct (f a); intuition.
    discriminate.
    eapply H2.
    eexists; split; eauto.
  Qed.

  Lemma In_app_all_intro : forall lsls ls e, In e ls -> In ls lsls -> In e (app_all lsls).
    induction lsls; simpl; intros.
    eauto.
    openhyp.
    subst.
    eapply in_or_app.
    eauto.
    eapply in_or_app.
    right.
    eauto.
  Qed.

  Lemma In_app_all_elim : forall lsls x, In x (app_all lsls) -> exists ls, In x ls /\ In ls lsls.
    induction lsls; simpl; intros.
    intuition.
    eapply in_app_or in H.
    openhyp.
    eexists.
    eauto.
    eapply IHlsls in H.
    openhyp.
    eexists; eauto.
  Qed.

  Lemma Disjoint_symm : forall ls1 ls2, Disjoint ls1 ls2 -> Disjoint ls2 ls1.
    unfold Disjoint; intros; firstorder.
  Qed.

  Lemma Disjoint_incl : forall ls1 ls2 ls1' ls2', Disjoint ls1 ls2 -> incl ls1' ls1 -> incl ls2' ls2 -> Disjoint ls1' ls2'.
    unfold Disjoint, incl; intros; firstorder.
  Qed.

  Lemma incl_map : forall f ls1 ls2, incl ls1 ls2 -> incl (map f ls1) (map f ls2).
    unfold incl.
    intros.
    eapply in_map_iff in H0.
    openhyp.
    subst.
    eapply H in H1.
    eapply in_map_iff.
    eexists.
    eauto.
  Qed.

  Lemma Disjoint_map : forall f ls1 ls2, Disjoint (map f ls1) (map f ls2) -> Disjoint ls1 ls2.
    unfold Disjoint; intros.
    intuition.
    eapply H.
    split; eapply in_map; eauto.
  Qed.

  Lemma Injection_NoDup : forall f ls, IsInjection f -> NoDup ls -> NoDup (map f ls).
    unfold IsInjection.
    induction ls; simpl; intros.
    econstructor.
    inversion H0; subst.
    econstructor.
    intuition.
    contradict H3.
    eapply in_map_iff in H1.
    openhyp.
    eapply H in H1.
    intuition.
    intros.
    subst.
    inversion H0; subst.
    contradiction.
    eapply IHls.
    eauto.
    eauto.
  Qed.

  Lemma NoDup_app : forall ls1 ls2, NoDup ls1 -> NoDup ls2 -> Disjoint ls1 ls2 -> NoDup (ls1 ++ ls2).
    unfold Disjoint.
    induction ls1; simpl; intros.
    eauto.
    econstructor.
    intuition.
    eapply in_app_or in H2.
    openhyp.
    inversion H; subst.
    contradiction.
    eapply H1.
    eauto.
    eapply IHls1.
    inversion H; subst.
    eauto.
    eauto.
    intros.
    firstorder.
  Qed.

End TopSection.

Require Import Coq.Bool.Bool.

Local Open Scope bool_scope.

Fixpoint forall2 A B (pred : A -> B -> bool) ls1 ls2 :=
  match ls1, ls2 with
    | a :: ls1', b :: ls2' => pred a b && forall2 pred ls1' ls2'
    | nil, nil => true
    | _, _ => false
  end.

Lemma forall2_sound A B pred (P : A -> B -> Prop) : (forall a b, pred a b = true -> P a b) -> forall ls1 ls2, forall2 pred ls1 ls2 = true -> List.Forall2 P ls1 ls2.
Proof.
  intros Hs.
  induction ls1; destruct ls2; simpl; try solve [intros; try discriminate; intuition].
  intros Hp; eapply andb_true_iff in Hp.
  openhyp; econstructor; eauto.
Qed.
