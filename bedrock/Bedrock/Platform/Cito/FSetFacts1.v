Set Implicit Arguments.

Require Import Coq.Structures.DecidableTypeEx.
Require Import Coq.FSets.FSetInterface.
Require Coq.FSets.FSetProperties.
Require Bedrock.Platform.Cito.GeneralTactics.
Require Bedrock.Platform.Cito.SetoidListFacts.
Require Bedrock.Platform.Cito.ListFacts1.

Module UWFacts_fun (E : UsualDecidableType) (Import M : WSfun E).

  Import Coq.FSets.FSetProperties.
  Module Import P := WProperties_fun E M.
  Import FM.

  Module FSetNotations.
    Infix "+" := union : fset_scope.
    Infix "-" := diff : fset_scope.
    Infix "*" := inter : fset_scope.
    Infix "<=" := Subset : fset_scope.
    Delimit Scope fset_scope with fset.
    Module FSetNotationsTrial.
      Notation " [ ] " := empty : fset_scope.
      Notation "m %- k" := (remove k m) (at level 60) : fset_scope.
    End FSetNotationsTrial.
  End FSetNotations.

  Definition Disjoint a b := forall x, ~ (In x a /\ In x b).

  Import ListNotations.
  Import Bedrock.Platform.Cito.GeneralTactics.

  Import Bedrock.Platform.Cito.SetoidListFacts.

  Lemma NoDup_elements : forall s, List.NoDup (elements s).
    intros.
    apply NoDupA_NoDup.
    apply elements_3w.
  Qed.

  Lemma of_list_fwd : forall e ls,
    In e (of_list ls)
    -> List.In e ls.
    intros.
    eapply of_list_1 in H.
    eapply InA_eq_In_iff; eauto.
  Qed.

  Lemma of_list_bwd : forall e ls,
    List.In e ls
    -> In e (of_list ls).
    intros.
    eapply of_list_1.
    eapply InA_eq_In_iff; eauto.
  Qed.

  Local Hint Resolve of_list_fwd of_list_bwd.

  Lemma of_list_spec : forall e ls, In e (of_list ls) <-> List.In e ls.
    generalize of_list_fwd, of_list_bwd; firstorder.
  Qed.

  Lemma of_list_singleton : forall e, Equal (of_list [e]) (singleton e).
    intros.
    unfold of_list.
    simpl.
    unfold Equal.
    split; intros.
    eapply singleton_iff.
    eapply add_iff in H.
    openhyp.
    eauto.
    eapply empty_iff in H.
    intuition.
    eapply singleton_iff in H.
    eapply add_iff; eauto.
  Qed.

  Lemma of_list_cons : forall e ls, Equal (of_list (e :: ls)) (union (singleton e) (of_list ls)).
    unfold Equal; intuition.
    simpl in *.
    apply add_iff in H; intuition (subst; eauto).
    apply union_iff; left; apply singleton_iff; auto.
    eapply union_iff; eauto.
    simpl.
    apply union_iff in H.
    openhyp.
    eapply singleton_iff in H.
    eapply add_iff; eauto.
    eapply add_iff; eauto.
  Qed.

  Global Add Morphism Disjoint with signature Equal ==> Equal ==> iff as Disjoint_m.
    unfold Equal, Disjoint; firstorder.
  Qed.

  Local Hint Resolve union_2 union_3.

  Lemma Disjoint_union : forall s1 s2 s3, Disjoint s1 (union s2 s3) <-> (Disjoint s1 s2 /\ Disjoint s1 s3).
    unfold Disjoint; intuition eauto.
    apply union_iff in H3; intuition eauto.
  Qed.

  Local Hint Resolve singleton_2.

  Lemma Disjoint_singletons : forall e1 e2, Disjoint (singleton e1) (singleton e2) <-> e1 <> e2.
    unfold Disjoint; intuition eauto.
    apply singleton_iff in H1; apply singleton_iff in H2.
    congruence.
  Qed.

  Lemma Disjoint_singleton : forall e s, Disjoint (singleton e) s <-> ~ In e s.
    unfold Disjoint; intuition eauto.
    apply singleton_iff in H1.
    congruence.
  Qed.

  Local Hint Resolve inter_1 inter_2 inter_3.

  Lemma inter_is_empty_iff : forall s1 s2, is_empty (inter s1 s2) = true <-> Disjoint s1 s2.
    unfold Disjoint; intuition eauto.
    apply is_empty_2 in H.
    eapply H; eauto.
    apply is_empty_1.
    hnf; intuition.
    eauto.
  Qed.

  Lemma Equal_Subset_iff : forall s1 s2, Equal s1 s2 <-> (Subset s1 s2 /\ Subset s2 s1).
    unfold Equal, Subset; firstorder.
  Qed.

  Require Import IffFacts.
  Export IffFacts.

  Lemma singleton_not_iff x x' : ~ In x' (singleton x) <-> x <> x'.
  Proof.
    eapply iff_not_iff.
    eapply singleton_iff.
  Qed.

  Lemma union_not_iff a b x : ~ In x (union a b) <-> (~ In x a /\ ~ In x b).
  Proof.
    etransitivity.
    - eapply iff_not_iff.
      eapply union_iff.
    - intuition.
  Qed.

  Lemma of_list_not_iff x ls : ~ In x (of_list ls) <-> ~ List.In x ls.
    eapply iff_not_iff.
    eapply of_list_spec.
  Qed.

  Lemma set_disjoint_list_disjoint ls1 ls2 : Disjoint (of_list ls1) (of_list ls2) -> ListFacts1.Disjoint ls1 ls2.
    unfold ListFacts1.Disjoint, Disjoint.
    intros Hdisj e [Hin1 Hin2].
    eapply Hdisj; split; eapply of_list_spec; eauto.
  Qed.

  Lemma list_disjoint_set_disjoint ls1 ls2 : ListFacts1.Disjoint ls1 ls2 -> Disjoint (of_list ls1) (of_list ls2).
    unfold ListFacts1.Disjoint, Disjoint.
    intros Hdisj e [Hin1 Hin2].
    eapply Hdisj; split; eapply of_list_spec; eauto.
  Qed.

  Lemma compat_bool_f A (f : A -> bool) : SetoidList.compat_bool Logic.eq f.
    unfold SetoidList.compat_bool.
    intuition.
  Qed.

  Lemma for_all_elim p s : for_all p s = true -> forall x, In x s -> p x = true.
  Proof.
    intros H x Hin.
    eapply for_all_iff in H; eauto.
    eapply compat_bool_f; eauto.
  Qed.

  Global Arguments for_all_elim [p s] _ _ _.

  Lemma for_all_intro p s : (forall x, In x s -> p x = true) -> for_all p s = true.
  Proof.
    intros H.
    eapply for_all_iff; eauto.
    eapply compat_bool_f; eauto.
  Qed.

  Lemma for_all_singleton_elim p x : for_all p (singleton x) = true -> p x = true.
  Proof.
    intros H.
    specialize (for_all_elim H); intros HH.
    eapply HH.
    eapply singleton_iff; eauto.
  Qed.

  Lemma for_all_union_elim p a b : for_all p (union a b) = true -> for_all p a = true /\ for_all p b = true.
  Proof.
    intros H.
    specialize (for_all_elim H); intros HH.
    split.
    - eapply for_all_intro.
      intros; eapply HH.
      eapply union_iff; intuition.
    - eapply for_all_intro.
      intros; eapply HH.
      eapply union_iff; intuition.
  Qed.

  Lemma for_all_of_list_elim p ls : for_all p (of_list ls) = true -> List.forallb p ls = true.
  Proof.
    intros H.
    specialize (for_all_elim H); intros HH.
    eapply List.forallb_forall.
    intros x Hin.
    eapply HH.
    eapply of_list_spec; eauto.
  Qed.

End UWFacts_fun.
