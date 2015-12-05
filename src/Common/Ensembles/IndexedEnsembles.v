Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Logic.FunctionalExtensionality
        Coq.Sorting.Permutation Coq.Sets.Ensembles
        Fiat.Common.DecideableEnsembles
        Fiat.Common.List.PermutationFacts
        Fiat.Common.List.ListMorphisms
        Fiat.Common.List.ListFacts.

Class UnConstrRelationAbsRClass {A B : Type} :=
  { UnConstrRelationAbsR : Ensemble A -> B -> Prop }.

Section IndexedEnsembles.

  Context {ElementType : Type}.

  Record IndexedElement :=
    { elementIndex : nat;
      indexedElement : ElementType }.

  Definition IndexedEnsemble := Ensemble IndexedElement.

  Definition IndexedEnsemble_In
             (ensemble : IndexedEnsemble)
             (item : ElementType) :=
    exists idx, In _ ensemble {| elementIndex := idx; indexedElement := item |}.

  Definition IndexedEnsembleSubtract
             (element : ElementType)
             (ens : IndexedEnsemble)
    : IndexedEnsemble :=
    fun element' => indexedElement element' <> element /\ ens element'.

  (* 'Deleting' a set of tuples [R] from a relation [F] is the same
   as taking the intersection of [F] and the complement of [R]. *)
  Definition EnsembleDelete
             (F : IndexedEnsemble)
             (R : Ensemble ElementType)
    := Intersection _ F (Complement _ (fun iel => R (indexedElement iel))).

  Definition IndexedEnsembleUpdate
             (ens : IndexedEnsemble)
             (cond : Ensemble ElementType)
             (updateR : relation ElementType)
    : IndexedEnsemble
    := fun e => (exists f: IndexedElement, ((ens f) /\ cond (indexedElement f) /\ updateR (indexedElement f) (indexedElement e))
                                           /\ elementIndex e = elementIndex f) \/
                ((ens e) /\ Complement _ (fun f => cond (indexedElement f)) e).

  Definition UnIndexedEnsembleListEquivalence
             (ensemble : IndexedEnsemble)
             (l : list ElementType)  :=
    exists l', (map indexedElement l') = l /\
               (forall x, Ensembles.In _ ensemble x <-> List.In x l') /\
               NoDup (map elementIndex l').

  Definition UnConstrFreshIdx
             (ensemble : IndexedEnsemble)
             (bound : nat) :=
    forall element,
      ensemble element
      -> lt (elementIndex element) bound.

  Definition EnsembleIndexedListEquivalence
             (ensemble : IndexedEnsemble)
             (l : list ElementType) :=
    (exists bound, UnConstrFreshIdx ensemble bound)
    /\ UnIndexedEnsembleListEquivalence ensemble l.

  Global Instance EnsembleListEquivalence_AbsR :
    @UnConstrRelationAbsRClass (IndexedElement)
                               (list ElementType) :=
    {| UnConstrRelationAbsR := EnsembleIndexedListEquivalence|}.

  Ltac destruct_EnsembleIndexedListEquivalence :=
    match goal with
      H : EnsembleIndexedListEquivalence ?or ?nr |- _ =>
      let bnd := fresh "bnd" in
      let fresh_bnd := fresh "fresh_bnd" in
      let lor := fresh "l" or in
      let eqv_or := fresh "eqv_" or in
      let NoDup_lor := fresh "NoDup_" or in
      let eqv_r_n := fresh "eqv_nr" in
      let H' := fresh in
      pose proof H as H';
        destruct H' as [[bnd fresh_bnd] [lor [eqv_or [eqv_r_n NoDup_lor]]]]
    end.

  Lemma Permutation_EnsembleIndexedListEquivalence
    : forall ensemble (l l' : list _),
      EnsembleIndexedListEquivalence ensemble l
      -> Permutation l l'
      -> EnsembleIndexedListEquivalence ensemble l'.
  Proof.
    simpl; intros.
    destruct_EnsembleIndexedListEquivalence.
    econstructor; eauto.
    symmetry in H0.
    destruct (permutation_map_base indexedElement H0 _ eqv_ensemble) as [l'' [l''_eq H']].
    econstructor; split; eauto.
    constructor.
    - intros; rewrite eqv_nr.
      split; apply Permutation_in; intuition.
    - apply NoDup_modulo_permutation.
      exists (map elementIndex lensemble).
      intuition. apply Permutation_map. auto.
  Qed.

  Lemma NoDup_IndexedElement :
    forall (l1 : list IndexedElement),
      NoDup (map elementIndex l1) ->
      NoDup l1.
  Proof.
    induction l1; simpl; constructor; inversion H; subst; eauto using in_map.
  Qed.

  Definition IndexedEnsemble_Intersection
             (ens : IndexedEnsemble)
             (ens' : Ensemble ElementType)
    : IndexedEnsemble :=
    fun element' => ens element' /\ ens' (indexedElement element').

  Definition FiniteEnsemble (P : IndexedEnsemble)
    := exists l, UnIndexedEnsembleListEquivalence P l.

  Lemma NoDup_filter_map :
    forall (f : _ -> bool)
           (l : list _),
      NoDup (map elementIndex l)
      -> NoDup
           (map elementIndex
                (filter (fun a => f (indexedElement a)) l)) .
  Proof.
    induction l; simpl.
    - constructor.
    - case_eq (f (indexedElement a)); simpl; intros; inversion H0; subst; eauto.
      constructor; eauto.
      unfold not; intros; apply H3.
      revert H1; clear; induction l; simpl.
      + eauto.
      + case_eq (f (indexedElement a0)); simpl; intros; intuition.
  Qed.


  Lemma UnIndexedEnsembleListEquivalence_filter
    : forall R P (P_dec : DecideableEnsemble (A := ElementType) P) l,
      UnIndexedEnsembleListEquivalence R l
      -> UnIndexedEnsembleListEquivalence (IndexedEnsemble_Intersection R P)
                                          (filter (@DecideableEnsembles.dec _ P P_dec) l).
  Proof.
    destruct 1.
    eexists (filter (fun x => DecideableEnsembles.dec (indexedElement x)) x); simpl; intuition.
    - rewrite <- filter_map, H0; reflexivity.
    - inversion H1.
      rewrite H in H3.
      revert H3 H4; clear; induction x; simpl; intuition subst.
      + apply dec_decides_P in H4; rewrite H4; simpl; intuition.
      + find_if_inside; simpl; eauto.
    - apply filter_In in H1; intuition.
      apply dec_decides_P in H4; econstructor; eauto.
      apply H; eauto.
    - eauto using NoDup_filter_map.
  Qed.

  Lemma Permutation_UnIndexedEnsembleListEquivalence
    : forall ensemble (l l' : list ElementType),
      UnIndexedEnsembleListEquivalence ensemble l
      -> Permutation l l'
      -> UnIndexedEnsembleListEquivalence ensemble l'.
  Proof.
    simpl; intros.
    destruct H; intuition; symmetry in H0.
    destruct (PermutationFacts.permutation_map_base _ H0 _ H1)
      as [l'' [l''_eq H']].
    econstructor; split; intuition eauto.
    rewrite H'; eapply H; eauto.
    rewrite H' in H2; eapply H; eauto.
    eapply PermutationFacts.NoDup_modulo_permutation.
    eexists (map elementIndex x).
    intuition. apply Permutation_map. auto.
  Qed.

  Lemma Permutation_UnIndexedEnsembleListEquivalence'
    : forall ensemble (l l' : list _),
      UnIndexedEnsembleListEquivalence ensemble l
      -> UnIndexedEnsembleListEquivalence ensemble l'
      -> Permutation l l'.
  Proof.
    simpl; intros.
    destruct H; destruct H0; intuition subst.
    setoid_rewrite H0 in H2.
    eapply Permutation_map.
    eapply NoDup_Permutation; eauto using NoDup_IndexedElement.
  Qed.

End IndexedEnsembles.

Ltac destruct_EnsembleIndexedListEquivalence :=
  match goal with
    H : EnsembleIndexedListEquivalence ?or ?nr |- _ =>
    let bnd := fresh "bnd" in
    let fresh_bnd := fresh "fresh_bnd" in
    let lor := fresh "l" or in
    let eqv_or := fresh "eqv_" or in
    let NoDup_lor := fresh "NoDup_" or in
    let eqv_r_n := fresh "eqv_nr" in
    let H' := fresh in
    pose proof H as H';
      destruct H' as [[bnd fresh_bnd] [lor [eqv_or [eqv_r_n NoDup_lor]]]]
  end.
