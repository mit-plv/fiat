Require Import Coq.Lists.List Coq.Strings.String
        Coq.Logic.FunctionalExtensionality
        Coq.Sorting.Permutation Coq.Sets.Ensembles
        Fiat.Common.List.PermutationFacts.

Class UnConstrRelationAbsRClass {A B : Type} :=
  { UnConstrRelationAbsR : Ensemble A -> B -> Prop }.

Section IndexedEnsembles.

  Context {ElementType : Type}.

  Record IndexedElement :=
    { elementIndex : nat;
      indexedElement : ElementType }.

  Definition IndexedEnsemble := Ensemble IndexedElement.

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
             (update : ElementType -> ElementType)
  : IndexedEnsemble
    := fun e => (exists f: IndexedElement, ((ens f) /\ cond (indexedElement f) /\ (indexedElement e) = (update (indexedElement f))) /\ elementIndex e = elementIndex f) \/
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
