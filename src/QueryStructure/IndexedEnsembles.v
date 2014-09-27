Require Import List String FunctionalExtensionality Permutation
         Ensembles AdditionalPermutationLemmas.

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

  (* Definition IndexedEnsembleUpdate
             (element : ElementType)
             (ens : IndexedEnsemble)
             (cond : Ensemble ElementType)
             (f : ElementType -> ElementType)
  : IndexedEnsemble :=
    fun element' =>
        indexedElement element' <> element /\ ens element'.

  : Prop := ((fst kv) = k /\ exists v, (snd kv) = f v /\ In _ ens (k, v)) \/
            (EnsembleRemove k ens kv). *)

  Definition EnsembleListEquivalence
             {A}
             (ensemble : Ensemble A)
             (seq : list A) :=
    NoDup seq /\
    forall x, Ensembles.In _ ensemble x <-> List.In x seq.

  Definition UnIndexedEnsembleListEquivalence
             (ensemble : IndexedEnsemble)
             (l : list ElementType)  :=
    exists l', (map indexedElement l') = l /\
               EnsembleListEquivalence ensemble l'.

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
        destruct H' as [[bnd fresh_bnd] [lor [eqv_or [NoDup_lor eqv_r_n]]]]
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
    apply NoDup_modulo_permutation; eauto.
    intros; rewrite eqv_nr.
    split; apply Permutation_in; eauto; symmetry; eauto.
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
        destruct H' as [[bnd fresh_bnd] [lor [eqv_or [NoDup_lor eqv_r_n]]]]
    end.
