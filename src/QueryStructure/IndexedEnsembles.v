Require Import List String FunctionalExtensionality Ensembles.

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

End IndexedEnsembles.
