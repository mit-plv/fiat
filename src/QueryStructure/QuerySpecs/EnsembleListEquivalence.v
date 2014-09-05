Require Import Ensembles List Coq.Lists.SetoidList Tuple QueryStructure.

Definition EnsembleListEquivalence {A: Type} (ensemble: A -> Prop) (seq: list A) :=
  NoDup seq /\
  forall x, Ensembles.In _ ensemble x <-> List.In x seq.

Definition UnIndexedEnsembleListEquivalence
           {heading} R (l : list (@Tuple heading))  :=
  exists l', (map indexedTuple l') = l /\
  EnsembleListEquivalence R l'.

Definition UnConstrFreshIdx {heading} (R : Ensemble (@IndexedTuple heading)) (bound : nat) :=
  forall tup, R tup -> lt (tupleIndex tup) bound.

Definition EnsembleIndexedListEquivalence {heading}
           (R : Ensemble (@IndexedTuple heading))
           (l : list (@Tuple heading)) :=
  (exists bound, UnConstrFreshIdx R bound)
  /\ UnIndexedEnsembleListEquivalence R l.

Instance EnsembleListEquivalence_AbsR {heading}:
  @UnConstrRelationAbsRClass (@IndexedTuple heading)
                             (list (@Tuple heading)) :=
  {| UnConstrRelationAbsR := @EnsembleIndexedListEquivalence heading|}.
