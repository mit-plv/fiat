Require Import Ensembles List Coq.Lists.SetoidList.

Definition EnsembleListEquivalence {A: Type} (ensemble: A -> Prop) (seq: list A) :=
  NoDup seq /\
  forall x, Ensembles.In _ ensemble x <-> List.In x seq.
