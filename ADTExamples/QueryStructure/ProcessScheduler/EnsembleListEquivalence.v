Require Import Ensembles List.

Definition EnsembleListEquivalence {A: Type} (ensemble: A -> Prop) (seq: list A) :=
  forall x, Ensembles.In _ ensemble x <-> List.In x seq.
