Require Export Coq.Sets.Ensembles.
Require Export Fiat.Common.ReservedNotations.

Delimit Scope Ensemble_scope with ensemble.
Bind Scope Ensemble_scope with Ensemble.

Infix "∪" := (Union _) : Ensemble_scope.
Infix "∩" := (Intersection _) : Ensemble_scope.
Infix "\" := (Setminus _) : Ensemble_scope.
Infix "≅" := (Same_set _) : Ensemble_scope.
Notation "x ∈ S" := (In _ S x) : Ensemble_scope.
Notation "{{ x }}" := (Singleton _ x) : Ensemble_scope.
Notation "∅" := (Empty_set _) : Ensemble_scope.
