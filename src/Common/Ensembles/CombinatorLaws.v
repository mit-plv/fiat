Require Import ADTSynthesis.Common.Ensembles.Notations.
Require Import ADTSynthesis.Common.Ensembles.Tactics.

Local Open Scope Ensemble_scope.

Lemma Same_set_Intersection_Union {A} (x y z : Ensemble A)
: (x ∩ (y ∪ z)) ≅ (x ∩ y) ∪ (x ∩ z).
Proof. Ensemble_mor_t. Qed.

Lemma Same_set_Union_Intersection {A} (x y z : Ensemble A)
: (x ∪ (y ∩ z)) ≅ (x ∪ y) ∩ (x ∪ z).
Proof. Ensemble_mor_t. Qed.

Lemma Union_assoc {A} (x y z : Ensemble A)
: (x ∪ (y ∪ z)) ≅ ((x ∪ y) ∪ z).
Proof. Ensemble_mor_t. Qed.

Lemma Union_sym {A} (x y : Ensemble A)
: (x ∪ y) ≅ (y ∪ x).
Proof. Ensemble_mor_t. Qed.

Lemma Intersection_sym {A} (x y : Ensemble A)
: (x ∩ y) ≅ (y ∩ x).
Proof. Ensemble_mor_t. Qed.

Lemma Same_set_Intersection_Union' {A} (x y z : Ensemble A)
: ((y ∪ z) ∩ x) ≅ (y ∩ x) ∪ (z ∩ x).
Proof. Ensemble_mor_t. Qed.

Lemma Same_set_Union_Intersection' {A} (x y z : Ensemble A)
: ((y ∩ z) ∪ x) ≅ (y ∪ x) ∩ (z ∪ x).
Proof. Ensemble_mor_t. Qed.
