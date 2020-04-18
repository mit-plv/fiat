Require Import Fiat.Common.Ensembles.Notations.
Require Import Fiat.Common.Ensembles.Tactics.
Require Import Fiat.Common.Ensembles.Morphisms.
Require Import Fiat.Common.

Local Open Scope Ensemble_scope.

Lemma Same_set_Intersection_Union {A} (x y z : Ensemble A)
: (x ∩ (y ∪ z)) ≅ (x ∩ y) ∪ (x ∩ z).
Proof. Ensembles_t. Qed.

Lemma Same_set_Union_Intersection {A} (x y z : Ensemble A)
: (x ∪ (y ∩ z)) ≅ (x ∪ y) ∩ (x ∪ z).
Proof. Ensembles_t. Qed.

Lemma Union_assoc {A} (x y z : Ensemble A)
: (x ∪ (y ∪ z)) ≅ ((x ∪ y) ∪ z).
Proof. Ensembles_t. Qed.

Lemma Union_sym {A} (x y : Ensemble A)
: (x ∪ y) ≅ (y ∪ x).
Proof. Ensembles_t. Qed.

Lemma Intersection_sym {A} (x y : Ensemble A)
: (x ∩ y) ≅ (y ∩ x).
Proof. Ensembles_t. Qed.

Lemma Same_set_Intersection_Union' {A} (x y z : Ensemble A)
: ((y ∪ z) ∩ x) ≅ (y ∩ x) ∪ (z ∩ x).
Proof. Ensembles_t. Qed.

Lemma Same_set_Union_Intersection' {A} (x y z : Ensemble A)
: ((y ∩ z) ∪ x) ≅ (y ∪ x) ∩ (z ∪ x).
Proof. Ensembles_t. Qed.

Lemma Intersection_Empty A S0
: Same_set A (Intersection A (fun _ : A => False) S0) (fun _ => False).
Proof. Ensembles_t. Qed.

Lemma Same_set__Intersection_Complement__Setminus {A} (S0 S1 : Ensemble A)
: Same_set _ (Intersection _ S0 (Complement _ S1)) (Setminus _ S0 S1).
Proof. Ensembles_t. Qed.

Lemma Same_set__Intersection_beq__Setminus {A} (S0 : Ensemble A) f (b : bool)
: Same_set _ (Intersection _ S0 (fun y => f y = b)) (Setminus _ S0 (fun y => f y = negb b)).
Proof. Ensembles_t. Qed.

Lemma Same_set__Intersection_bneq__Setminus {A} (S0 : Ensemble A) f (b : bool)
: Same_set _ (Intersection _ S0 (fun y => ~f y = b)) (Setminus _ S0 (fun y => f y = b)).
Proof. Ensembles_t. Qed.

Lemma Same_set__Intersection_bnneq__Setminus {A} (S0 : Ensemble A) f (b : bool)
: Same_set _ (Intersection _ S0 (fun y => ~~f y = b)) (Setminus _ S0 (fun y => f y = negb b)).
Proof. Ensembles_t. Qed.
