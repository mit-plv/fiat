Require Export Coq.Sets.Ensembles.
Require Import ADTSynthesis.Common.Ensembles.Equivalence.
Require Import ADTSynthesis.Common.Ensembles.Tactics.
Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.
Require Import ADTSynthesis.Common.

Global Add Parametric Relation {T} : _ (@Same_set T)
    reflexivity proved by reflexivity
    symmetry proved by symmetry
    transitivity proved by transitivity
      as Same_set_rel.

Global Add Parametric Relation {T} : _ (@Included T)
    reflexivity proved by reflexivity
    transitivity proved by transitivity
      as Included_rel.

Add Parametric Morphism {T} : (@Union T)
    with signature eq ==> Included T ==> Included T
      as Union_Included2_mor.
Proof. Ensemble_mor_t. Qed.

Add Parametric Morphism {T} : (@Union T)
    with signature Included T ==> eq ==> Included T
      as Union_Included1_mor.
Proof. Ensemble_mor_t. Qed.

Add Parametric Morphism {T} : (@Union T)
    with signature Same_set T ==> eq ==> Same_set T
      as Union_Same_set1_mor.
Proof. Ensemble_mor_t. Qed.

Add Parametric Morphism {T} : (@Union T)
    with signature eq ==> Same_set T ==> Same_set T
      as Union_Same_set2_mor.
Proof. Ensemble_mor_t. Qed.



Add Parametric Morphism {T} : (@Intersection T)
    with signature eq ==> Included T ==> Included T
      as Intersection_Included2_mor.
Proof. Ensemble_mor_t. Qed.

Add Parametric Morphism {T} : (@Intersection T)
    with signature Included T ==> eq ==> Included T
      as Intersection_Included1_mor.
Proof. Ensemble_mor_t. Qed.

Add Parametric Morphism {T} : (@Intersection T)
    with signature Same_set T ==> eq ==> Same_set T
      as Intersection_Same_set1_mor.
Proof. Ensemble_mor_t. Qed.

Add Parametric Morphism {T} : (@Intersection T)
    with signature eq ==> Same_set T ==> Same_set T
      as Intersection_Same_set2_mor.
Proof. Ensemble_mor_t. Qed.
