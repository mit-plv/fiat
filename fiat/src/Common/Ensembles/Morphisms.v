Require Export Coq.Sets.Ensembles.
Require Import Fiat.Common.Ensembles.Equivalence.
Require Import Fiat.Common.Ensembles.Tactics.
Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.
Require Import Fiat.Common.

Add Parametric Morphism {T} : (@Union T)
    with signature eq ==> Included T ==> Included T
      as Union_Included2_mor.
Proof. Ensembles_t. Qed.

Add Parametric Morphism {T} : (@Union T)
    with signature Included T ==> eq ==> Included T
      as Union_Included1_mor.
Proof. Ensembles_t. Qed.

Add Parametric Morphism {T} : (@Union T)
    with signature Same_set T ==> eq ==> Same_set T
      as Union_Same_set1_mor.
Proof. Ensembles_t. Qed.

Add Parametric Morphism {T} : (@Union T)
    with signature eq ==> Same_set T ==> Same_set T
      as Union_Same_set2_mor.
Proof. Ensembles_t. Qed.



Add Parametric Morphism {T} : (@Intersection T)
    with signature eq ==> Included T ==> Included T
      as Intersection_Included2_mor.
Proof. Ensembles_t. Qed.

Add Parametric Morphism {T} : (@Intersection T)
    with signature Included T ==> eq ==> Included T
      as Intersection_Included1_mor.
Proof. Ensembles_t. Qed.

Add Parametric Morphism {T} : (@Intersection T)
    with signature Same_set T ==> eq ==> Same_set T
      as Intersection_Same_set1_mor.
Proof. Ensembles_t. Qed.

Add Parametric Morphism {T} : (@Intersection T)
    with signature eq ==> Same_set T ==> Same_set T
      as Intersection_Same_set2_mor.
Proof. Ensembles_t. Qed.
