Require Import FiatToFacade.Superset.
Require Import Facade.Facade.
Require Import Coq.Classes.Morphisms Setoid.
Require Import StringMap.

Ltac rewrite_Eq_in_all :=
  repeat match goal with
           | [ H: StringMap.Equal _ _, H': _ |- _ ] =>
             progress (try setoid_rewrite H in H';
                       try setoid_rewrite H)
           | [ H: pointwise_relation _ _ _ _, H': _ |- _ ] =>
             progress (try setoid_rewrite H in H';
                       try setoid_rewrite H)
           | [ H: _ _ _, H': _ |- _ ] =>
             progress (try setoid_rewrite H in H';
                       try setoid_rewrite H)
         end.

Add Parametric Morphism elt welt :
  (@Superset elt welt)
    with signature (StringMap.Equal ==> StringMap.Equal ==> pointwise_relation _ (@eq _) ==> iff)
      as Superset_morphism.
  unfold Superset; intros; rewrite_Eq_in_all; reflexivity.
Qed. 
  
Add Parametric Morphism {av} :
  (@SomeSCAs av)
    with signature (StringMap.Equal ==> StringMap.Equal ==> iff)
      as SomeSCAs_morphism.
Proof.
  unfold SomeSCAs; intros; apply Superset_morphism; intuition.
Qed.

Add Parametric Morphism {av} :
  (@AllADTs av)
    with signature (StringMap.Equal ==> StringMap.Equal ==> iff)
      as AllADTs_morphism.
Proof.
  unfold AllADTs; intros * eq1 * eq2.
  split; intros (? & ?); split;
  rewrite !eq1, !eq2 in *; assumption.
Qed.

Add Parametric Relation {elt welt wrapper} : (StringMap.t welt) (fun a b => @Superset elt welt a b wrapper)
    reflexivity proved by _
    transitivity proved by _
as superset.
Proof.
  firstorder.
  firstorder.
Qed.

(* Uh? *)
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.

Add Parametric Relation {av} : (Facade.State av) (@SomeSCAs av)
    reflexivity proved by _
    transitivity proved by _
as some_scas.
Proof.
  firstorder.
Qed.

(* Uh? *)
Proof.
firstorder.
Qed.

Add Parametric Relation {av} : (State av) (@AllADTs av)
    reflexivity proved by _
    symmetry proved by _                             
    transitivity proved by _
as all_adts.
Proof.
  firstorder.
  firstorder.
  firstorder.
Qed.

(* Uh? *)
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.
Proof.
  firstorder.
Qed.

Add Parametric Morphism av :
  (@AllADTs av)
    with signature (@AllADTs av ==> @AllADTs av ==> iff)
      as AllADTs_AllADTs_morphism.
  firstorder.
Qed.

Add Parametric Morphism {av k v} :
  (StringMap.add k v)
    with signature (@AllADTs av ==> @AllADTs av)
      as StringMap_add_AllADTs.
Proof.
  unfold AllADTs, Superset; intros; split; intros;
  generalize H0; StringMapFacts.map_iff; intuition.
Qed.

Add Parametric Morphism {av k} :
  (StringMap.remove k)
    with signature (@AllADTs av ==> @AllADTs av)
      as StringMap_remove_AllADTs.
Proof.
  unfold AllADTs, Superset; intros; split; intros;
  generalize H0; StringMapFacts.map_iff; intuition.
Qed.
