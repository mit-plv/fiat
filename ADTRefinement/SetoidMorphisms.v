Require Import Common Computation ADT Ensembles.
Require Export ADTRefinement.Core.

Generalizable All Variables.
Set Implicit Arguments.

Instance refineMutator_refl rep
: Reflexive (@refineMutator rep rep eq).
Proof.
  intro; simpl; intros; subst; econstructor; eauto.
Qed.

Instance refineObserver_refl rep
: Reflexive (@refineObserver rep rep eq).
Proof.
  intro; simpl; intros; subst; reflexivity.
Qed.

Global Instance refineADT_PreOrder : PreOrder refineADT.
Proof.
  split; compute in *.
  - intro x.
    econstructor 1 with
    (BiR := eq)
      (mutatorMap := id)
      (observerMap := id);
      unfold id;
      try reflexivity.
  - intros x y z
           [BiR mutMap obsMap mutH obsH]
           [BiR' mutMap' obsMap' mutH' obsH'].
    econstructor 1 with
      (BiR := fun x z => exists y, BiR x y /\ BiR' y z)
        (mutatorMap := mutMap' ∘ mutMap)
        (observerMap := obsMap' ∘ obsMap);
    unfold id, compose; simpl in *; intros.
    + destruct_ex; intuition.
      rewrite <- mutH', <- mutH; eauto.
      intros r_n' Comp_n'; inversion_by computes_to_inv.
      econstructor; eauto.
    + destruct_ex; intuition; rewrite obsH, obsH'; eauto; reflexivity.
Qed.

Add Parametric Relation : ADT refineADT
    reflexivity proved by reflexivity
    transitivity proved by transitivity
      as refineADT_rel.

  (* Refining the representation type is a valid refinement,
     as long as the new methods are valid refinements.

   If we had dependent setoid relations in [Type], then we could write

<<
Add Parametric Morphism : @Build_ADT
  with signature
  (fun oldM newM => newM -> Comp oldM)
    ==> arrow
    ==> arrow
    ==> (pointwise_relation _ (@refineMutator _ _ _))
    ==> (pointwise_relation _ (@refineObserver _ _ _))
    ==> refineADT
    as refineADT_Build_ADT.
Proof.
  ...
Qed.
>>

    But, alas, Matthieu is still working on those.  So the rewrite
    machinery won't work very well when we're switching reps, and
    we'll instead have to use [etransitivity] and [apply] the
    [refineADT_Build_ADT_Rep] lemma to switch representations.

    The statement of [refineADT_Build_ADT_Rep] mimics the notation for
    registering [Parametric Morphism]s so that it will be easy to
    integrate if dependent setoid relations are added.

 **)

Lemma refineADT_Build_ADT_Rep oldRep newRep
      (BiR : oldRep -> newRep -> Prop)
      mutIdx obsIdx :
  (respectful_hetero
     (mutIdx -> mutatorMethodType oldRep)
     (mutIdx -> mutatorMethodType newRep)
     (fun oldMuts => (obsIdx -> observerMethodType oldRep) -> ADT)
     (fun newMuts => (obsIdx -> observerMethodType newRep) -> ADT)
     (fun oldMuts newMuts =>
        forall mutIdx,
          @refineMutator oldRep newRep BiR
                         (oldMuts mutIdx)
                         (newMuts mutIdx))
     (fun x y => respectful_hetero
                   (obsIdx -> observerMethodType oldRep)
                   (obsIdx -> observerMethodType newRep)
                   (fun _ => ADT)
                   (fun _ => ADT)
                   (fun obs obs' =>
                      forall obsIdx,
                        @refineObserver oldRep newRep BiR
                                        (obs obsIdx)
                                        (obs' obsIdx))
                   (fun obs obs' => refineADT)))
    (@Build_ADT oldRep mutIdx obsIdx)
    (@Build_ADT newRep mutIdx obsIdx).
Proof.
  unfold Proper, respectful_hetero; intros.
  let A := match goal with |- refineADT ?A ?B => constr:(A) end in
  let B := match goal with |- refineADT ?A ?B => constr:(B) end in
  eapply (@refinesADT A B BiR id id);
    unfold id, pointwise_relation in *; simpl in *; intros; eauto.
Qed.

(* Thankfully, we can register a number of different refinements
     which follow from [refineADT_Build_ADT_Rep] as [Parametric Morphism]s.*)

(* Refining Observers is a valid ADT refinement. *)
Add Parametric Morphism rep mutIdx obsIdx ms
: (fun os => @Build_ADT rep mutIdx obsIdx ms os)
    with signature
    (pointwise_relation _ (@refineObserver _ _ eq))
      ==> refineADT
      as refineADT_Build_ADT_Observer.
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
Qed.

(* Refining Mutators is also a valid ADT refinement. *)

Add Parametric Morphism rep mutIdx obsIdx obs
: (fun ms => @Build_ADT rep mutIdx obsIdx ms obs)
    with signature
    (pointwise_relation _ (@refineMutator _ _ eq))
      ==> refineADT
      as refineADT_Build_ADT_Mutators.
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
Qed.

(* Refining observers and mutators at the same time is also a valid
   refinement. [BD: I've come to the conclusion that smaller refinement
   steps are better, so using the previous refinements should be the
   preferred mode. ]*)

Add Parametric Morphism rep mutIdx obsIdx
: (fun ms os => @Build_ADT rep mutIdx obsIdx ms os)
    with signature
    (pointwise_relation _ (@refineMutator _ _ eq))
      ==> (pointwise_relation _ (@refineObserver _ _ eq))
      ==> refineADT
      as refineADT_Build_ADT_Both.
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
Qed.
