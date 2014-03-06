Require Import Common Computation ADT Ensembles.
Require Export ADTRefinement.Core.

Generalizable All Variables.
Set Implicit Arguments.

Instance refineMutator_refl rep Dom
: Reflexive (@refineMutator rep rep eq Dom).
Proof.
  intro; simpl; intros; subst; econstructor; eauto.
Qed.

Instance refineObserver_refl rep Dom Cod
: Reflexive (@refineObserver rep rep eq Dom Cod).
Proof.
  intro; simpl; intros; subst; reflexivity.
Qed.

Global Instance refineADT_PreOrder Sig : PreOrder (refineADT (Sig := Sig)).
Proof.
  split; compute in *.
  - intro x; destruct x.
    econstructor 1 with
    (SiR := @eq Rep);
      try reflexivity.
  - intros x y z H H'.
    destruct H.
    destruct H'; simpl in *.
    econstructor 1 with
      (SiR := fun x z => exists y, SiR x y /\ SiR0 y z);
      simpl in *; intros.
    + destruct_ex; intuition; rewrite <- H1, <- H; eauto.
      autorewrite with refine_monad; f_equiv; unfold pointwise_relation;
      intros; econstructor; inversion_by computes_to_inv;
      eauto.
    + destruct_ex; intuition; rewrite <- H2; eauto.
Qed.

Add Parametric Relation Sig : (ADT Sig) refineADT
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

Lemma refineADT_Build_ADT_Rep Sig oldRep newRep
      (SiR : oldRep -> newRep -> Prop)
:
   (respectful_hetero
      (forall idx, mutatorMethodType oldRep (MutatorDom Sig idx))
      (forall idx, mutatorMethodType newRep (MutatorDom Sig idx))
      (fun oldMuts =>
         (forall idx,
            observerMethodType oldRep (ObserverDom Sig idx) (ObserverCod Sig idx))
         -> ADT Sig)
      (fun newMuts =>
         (forall idx,
            observerMethodType newRep (ObserverDom Sig idx) (ObserverCod Sig idx))
         -> ADT Sig)
      (fun oldMuts newMuts =>
         forall mutIdx,
           @refineMutator oldRep newRep SiR
                          _
                          (oldMuts mutIdx)
                          (newMuts mutIdx))
      (fun x y => respectful_hetero
                    (forall idx, observerMethodType oldRep _ _)
                    (forall idx, observerMethodType newRep _ _)
                    (fun _ => ADT Sig)
                    (fun _ => ADT Sig)
                    (fun obs obs' =>
                       forall obsIdx : ObserverIndex Sig,
                         @refineObserver oldRep newRep SiR
                                         (ObserverDom Sig obsIdx)
                                         (ObserverCod Sig obsIdx)
                                        (obs obsIdx)
                                        (obs' obsIdx))
                    (fun obs obs' => refineADT)))
     (@Build_ADT Sig oldRep)
     (@Build_ADT Sig newRep).
 Proof.
   unfold Proper, respectful_hetero; intros.
   let A := match goal with |- refineADT ?A ?B => constr:(A) end in
   let B := match goal with |- refineADT ?A ?B => constr:(B) end in
   eapply (@refinesADT Sig A B SiR);
     unfold id, pointwise_relation in *; simpl in *; intros; eauto.
 Qed.
 (* Thankfully, we can register a number of different refinements
    which follow from [refineADT_Build_ADT_Rep] as [Parametric Morphism]s. *)


(* Refining Observers is a valid ADT refinement. *)

 Print relation.
Add Parametric Morphism rep Sig ms
: (@Build_ADT Sig rep ms)
    with signature
    (fun obs obs' =>
       forall idx, @refineObserver _ _ eq
                                   (ObserverDom Sig idx)
                                   (ObserverCod Sig idx)
                                   (obs idx) (obs' idx))
      ==> refineADT
      as refineADT_Build_ADT_Observer.
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
Qed.

(* Refining Mutators is also a valid ADT refinement. *)

Add Parametric Morphism rep Sig obs
: (fun ms => @Build_ADT Sig rep ms obs)
    with signature
    (fun mut mut' =>
       forall idx, @refineMutator _ _ eq
                                   (MutatorDom Sig idx)
                                   (mut idx) (mut' idx))
      ==> refineADT
      as refineADT_Build_ADT_Mutators.
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
Qed.

(* Refining observers and mutators at the same time is also a valid
   refinement. [BD: I've come to the conclusion that smaller refinement
   steps are better, so using the previous refinements should be the
   preferred mode. ]*)

Add Parametric Morphism Sig rep
: (@Build_ADT Sig rep)
    with signature
    (fun mut mut' =>
       forall idx, @refineMutator _ _ eq
                                   (MutatorDom Sig idx)
                                   (mut idx) (mut' idx))
      ==> (fun obs obs' =>
       forall idx, @refineObserver _ _ eq
                                   (ObserverDom Sig idx)
                                   (ObserverCod Sig idx)
                                   (obs idx) (obs' idx))
      ==> refineADT
      as refineADT_Build_ADT_Both.
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
Qed.
