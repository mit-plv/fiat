Require Import Common Computation ADT Ensembles.
Require Export ADTRefinement.Core.

(** Definitions for integrating [refineADT] into the setoid rewriting
    framework. *)

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

Global Instance refineADT_PreOrder Sig : PreOrderT (refineADT (Sig := Sig)).
Proof.
  split; compute in *.
  - intro x; destruct x.
    econstructor 1 with
    (SiR := @eq Rep);
      try reflexivity.
  - intros x y z H H'.
    destruct H as [SiR ? ?].
    destruct H' as [SiR' ? ?]; simpl in *.
    econstructor 1 with
      (SiR := fun x z => exists y, SiR x y /\ SiR' y z);
      simpl in *; intros.
    + destruct_ex; intuition; rewrite_rev_hyp; eauto.
      autorewrite with refine_monad; f_equiv; unfold pointwise_relation;
      intros; econstructor; inversion_by computes_to_inv;
      eauto.
    + destruct_ex; intuition; rewrite_rev_hyp; eauto; reflexivity.
Qed.

(*Add Parametric Relation Sig : (ADT Sig) refineADT
    reflexivity proved by reflexivity
    transitivity proved by transitivity
      as refineADT_rel.*)

(** Refining the representation type is a valid refinement, as long as
    the new methods are valid refinements.

    If we had dependent setoid relations in [Type], then we could
    write

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

 *)

Lemma refineADT_Build_ADT_Rep Sig oldRep newRep
      (SiR : oldRep -> newRep -> Prop)
:
  (@respectful_heteroT
     (forall idx, mutatorMethodType oldRep (MutatorDom Sig idx))
     (forall idx, mutatorMethodType newRep (MutatorDom Sig idx))
     (fun oldMuts =>
        (forall idx,
           observerMethodType oldRep (fst (ObserverDomCod Sig idx)) (snd (ObserverDomCod Sig idx)))
        -> ADT Sig)
     (fun newMuts =>
        (forall idx,
           observerMethodType newRep (fst (ObserverDomCod Sig idx)) (snd (ObserverDomCod Sig idx)))
        -> ADT Sig)
     (fun oldMuts newMuts =>
        forall mutIdx,
          @refineMutator oldRep newRep SiR
                         _
                         (oldMuts mutIdx)
                         (newMuts mutIdx))
     (fun x y => @respectful_heteroT
                   (forall idx, observerMethodType oldRep _ _)
                   (forall idx, observerMethodType newRep _ _)
                   (fun _ => ADT Sig)
                   (fun _ => ADT Sig)
                   (fun obs obs' =>
                      forall obsIdx : ObserverIndex Sig,
                        @refineObserver oldRep newRep SiR
                                        (fst (ObserverDomCod Sig obsIdx))
                                        (snd (ObserverDomCod Sig obsIdx))
                                        (obs obsIdx)
                                        (obs' obsIdx))
                   (fun obs obs' => refineADT)))
    (@Build_ADT Sig oldRep)
    (@Build_ADT Sig newRep).
Proof.
  unfold Proper, respectful_heteroT; intros.
  let A := match goal with |- refineADT ?A ?B => constr:(A) end in
  let B := match goal with |- refineADT ?A ?B => constr:(B) end in
  eapply (@refinesADT Sig A B SiR);
    unfold id, pointwise_relation in *; simpl in *; intros; eauto.
Qed.

(** Thankfully, we can register a number of different refinements
    which follow from [refineADT_Build_ADT_Rep] as [Parametric
    Morphism]s... or we could, if [refineADT] were in [Prop]. *)

(** Refining Observers is a valid ADT refinement. *)

Lemma refineADT_Build_ADT_Observer' rep Sig ms
: forall obs obs',
    (forall idx, @refineObserver _ _ eq
                                 (fst (ObserverDomCod Sig idx))
                                 (snd (ObserverDomCod Sig idx))
                                 (obs idx) (obs' idx))
    -> refineADT (@Build_ADT Sig rep ms obs) (@Build_ADT Sig rep ms obs').
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
Qed.

Definition refineADT_Build_ADT_Observer := refineADT_Build_ADT_Observer'.

(*Add Parametric Morphism rep Sig ms
: (@Build_ADT Sig rep ms)
    with signature
    (fun obs obs' =>
       forall idx, @refineObserver _ _ eq
                                   (fst (ObserverDomCod Sig idx))
                                   (snd (ObserverDomCod Sig idx))
                                   (obs idx) (obs' idx))
      ==> refineADT
      as refineADT_Build_ADT_Observer.
Proof.
  apply refineADT_Build_ADT_Observer'.
Qed.*)

(** Refining Mutators is also a valid ADT refinement. *)

Lemma refineADT_Build_ADT_Mutators' rep Sig obs
: forall mut mut',
    (forall idx, @refineMutator _ _ eq
                                (MutatorDom Sig idx)
                                (mut idx) (mut' idx))
    -> refineADT (@Build_ADT Sig rep mut obs) (@Build_ADT Sig rep mut' obs).
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
Qed.

Definition refineADT_Build_ADT_Mutators := refineADT_Build_ADT_Mutators'.
(*Add Parametric Morphism rep Sig obs
: (fun ms => @Build_ADT Sig rep ms obs)
    with signature
    (fun mut mut' =>
       forall idx, @refineMutator _ _ eq
                                   (MutatorDom Sig idx)
                                   (mut idx) (mut' idx))
      ==> refineADT
      as refineADT_Build_ADT_Mutators.
Proof.
  apply refineADT_Build_ADT_Mutators'.
Qed.*)

(** Refining observers and mutators at the same time is also a valid
    refinement. [BD: I've come to the conclusion that smaller
    refinement steps are better, so using the previous refinements
    should be the preferred mode. ]*)

Lemma refineADT_Build_ADT_Both' rep Sig
: forall obs obs',
    (forall idx, @refineObserver _ _ eq
                                 (fst (ObserverDomCod Sig idx))
                                 (snd (ObserverDomCod Sig idx))
                                 (obs idx) (obs' idx))
    -> forall mut mut',
         (forall idx, @refineMutator _ _ eq
                                     (MutatorDom Sig idx)
                                     (mut idx) (mut' idx))
         -> refineADT (@Build_ADT Sig rep mut obs) (@Build_ADT Sig rep mut' obs').
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
Qed.

Definition refineADT_Build_ADT_Both := refineADT_Build_ADT_Both'.
(*Add Parametric Morphism Sig rep
: (@Build_ADT Sig rep)
    with signature
    (fun mut mut' =>
       forall idx, @refineMutator _ _ eq
                                   (MutatorDom Sig idx)
                                   (mut idx) (mut' idx))
      ==> (fun obs obs' =>
       forall idx, @refineObserver _ _ eq
                                   (fst (ObserverDomCod Sig idx))
                                   (snd (ObserverDomCod Sig idx))
                                   (obs idx) (obs' idx))
      ==> refineADT
      as refineADT_Build_ADT_Both.
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
Qed.*)
