Require Import Common Computation Ensembles.
Require Import ADT.ADTSig ADT.Core ADTRefinement.Core.

(** Definitions for integrating [refineADT] into the setoid rewriting
    framework. *)

Instance refineConstructor_refl rep Dom
: Reflexive (@refineConstructor rep rep eq Dom).
Proof.
  intro; simpl; intros; subst; econstructor; eauto.
Qed.

Instance refineMethod_refl rep Dom Cod
: Reflexive (@refineMethod rep rep eq Dom Cod).
Proof.
  intro; simpl; unfold refine; intros; subst;
  repeat econstructor; try destruct v; eauto.
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
    + destruct_ex; intuition; rewrite_rev_hyp; eauto.
      autorewrite with refine_monad; f_equiv; unfold pointwise_relation.
      intros; rewrite refine_split_ex; autorewrite with refine_monad;
      f_equiv; unfold pointwise_relation; intros;
      autorewrite with refine_monad; simpl; f_equiv.
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
    ==> (pointwise_relation _ (@refineConstructor _ _ _))
    ==> (pointwise_relation _ (@refineMethod _ _ _))
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
     (forall idx, constructorType oldRep (ConstructorDom Sig idx))
     (forall idx, constructorType newRep (ConstructorDom Sig idx))
     (fun oldConstrs =>
        (forall idx,
           methodType oldRep (fst (MethodDomCod Sig idx)) (snd (MethodDomCod Sig idx)))
        -> ADT Sig)
     (fun newConstrs =>
        (forall idx,
           methodType newRep (fst (MethodDomCod Sig idx)) (snd (MethodDomCod Sig idx)))
        -> ADT Sig)
     (fun oldConstrs newConstrs =>
        forall mutIdx,
          @refineConstructor oldRep newRep SiR
                         _
                         (oldConstrs mutIdx)
                         (newConstrs mutIdx))
     (fun x y => @respectful_heteroT
                   (forall idx, methodType oldRep _ _)
                   (forall idx, methodType newRep _ _)
                   (fun _ => ADT Sig)
                   (fun _ => ADT Sig)
                   (fun obs obs' =>
                      forall obsIdx : MethodIndex Sig,
                        @refineMethod oldRep newRep SiR
                                        (fst (MethodDomCod Sig obsIdx))
                                        (snd (MethodDomCod Sig obsIdx))
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

(** Refining Methods is a valid ADT refinement. *)

Lemma refineADT_Build_ADT_Method rep Sig cs
: forall ms ms',
    (forall idx, @refineMethod _ _ eq
                                 (fst (MethodDomCod Sig idx))
                                 (snd (MethodDomCod Sig idx))
                                 (ms idx) (ms' idx))
    -> refineADT (@Build_ADT Sig rep cs ms) (@Build_ADT Sig rep cs ms').
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
Qed.

(** Refining Constructors is also a valid ADT refinement. *)

Lemma refineADT_Build_ADT_Constructors rep Sig ms
: forall cs cs',
    (forall idx, @refineConstructor _ _ eq
                                (ConstructorDom Sig idx)
                                (cs idx) (cs' idx))
    -> refineADT (@Build_ADT Sig rep cs ms) (@Build_ADT Sig rep cs' ms).
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
Qed.

(** Refining observers and mutators at the same time is also a valid
    refinement. [BD: I've come to the conclusion that smaller
    refinement steps are better, so using the previous refinements
    should be the preferred mode. ]*)

Lemma refineADT_Build_ADT_Both rep Sig
: forall ms ms',
    (forall idx, @refineMethod _ _ eq
                                 (fst (MethodDomCod Sig idx))
                                 (snd (MethodDomCod Sig idx))
                                 (ms idx) (ms' idx))
    -> forall cs cs',
         (forall idx, @refineConstructor _ _ eq
                                     (ConstructorDom Sig idx)
                                     (cs idx) (cs' idx))
         -> refineADT (@Build_ADT Sig rep cs ms) (@Build_ADT Sig rep cs' ms').
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
Qed.

(* If [refineADT] lived in [Prop], we'd be able to register
   refineADT_Build_ADT_Both as a morphism.

Add Parametric Morphism Sig rep
: (@Build_ADT Sig rep)
    with signature
    (fun mut mut' =>
       forall idx, @refineConstructor _ _ eq
                                   (ConstructorDom Sig idx)
                                   (mut idx) (mut' idx))
      ==> (fun obs obs' =>
       forall idx, @refineMethod _ _ eq
                                   (fst (MethodDomCod Sig idx))
                                   (snd (MethodDomCod Sig idx))
                                   (obs idx) (obs' idx))
      ==> refineADT
      as refineADT_Build_ADT_Both.
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
Qed.*)
