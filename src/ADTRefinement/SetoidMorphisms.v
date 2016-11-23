Require Import Fiat.Common Fiat.Computation Coq.Sets.Ensembles.
Require Import Fiat.ADT.ADTSig Fiat.ADT.Core Fiat.ADTRefinement.Core.

(** Definitions for integrating [refineADT] into the setoid rewriting
    framework. *)

Instance refineConstructor_refl rep Dom
: Reflexive (@refineConstructor rep rep eq Dom).
Proof.
  induction Dom; simpl.
  - intro; simpl; intros; subst; computes_to_econstructor; eauto.
  - intro; simpl; intros; subst; apply IHDom.
Qed.

Instance refineMethod_refl arity rep Dom Cod
: Reflexive (@refineMethod rep rep eq arity Dom Cod).
Proof.
  revert rep Dom Cod.
  induction arity.
  - unfold refineMethod, methodType; intro; simpl; intros; subst;
      induction Dom; simpl.
    + destruct Cod; intro; simpl; intros; subst;
        repeat computes_to_econstructor; try destruct v; eauto.
    + intro; simpl; intros; subst; apply IHDom.
  - intros; simpl; intro; intros; subst; eapply IHarity.
Qed.

Lemma refineConstructor_trans
      rep rep' rep'' Dom
      AbsR AbsR'
  : forall c c' c'',
    @refineConstructor rep rep' AbsR Dom c c'
    -> @refineConstructor rep' rep'' AbsR' Dom c' c''
    -> refineConstructor
         (fun r_o r_n => exists r_o', AbsR r_o r_o' /\ AbsR' r_o' r_n)
         c c''.
Proof.
  induction Dom.
  - intro; simpl; intros; subst; intros v Comp_v.
    apply H0 in Comp_v; computes_to_inv; subst.
    apply H in Comp_v; computes_to_inv; subst; eauto.
  - simpl; intros; eapply IHDom; simpl in *.
    apply H.
    eapply H0.
Qed.

Lemma refineConstructor_eq_trans
      rep rep' Dom
      AbsR
  : forall c c' c'',
    @refineConstructor rep rep' AbsR Dom c c'
    -> @refineConstructor_eq rep' Dom c' c''
    -> refineConstructor AbsR c c''.
Proof.
  induction Dom.
  - intro; simpl; intros; subst; intros v Comp_v.
    apply H0 in Comp_v; computes_to_inv; subst.
    apply H in Comp_v; computes_to_inv; subst; eauto.
  - simpl; intros; eapply IHDom; simpl in *.
    apply H.
    eapply H0.
Qed.

Instance refineConstructor_trans' rep Dom
: Transitive (@refineConstructor rep rep eq Dom).
Proof.
  induction Dom.
  - intro; intros.
    pose proof (refineConstructor_trans nil eq eq x y z H H0);
      unfold refineConstructor, refine; intros.
    eapply H1 in H2; computes_to_inv; subst.
    destruct_ex; intuition; subst; eauto.
  - simpl; intro; intros.
    eapply IHDom.
    apply H.
    apply H0.
Qed.

Lemma refineMethod_trans arity rep rep' rep'' Dom Cod
      AbsR AbsR'
  : forall m m' m'',
    @refineMethod rep rep' AbsR arity Dom Cod m m'
    -> @refineMethod rep' rep'' AbsR' arity Dom Cod m' m''
    -> refineMethod (fun r_o r_n => exists r_o', AbsR r_o r_o' /\ AbsR' r_o' r_n)
                    arity m m''.
Proof.
  induction arity.
  - unfold refineMethod, methodType; induction Dom.
    + intro; simpl; intros; destruct Cod; subst; intros v Comp_v.
      * destruct_ex; intuition.
        eapply H0 in Comp_v; eauto; computes_to_inv; subst.
        eapply H in Comp_v; eauto; computes_to_inv; subst; eauto.
        repeat computes_to_econstructor; eauto.
      * destruct_ex; intuition.
        eapply H0 in Comp_v; eauto; computes_to_inv; subst.
        eapply H in Comp_v; eauto; computes_to_inv; subst; eauto.
    + simpl; intros.
      destruct_ex; intuition.
      eapply (IHDom (m d)
                    (m' d)
                    (m'' d)); eauto.
  - simpl; intros; destruct_ex; intuition; eapply IHarity; eauto.
Qed.

Lemma refineMethod_eq_trans arity rep rep' Dom Cod
      AbsR
  : forall m m' m'',
    @refineMethod rep rep' AbsR arity Dom Cod m m'
    -> @refineMethod_eq rep' arity Dom Cod m' m''
    -> refineMethod AbsR arity m m''.
Proof.
  induction arity.
  - unfold refineMethod, methodType; induction Dom.
    + intro; simpl; intros; destruct Cod; subst; intros v Comp_v.
      * destruct_ex; intuition.
      * destruct_ex; intuition.
    + simpl; intros.
      eapply IHDom.
      eapply H.
      eapply H0.
  - simpl; intros; eauto.
Qed.

Lemma refineMethod_eq_trans' arity rep rep' Dom Cod
      AbsR
  : forall m m' m'',
    @refineMethod_eq rep arity Dom Cod m m'
    -> @refineMethod rep rep' AbsR arity Dom Cod m' m''
    -> refineMethod AbsR arity m m''.
Proof.
  induction arity.
  - unfold refineMethod, methodType; induction Dom.
    + intro; simpl; intros; destruct Cod; subst; intros v Comp_v.
      * apply H0 in Comp_v; computes_to_inv; subst;
          repeat computes_to_econstructor; eauto.
      * apply H0 in Comp_v; computes_to_inv; subst;
          repeat computes_to_econstructor; eauto.
    + simpl; intros.
      eapply IHDom.
      eapply H.
      eapply H0.
  - simpl; intros; eauto.
Qed.

Instance refineMethod_trans' arity rep Dom Cod
: Transitive (@refineMethod rep rep eq arity Dom Cod).
Proof.
  induction arity.
  - unfold refineMethod, methodType; subst; induction Dom.
    + intro; intros.
      pose proof (refineMethod_trans 0 _ _ _ _ _ _ _ H H0);
        unfold refineMethod, refineMethod', refine in *; destruct Cod; intros; subst.
       * eapply H1 in H2; eauto; computes_to_inv; subst.
         destruct_ex; intuition; subst; eauto.
       * eapply H1 in H2; eauto; computes_to_inv; subst.
         destruct_ex; intuition; subst; eauto.
    +  intro; simpl; intros; subst.
       eapply IHDom; eauto.
  - simpl; unfold Transitive in *; intros.
    eapply IHarity; eauto.
Qed.

Global Instance refineADT_PreOrder Sig : PreOrderT (refineADT (Sig := Sig)).
Proof.
  split; compute in *.
  - intro x; destruct x.
    econstructor 1 with
    (AbsR := @eq Rep);
      try reflexivity.
  - intros x y z H H'.
    destruct H as [AbsR ? ?].
    destruct H' as [AbsR' ? ?].
    econstructor 1 with
      (AbsR := fun x z => exists y, AbsR x y /\ AbsR' y z);
      simpl in *; intros.
    + eauto using refineMethod_trans.
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
      (AbsR : oldRep -> newRep -> Prop)
:
  @respectful_heteroT
    (forall idx, methodType _ oldRep _ _)
    (forall idx, methodType _ newRep _ _)
    (fun _ => ADT Sig)
    (fun _ => ADT Sig)
    (fun obs obs' =>
       forall obsIdx : MethodIndex Sig,
         @refineMethod oldRep newRep AbsR
                       (fst (fst (MethodDomCod Sig obsIdx)))
                       (snd (fst (MethodDomCod Sig obsIdx)))
                       (snd (MethodDomCod Sig obsIdx))
                       (obs obsIdx)
                       (obs' obsIdx))
    (fun obs obs' => refineADT)
    (@Build_ADT Sig oldRep)
    (@Build_ADT Sig newRep).
Proof.
  unfold Proper, respectful_heteroT; intros.
  let A := match goal with |- refineADT ?A ?B => constr:(A) end in
  let B := match goal with |- refineADT ?A ?B => constr:(B) end in
  eapply (@refinesADT Sig A B AbsR);
    unfold id, pointwise_relation in *; simpl in *; intros; eauto.
Qed.

(** Thankfully, we can register a number of different refinements
    which follow from [refineADT_Build_ADT_Rep] as [Parametric
    Morphism]s... or we could, if [refineADT] were in [Prop]. *)

(** Refining Methods is a valid ADT refinement. *)

Lemma refineADT_Build_ADT_Method rep Sig
: forall ms ms',
    (forall idx, @refineMethod _ _ eq
                               (fst (fst (MethodDomCod Sig idx)))
                               (snd (fst (MethodDomCod Sig idx)))
                               (snd (MethodDomCod Sig idx))
                               (ms idx) (ms' idx))
    -> refineADT (@Build_ADT Sig rep ms) (@Build_ADT Sig rep ms').
Proof.
  intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
Qed.

(* If [refineADT] lived in [Prop], we'd be able to register
   refineADT_Build_ADT_Method as a morphism. *)
