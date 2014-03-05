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

Global Instance refineADT_PreOrder : PreOrder refineADT.
Proof.
  split; compute in *.
  - intro x; destruct x.
    econstructor 1 with
    (SiR := @eq Rep)
      (mutatorMap := @id MutatorIndex)
      (observerMap := @id ObserverIndex)
      (B := {| Rep := Rep |});
      unfold id;
      try reflexivity.
  - intros x y z H H'.
    destruct H.
    destruct H'; simpl in *.
    econstructor 1 with
      (SiR := fun x z => exists y, SiR x y /\ SiR0 y z)
        (mutatorMap := mutatorMap0 ∘ mutatorMap)
        (observerMap := observerMap0 ∘ observerMap);
    unfold id, compose; simpl in *; intros.
    + destruct_ex; intuition; rewrite <- H1; eauto.
      unfold MutatorMethods, UnbundledMutatorMethods in H.
      etransitivity;
        [ idtac
        | eapply (@refineBundled_bind
                    (ADTLookupContext {| Rep := repA |})
                    (ADTLookupContext {| Rep := repA0 |})); eapply_hyp;
          intros; refineBundledEquiv_reflexivity_ignore_context].
      etransitivity;
        [idtac
        | eapply refineBundledEquiv_bind_bind].
      eapply (@refineBundledEquiv_under_bind
              (ADTLookupContext {| Rep := repA |})).
      constructor; unfold refine; intros.
      apply computes_to_inv in H3; simpl in *; destruct_ex; intuition.
      repeat econstructor; eauto.
      apply computes_to_inv in H3; simpl in *; destruct_ex; intuition.
      apply computes_to_inv in H6; apply computes_to_inv in H7.
      repeat econstructor; eauto.
    + destruct_ex; intuition; rewrite <- H2; eauto.
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
        mutIdx obsIdx
        mutDom obsDom obsCod
        (oldMuts : forall idx : mutIdx,
                     mutatorMethodTypeUnbundled oldRep (mutDom idx) mutDom obsDom obsCod)
        (newMuts : forall idx : mutIdx,
                     mutatorMethodTypeUnbundled newRep (mutDom idx) mutDom obsDom obsCod)
        (oldObs : forall idx : obsIdx,
                    observerMethodTypeUnbundled oldRep (obsDom idx) (obsCod idx) mutDom obsDom obsCod)
        (newObs : forall idx : obsIdx,
                    observerMethodTypeUnbundled newRep (obsDom idx) (obsCod idx) mutDom obsDom obsCod)
: (forall mutIdx,
     @refineMutator oldRep newRep BiR (mutDom mutIdx)
                    (MutatorMethods
                       {| Rep := oldRep;
                          UnbundledMutatorMethods := oldMuts;
                          UnbundledObserverMethods := oldObs |} mutIdx)
                    (MutatorMethods
                       {| Rep := newRep;
                          UnbundledMutatorMethods := newMuts;
                          UnbundledObserverMethods := newObs |} mutIdx))
  -> (forall obsIdx,
     @refineObserver oldRep newRep BiR (obsDom obsIdx) (obsCod obsIdx)
                    (ObserverMethods
                       {| Rep := oldRep;
                          UnbundledMutatorMethods := oldMuts;
                          UnbundledObserverMethods := oldObs |} obsIdx)
                    (ObserverMethods
                       {| Rep := newRep;
                          UnbundledMutatorMethods := newMuts;
                          UnbundledObserverMethods := newObs |} obsIdx))
  -> refineADT (@Build_ADT oldRep mutIdx obsIdx mutDom obsDom obsCod oldMuts oldObs)
               (@Build_ADT newRep mutIdx obsIdx mutDom obsDom obsCod newMuts newObs).
Proof.
  intros; let A := match goal with |- refineADT ?A ?B => constr:(A) end in
          let B := match goal with |- refineADT ?A ?B => constr:(B) end in
          eapply (@refinesADT (Rep A) _ _ B id id _ _ BiR); eauto.
Qed.

(* Carrying computation contexts around breaks down the Morphism structure of
  most of our common refinements.

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
Qed. *)
