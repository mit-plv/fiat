Require Import Common Computation ADT Ensembles.
Require Export ADTRefinement.Core ADTRefinement.Specs ADTRefinement.Pick ADTRefinement.SetoidMorphisms.

Generalizable All Variables.
Set Implicit Arguments.

(* To derive an ADT interactively from a specification [spec], we can build a dependent
   product [ {adt | refineADT spec adt} ]. The derivation flow has the form:
   1. Apply a refinement.
   2. Discharge any side conditions.
   3. Repeat steps 1-2 until adt is completely specialized.

   My (Ben's) current thought is that to make this as pleasant as possible,
   the refinements used in the first step should be implemented using tactics
   which present the user with 'nice' side conditions. (In particular, this lets us
   be careful about not having any dangling existential variables at the end of a
   derivation).

   Aside on notation:
   When naming these tactics, I wanted one which wasn't already used by a tactic-
   refine, specialize, and replace were taken. The thesaurus suggested 'hone'.
   This kind of agrees with 'BedRock' (in as much as a WhetStone is used to sharpen
   knives), so I'm carrying on the naming convention with a 'Sharpened' notation
   for the dependent products. *)

Notation Sharpened spec := {adt | refineADT spec adt}.

(* A single refinement step. *)
Definition SharpenStep adt :
  forall adt',
    refineADT adt adt' ->
    Sharpened adt' ->
    Sharpened adt.
Proof.
  intros adt'za refineA SpecA';
  eexists (proj1_sig SpecA'); rewrite refineA; exact (proj2_sig SpecA').
Defined.

(* A tactic for finishing a derivation. Probably needs a better name.*)
Tactic Notation "finish" "sharpening" := eexists; reflexivity.

Section GeneralRefinements.
(* Given an abstraction function, we can transform the rep of a pickImpl ADT. *)

  Theorem refines_rep_pickImpl
          newRep oldRep
          (abs : newRep -> oldRep)
          MutatorIndex ObserverIndex
          ObserverSpec MutatorSpec :
    refineADT
      (@pickImpl oldRep MutatorIndex ObserverIndex MutatorSpec ObserverSpec)
      (@pickImpl newRep MutatorIndex ObserverIndex
                 (fun idx nm n nm' => MutatorSpec idx (abs nm) n (abs nm'))
                 (fun idx nm => ObserverSpec idx (abs nm))).
  Proof.
    econstructor 1 with (BiR := fun om nm => om = (abs nm))
                          (mutatorMap := @id MutatorIndex)
                          (observerMap := @id ObserverIndex);
    compute; intros;
    [inversion_by computes_to_inv; subst; eauto
     | inversion_by computes_to_inv; subst; eauto].
  Qed.

  (* We can always build a default implementation (computation?) for the
     mutators of an ADT with an updated representation using the old
     mutators. *)
  Definition absMutatorMethods oldRep newRep
        (BiR : oldRep -> newRep -> Prop)
        mutIdx
        (oldMuts : mutIdx -> mutatorMethodType oldRep) idx nr n : Comp newRep :=
    {nr' | forall or,
             BiR or nr ->
             exists or',
               (oldMuts idx or n) ↝ or' /\
               BiR or' nr'}%comp.

  Lemma refine_absMutatorMethods oldRep newRep
        (BiR : oldRep -> newRep -> Prop)
        mutIdx
        (oldMuts : mutIdx -> mutatorMethodType oldRep)
  : forall idx,
      @refineMutator oldRep newRep BiR
                     (oldMuts idx)
                     (absMutatorMethods BiR oldMuts idx).
  Proof.
    unfold refineMutator, absMutatorMethods, refine; intros.
    inversion_by computes_to_inv.
    destruct (H0 _ H) as [or' [Comp_or BiR_or''] ].
    econstructor; eauto.
  Qed.

  (* Always unfold absMutatorMethods. *)
  Global Arguments absMutatorMethods oldRep newRep BiR mutIdx oldMuts / idx nr n.

  Hint Resolve refine_absMutatorMethods.

  (* A similar approach works for observers. *)

  Definition absObserverMethods oldRep newRep
             (BiR : oldRep -> newRep -> Prop)
             obsIdx
             (oldObs : obsIdx -> observerMethodType oldRep) idx nr n : Comp nat :=
    {n' | forall or,
            BiR or nr ->
            (oldObs idx or n) ↝ n'}%comp.

  Lemma refine_absObserverMethods oldRep newRep
        (BiR : oldRep -> newRep -> Prop)
        obsIdx
        (oldObs : obsIdx -> observerMethodType oldRep)
  : forall idx,
      @refineObserver oldRep newRep BiR (oldObs idx)
                     (absObserverMethods BiR oldObs idx).
  Proof.
    unfold refineObserver, absObserverMethods, refine; intros.
    inversion_by computes_to_inv; eauto.
  Qed.

  Global Arguments absObserverMethods oldRep newRep BiR obsIdx oldObs / idx nr n .

  Hint Resolve refine_absObserverMethods.

  (* We can refine an ADT using the above default mutator and observer
     implementations. *)

  Lemma refineADT_Build_ADT_Rep_default oldRep newRep
        (BiR : oldRep -> newRep -> Prop)
        mutIdx obsIdx oldMuts oldObs :
    refineADT
      (@Build_ADT oldRep mutIdx obsIdx oldMuts oldObs)
      (@Build_ADT newRep mutIdx obsIdx
                  (absMutatorMethods BiR oldMuts)
                  (absObserverMethods BiR oldObs)).
  Proof.
    eapply refineADT_Build_ADT_Rep; eauto.
  Qed.

  Section SimplifyRep.

  (* If a representation has extraneous information (perhaps intermediate
     data introduced during refinement), simplifying the representation
     is a valid refinement. *)

    Variable oldRep : Type.
    Variable newRep : Type.

    Variable simplifyf : oldRep -> newRep.
    Variable concretize : newRep -> oldRep.
    Variable BiR : oldRep -> newRep -> Prop.

    Notation "ro ≃ rn" := (BiR ro rn) (at level 70).

    Definition simplifyMutatorMethods
               mutIdx (oldMuts : mutIdx -> mutatorMethodType oldRep)
               idx r_n n : Comp newRep :=
      (r_o' <- (oldMuts idx (concretize r_n) n);
       ret (simplifyf r_o'))%comp.

  Definition simplifyObserverMethods
             obsIdx (oldObs : obsIdx -> observerMethodType oldRep)
             idx nr n : Comp nat :=
    oldObs idx (concretize nr) n.

  Definition simplifyRep
             mutIdx obsIdx oldMuts oldObs :
    (forall r_n r_o,
                (r_o ≃ r_n) ->
                forall idx n,
                  refineEquiv (r_o'' <- oldMuts idx r_o n;
                              {r_n' | r_o'' ≃ r_n'})
                              (r_o'' <- oldMuts idx (concretize r_n) n;
                              ret (simplifyf r_o''))) ->
    (forall r_n r_o,
                (r_o ≃ r_n) ->
                forall idx n,
                  refineEquiv (oldObs idx r_o n)
                              (oldObs idx (concretize r_n) n)) ->
    refineADT
      (@Build_ADT oldRep mutIdx obsIdx oldMuts oldObs)
      (@Build_ADT newRep mutIdx obsIdx
                  (simplifyMutatorMethods oldMuts)
                  (simplifyObserverMethods oldObs)).
  Proof.
    econstructor 1 with
    (BiR := BiR)
      (mutatorMap := @id mutIdx)
      (observerMap := @id obsIdx); simpl; eauto.
    - unfold simplifyMutatorMethods; intros; eapply H; eauto.
    - unfold simplifyObserverMethods; intros; eapply H0; eauto.
  Qed.

  End SimplifyRep.

(** TODO: Update this to reflect the new definition of ADT + ADT
    Refinement *)

(* If you mutate and then observe, you can do it before or after
    refinement.  I'm not actually sure this isn't obvious.
 *)

(* Lemma ADTRefinementOk
      (old new : ADT)
      (new_initial_value : Comp (Rep new))
      abs mutatorMap observerMap H H'
      (ref : refineADT old new
       := @refinesADT old new abs mutatorMap observerMap H H')
      mutIdx obsIdx n n'
: refine (v0 <- new_initial_value;
          v <- abs v0;
          v' <- MutatorMethods old mutIdx v n;
          ObserverMethods old obsIdx v' n')
         (v <- new_initial_value;
          v' <- MutatorMethods new (mutatorMap mutIdx) v n;
          ObserverMethods new (observerMap obsIdx) v' n').
Proof.
  simpl in *.
  apply refine_bind; [ reflexivity | ].
  intro.
  interleave_autorewrite_refine_monad_with setoid_rewrite_hyp.
Qed. *)

End GeneralRefinements.

(* Goals with [refine] nested in a [pick] crop up when
   switching representations; this simplifies them to
   what is expected. *)
Lemma refine_pick_refine (A B : Type) f P :
  refine {a : A | refine {b : B | P b} (ret (f a))} {a : A | P (f a)}.
Proof.
  intros Ra v; constructor; intros v' Rb.
  apply computes_to_inv in Rb; subst.
  inversion_by computes_to_inv; econstructor; eauto.
Qed.

Hint Rewrite refine_pick_refine : refine_monad.

(* Honing tactic for refining the observer method with the specified index.
     This version of the tactic takes the new implementation as an argument. *)
Tactic Notation "hone" "observer" constr(obsIdx) "using" constr(obsBody) :=
  let A :=
      match goal with
          |- Sharpened ?A => constr:(A) end in
  let mutIdx_eq' := fresh in
  let Rep' := eval simpl in (Rep A) in
    let MutatorIndex' := eval simpl in (MutatorIndex A) in
    let ObserverIndex' := eval simpl in (ObserverIndex A) in
    let MutatorMethods' := eval simpl in (MutatorMethods A) in
    let ObserverMethods' := eval simpl in (ObserverMethods A) in
      assert (forall idx idx' : ObserverIndex', {idx = idx'} + {idx <> idx'})
        as obsIdx_eq' by (decide equality);
      let RefineH := fresh in
      assert (pointwise_relation ObserverIndex' (refineObserver (@eq Rep'))
                                 (ObserverMethods')
                                 (fun idx => if (obsIdx_eq' idx ()) then
                                               obsBody
                                             else
                                               ObserverMethods' idx)) as RefineH;
        [let obsIdx' := fresh in
         unfold pointwise_relation; intro obsIdx';
         destruct (obsIdx_eq' obsIdx' ()); simpl; intros; simpl;
         [idtac | (* Replaced mutator case left to user*)
          subst; reflexivity] (* Otherwise, they are the same *)
        | eapply SharpenStep;
          [eapply (@refineADT_Build_ADT_Observer
                         Rep' ObserverIndex' MutatorIndex'
                         MutatorMethods'
                         ObserverMethods'
                         (fun idx => if (obsIdx_eq' idx ()) then
                                       obsBody
                                     else
                                       ObserverMethods' idx) RefineH)
          | idtac] ]; cbv beta in *; simpl in *.

  (* Honing tactic for refining the mutator method with the specified index.
     This version of the tactic takes the new implementation as an argument. *)
  Tactic Notation "hone" "mutator" constr(mutIdx) "using" constr(mutBody) :=
    let A :=
        match goal with
            |- Sharpened ?A => constr:(A) end in
    let mutIdx_eq' := fresh in
    let Rep' := eval simpl in (Rep A) in
    let MutatorIndex' := eval simpl in (MutatorIndex A) in
    let ObserverIndex' := eval simpl in (ObserverIndex A) in
    let MutatorMethods' := eval simpl in (MutatorMethods A) in
    let ObserverMethods' := eval simpl in (ObserverMethods A) in
      assert (forall idx idx' : MutatorIndex', {idx = idx'} + {idx <> idx'})
        as mutIdx_eq' by (decide equality);
      let RefineH := fresh in
      assert (pointwise_relation MutatorIndex' (refineMutator (@eq Rep'))
                                 (MutatorMethods')
                                 (fun idx => if (mutIdx_eq' idx ()) then
                                               mutBody
                                             else
                                               MutatorMethods' idx)) as RefineH;
        [let mutIdx' := fresh in
         unfold pointwise_relation; intro mutIdx';
         destruct (mutIdx_eq' mutIdx' ()); simpl; intros;
         setoid_rewrite refineEquiv_pick_eq'; autorewrite with refine_monad; simpl;
         [idtac | (* Replaced mutator case left to user*)
          subst; reflexivity] (* Otherwise, they are the same *)
        | eapply SharpenStep;
          [eapply (@refineADT_Build_ADT_Mutators
                         Rep' ObserverIndex' MutatorIndex'
                         ObserverMethods'
                         MutatorMethods'
                         (fun idx => if (mutIdx_eq' idx ()) then
                                       mutBody
                                     else
                                       MutatorMethods' idx) RefineH)
          | idtac] ]; cbv beta in *; simpl in *.

(* Honing tactic for refining the ADT representation which provides
   default observer and mutator implementations. *)
Tactic Notation "hone" "representation" "using" constr(BiSR) :=
    eapply SharpenStep;
    [eapply refineADT_Build_ADT_Rep_default with (BiR := BiSR) | idtac].
