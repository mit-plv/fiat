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
Definition SharpenStep Sig adt :
  forall adt',
    refineADT (Sig := Sig) adt adt' ->
    Sharpened adt' ->
    Sharpened adt.
Proof.
  intros adt' refineA SpecA';
  eexists (proj1_sig SpecA'); rewrite refineA; exact (proj2_sig SpecA').
Defined.

(* A tactic for finishing a derivation. Probably needs a better name.*)
Tactic Notation "finish" "sharpening" := eexists; reflexivity.

Section GeneralRefinements.
(* Given an abstraction function, we can transform the rep of a pickImpl ADT. *)

  Theorem refines_rep_pickImpl Sig
          newRep oldRep
          (abs : newRep -> oldRep)
          ObserverSpec MutatorSpec :
    refineADT
      (@pickImpl Sig oldRep MutatorSpec ObserverSpec)
      (@pickImpl Sig newRep
                 (fun idx nm n nm' => MutatorSpec idx (abs nm) n (abs nm'))
                 (fun idx nm => ObserverSpec idx (abs nm))).
  Proof.
    unfold pickImpl.
    let B' := match goal with |- refineADT ?A ?B => constr:(B) end in
    econstructor 1 with
    (B := B')
      (SiR := fun om nm => om = (abs nm));
    compute; intros; subst.
    apply computes_to_inv in H0; repeat econstructor; eauto.
    apply computes_to_inv in H0; repeat econstructor; eauto.
  Qed.

  (* We can always build a default implementation (computation?) for the
     mutators of an ADT with an updated representation using the old
     mutators. *)

  Definition absMutatorMethods Sig oldRep newRep
        (SiR : oldRep -> newRep -> Prop)
        (oldMuts :
           forall idx,
             mutatorMethodType oldRep (MutatorDom Sig idx)) idx nr n
  : Comp newRep :=
    {nr' | forall or,
             SiR or nr ->
             exists or',
               (oldMuts idx or n) ↝ or' /\
               SiR or' nr'}%comp.

  Lemma refine_absMutatorMethods Sig oldRep newRep
        (SiR : oldRep -> newRep -> Prop)
        (oldMuts :
           forall idx,
             mutatorMethodType oldRep (MutatorDom Sig idx))
  : forall idx,
      @refineMutator oldRep newRep SiR
                     _
                     (oldMuts idx)
                     (absMutatorMethods Sig SiR oldMuts idx).
  Proof.
    unfold refineMutator, absMutatorMethods, refine; intros.
    inversion_by computes_to_inv.
    destruct (H0 _ H) as [or' [Comp_or SiR_or''] ].
    econstructor; eauto.
  Qed.

  (* Always unfold absMutatorMethods. *)
  Global Arguments absMutatorMethods Sig oldRep newRep SiR oldMuts / idx nr n.

  Hint Resolve refine_absMutatorMethods.

  (* A similar approach works for observers. *)

  Definition absObserverMethods Sig oldRep newRep
             (SiR : oldRep -> newRep -> Prop)
             (oldObs :
                forall idx,
                  observerMethodType oldRep
                                     (ObserverDom Sig idx)
                                     (ObserverCod Sig idx))
             idx nr n
  : Comp (ObserverCod Sig idx) :=
    {n' | forall or,
            SiR or nr ->
            (oldObs idx or n) ↝ n'}%comp.

  Lemma refine_absObserverMethods Sig oldRep newRep
        (SiR : oldRep -> newRep -> Prop)
        (oldObs :
           forall idx,
             observerMethodType oldRep
                                (ObserverDom Sig idx)
                                (ObserverCod Sig idx))
  : forall idx,
      @refineObserver oldRep newRep SiR _ _ (oldObs idx)
                     (absObserverMethods Sig SiR oldObs idx).
  Proof.
    unfold refineObserver, absObserverMethods, refine; intros.
    inversion_by computes_to_inv; eauto.
  Qed.

  Global Arguments absObserverMethods Sig oldRep newRep SiR oldObs / idx nr n .

  Hint Resolve refine_absObserverMethods.

  (* We can refine an ADT using the above default mutator and observer
     implementations. *)

  Lemma refineADT_Build_ADT_Rep_default
        Sig oldRep newRep
        (SiR : oldRep -> newRep -> Prop)
        oldMuts oldObs :
    refineADT
      (@Build_ADT Sig oldRep oldMuts oldObs)
      (@Build_ADT Sig newRep
                  (absMutatorMethods Sig SiR oldMuts)
                  (absObserverMethods Sig SiR oldObs)).
  Proof.
    eapply refineADT_Build_ADT_Rep; eauto.
  Qed.

  Section SimplifyRep.

  (* If a representation has extraneous information (perhaps intermediate
     data introduced during refinement), simplifying the representation
     is a valid refinement. *)
    Variable Sig : ADTSig.

    Variable oldRep : Type.
    Variable newRep : Type.

    Variable simplifyf : oldRep -> newRep.
    Variable concretize : newRep -> oldRep.
    Variable SiR : oldRep -> newRep -> Prop.

    Notation "ro ≃ rn" := (SiR ro rn) (at level 70).

    Definition simplifyMutatorMethods
               (oldMuts :
                  forall idx,
                    mutatorMethodType oldRep (MutatorDom Sig idx))
               idx r_n n : Comp newRep :=
      (r_o' <- (oldMuts idx (concretize r_n) n);
       ret (simplifyf r_o'))%comp.

  Definition simplifyObserverMethods
             (oldObs :
                forall idx,
                  observerMethodType oldRep
                                     (ObserverDom Sig idx)
                                     (ObserverCod Sig idx))
             idx nr n : Comp (ObserverCod Sig idx) :=
    oldObs idx (concretize nr) n.

  Definition simplifyRep
             oldMuts oldObs :
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
      (@Build_ADT Sig oldRep oldMuts oldObs)
      (@Build_ADT Sig newRep
                  (simplifyMutatorMethods oldMuts)
                  (simplifyObserverMethods oldObs)).
  Proof.
    econstructor 1 with
    (SiR := SiR); simpl; eauto.
    - unfold simplifyMutatorMethods; intros; eapply H; eauto.
    - unfold simplifyObserverMethods; intros; eapply H0; eauto.
  Qed.

  End SimplifyRep.

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
    let ASig := match type of A with
                    ADT ?Sig => Sig
                end in
    let mutIdx_eq' := fresh in
    let Rep' := eval simpl in (Rep A) in
    let MutatorIndex' := eval simpl in (MutatorIndex ASig) in
    let ObserverIndex' := eval simpl in (ObserverIndex ASig) in
    let ObserverMethods' := eval simpl in (ObserverMethods A) in
      assert (forall idx idx' : ObserverIndex', {idx = idx'} + {idx <> idx'})
        as obsIdx_eq' by (decide equality);
      eapply SharpenStep;
      [eapply (@refineADT_Build_ADT_Observer
                 Rep' _ _ _
                 (fun idx : ObserverIndex ASig => if (obsIdx_eq' idx ()) then
                               obsBody
                             else
                               ObserverMethods' idx))
      | idtac]; cbv beta in *; simpl in *.

  (* Honing tactic for refining the mutator method with the specified index.
     This version of the tactic takes the new implementation as an argument. *)
  Tactic Notation "hone" "mutator" constr(mutIdx) "using" constr(mutBody) :=
    let A :=
        match goal with
            |- Sharpened ?A => constr:(A) end in
    let ASig := match type of A with
                    ADT ?Sig => Sig
                end in
    let mutIdx_eq' := fresh in
    let Rep' := eval simpl in (Rep A) in
    let MutatorIndex' := eval simpl in (MutatorIndex ASig) in
    let ObserverIndex' := eval simpl in (ObserverIndex ASig) in
    let MutatorMethods' := eval simpl in (MutatorMethods A) in
      assert (forall idx idx' : MutatorIndex', {idx = idx'} + {idx <> idx'})
        as mutIdx_eq' by (decide equality);
      eapply SharpenStep;
        [eapply (@refineADT_Build_ADT_Mutators Rep'
                   _
                   _
                   _
                   (fun idx : MutatorIndex ASig => if (mutIdx_eq' idx mutIdx) then
                                 mutBody
                               else
                                 MutatorMethods' idx))
        | idtac]; cbv beta in *; simpl in *.

(* Honing tactic for refining the ADT representation which provides
   default observer and mutator implementations. *)
Tactic Notation "hone" "representation" "using" constr(BiSR) :=
    eapply SharpenStep;
    [eapply refineADT_Build_ADT_Rep_default with (SiR := BiSR) | idtac].
