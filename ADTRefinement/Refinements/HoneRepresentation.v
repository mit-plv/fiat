Require Import Common Computation ADT Ensembles.
Require Import ADTRefinement.Core ADTRefinement.SetoidMorphisms ADTRefinement.GeneralRefinements.

(* A generic refinement and honing tactic for switching the
    representation of an ADT. *)

Section HoneRepresentation.

  Variable oldRep : Type. (* The old representation type. *)
  Variable newRep : Type. (* The new representation type. *)

  (* The simulation relation between old and new representations. *)
  Variable SiR : oldRep -> newRep -> Prop.
  Infix "≃" := (SiR) (at level 70).

  (* When switching representations, we can always build a default
     implementation (computation?) for the methods of an ADT with
     using the old methods. *)

  Definition absMutatorMethod
        (Dom : Type)
        (oldMuts : mutatorMethodType oldRep Dom) nr n
  : Comp newRep :=
    {nr' | forall or,
             or ≃ nr ->
             exists or',
               (oldMuts or n) ↝ or' /\
               or' ≃ nr'}%comp.

  Lemma refine_absMutatorMethod
        (Dom : Type)
        (oldMuts : mutatorMethodType oldRep Dom)
  : @refineMutator oldRep newRep SiR
                   _
                   oldMuts
                   (absMutatorMethod oldMuts).
  Proof.
    unfold refineMutator, absMutatorMethod, refine; intros.
    inversion_by computes_to_inv.
    destruct (H0 _ H) as [or' [Comp_or SiR_or''] ].
    econstructor; eauto.
  Qed.

  Hint Resolve refine_absMutatorMethod.

  (* A similar approach works for observers. *)
  Definition absObserverMethod
             (Dom Cod : Type)
             (oldObs : observerMethodType oldRep Dom Cod)
             nr n
  : Comp Cod :=
    {n' | forall or,
            or ≃ nr ->
            (oldObs or n) ↝ n'}%comp.

  Lemma refine_absObserverMethod
        (Dom Cod : Type)
        (oldObs :observerMethodType oldRep Dom Cod)
  : @refineObserver oldRep newRep SiR _ _ oldObs
                    (absObserverMethod oldObs).
  Proof.
    unfold refineObserver, absObserverMethod, refine; intros.
    inversion_by computes_to_inv; eauto.
  Qed.

  Hint Resolve refine_absObserverMethod.

  (* We can refine an ADT using the default mutator and observer
     implementations provided by [absMutatorMethod] and [absObserverMethod]. *)
  Lemma refineADT_Build_ADT_Rep_default
        Sig
        oldMuts oldObs :
    refineADT
      (@Build_ADT Sig oldRep oldMuts oldObs)
      (@Build_ADT Sig newRep
                  (fun idx => absMutatorMethod (oldMuts idx))
                  (fun idx => absObserverMethod (oldObs idx))).
  Proof.
    eapply refineADT_Build_ADT_Rep; eauto.
  Qed.

End HoneRepresentation.

  (* Always unfold absMutatorMethods and absObserverMethods. *)
Global Arguments absMutatorMethod oldRep newRep SiR Dom oldMuts / nr n.
Global Arguments absObserverMethod oldRep newRep SiR Dom Cod oldObs / nr n .

(* Honing tactic for refining the ADT representation which provides
   default observer and mutator implementations. *)
Tactic Notation "hone" "representation" "using" constr(BiSR) :=
    eapply SharpenStep;
    [eapply refineADT_Build_ADT_Rep_default with (SiR := BiSR) | idtac].
