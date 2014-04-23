Require Import List Common Computation ADT Ensembles ADTNotation.
Require Import ADTRefinement.Core ADTRefinement.SetoidMorphisms
        ADTRefinement.GeneralRefinements
        ADTRefinement.Refinements.HoneRepresentation
        ADTRefinement.BuildADTSetoidMorphisms.

Generalizable All Variables.
Set Implicit Arguments.

(* A generic refinement and honing tactic for switching the
    representation of an ADT built from [BuildADT]. *)

Section HoneRepresentation.

  Variable oldRep : Type. (* The old representation type. *)
  Variable newRep : Type. (* The new representation type. *)

  (* The simulation relation between old and new representations. *)
  Variable SiR : oldRep -> newRep -> Prop.

  (* When switching representations, we can always build a default
     implementation (computation?) for the methods of an ADT with
     using the old methods. *)

  Definition absMutDef
             (Sig : mutSig)
             (oldMut : @mutDef oldRep Sig)
  : @mutDef newRep Sig :=
    {| mutBody := absMutatorMethod SiR (mutBody oldMut) |}.

  Definition absObsDef
             (Sig : obsSig)
             (oldMut : @obsDef oldRep Sig)
  : @obsDef newRep Sig :=
    {| obsBody := absObserverMethod SiR (obsBody oldMut) |}.

  Lemma refineADT_BuildADT_Rep_default
            (mutSigs : list mutSig)
            (obsSigs : list obsSig)
            (mutDefs : ilist (@mutDef oldRep) mutSigs)
            (obsDefs : ilist (@obsDef oldRep) obsSigs) :
    refineADT
      (BuildADT mutDefs obsDefs)
      (BuildADT (imap _ absMutDef mutDefs)
                (imap _ absObsDef obsDefs)).
  Proof.
    eapply refineADT_Build_ADT_Rep with (SiR := SiR); eauto; intros.
    - unfold getMutDef.
      rewrite <- ith_Bounded_imap.
      unfold absMutDef, refineMutator, refine; simpl; intros.
      inversion_by computes_to_inv.
      destruct (H0 _ H) as [or' [Comp_or SiR_or''] ].
      econstructor; eauto.
    - unfold getObsDef.
      rewrite <- ith_Bounded_imap.
      unfold absObsDef, refineObserver, refine; simpl; intros.
      inversion_by computes_to_inv; eauto.
  Qed.

End HoneRepresentation.

(* Honing tactic for refining the ADT representation which provides
   default observer and mutator implementations. *)

Tactic Notation "hone" "representation'" "using" open_constr(SiR') :=
  eapply SharpenStep;
  [eapply refineADT_BuildADT_Rep_default with (SiR := SiR') |
   compute [imap absMutDef absMutatorMethod
                 absObsDef absObserverMethod]; simpl ].
