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
    unfold getMutDef.
    destruct (In_mutIdx _ mutIdx) as [dom In_mutIdx].
    rewrite In_ith with (a := {| mutID := mutIdx;
                                 mutDom := dom |})
                          (default_B :=
                             absMutDef (def mut "null" (r : rep, _ : ()) : rep :=
                                              ret r )%mutDef); eauto.
    rewrite <- ith_imap; simpl; eauto.
    unfold refine; intros.
    inversion_by computes_to_inv.
    destruct (H0 _ H) as [or' [Comp_or SiR_or''] ].
    econstructor; eauto.
    unfold mutSig_eq; find_if_inside; eauto.
    destruct (In_obsIdx _ obsIdx) as [dom [cod In_obsIdx] ].
    unfold getObsDef.
    rewrite In_ith with (a := {|obsID := obsIdx;
                                obsDom := dom;
                                obsCod := cod |})
                          (default_B :=
                             absObsDef (def obs "null" (r : rep, _ : () ) : () :=
                                              ret () )%obsDef); eauto.
    rewrite <- ith_imap; simpl; intros; eauto.
    unfold refine; intros.
    inversion_by computes_to_inv; eauto.
    unfold obsSig_eq; find_if_inside; eauto.
  Qed.

End HoneRepresentation.

(* Honing tactic for refining the ADT representation which provides
   default observer and mutator implementations. *)

Tactic Notation "hone" "representation'" "using" open_constr(SiR') :=
  eapply SharpenStep;
  [eapply refineADT_BuildADT_Rep_default with (SiR := SiR') |
   compute [imap absMutDef absMutatorMethod
                 absObsDef absObserverMethod]; simpl ].
