Require Import List Common 
        ADT.ADTSig ADT.Core
        ADTNotation.BuildADTSig ADTNotation.BuildADT
        ADTNotation.ilist ADTNotation.StringBound
        ADTRefinement.Core ADTRefinement.SetoidMorphisms
        ADTRefinement.GeneralRefinements
        ADTRefinement.Refinements.HoneRepresentation
        ADTRefinement.BuildADTSetoidMorphisms.

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

  Definition absConsDef
             (Sig : consSig)
             (oldCons : @consDef oldRep Sig)
  : @consDef newRep Sig :=
    {| consBody := absConstructor SiR (consBody oldCons) |}.

  Definition absMethDef
             (Sig : methSig)
             (oldCons : @methDef oldRep Sig)
  : @methDef newRep Sig :=
    {| methBody := absMethod SiR (methBody oldCons) |}.

  Lemma refineADT_BuildADT_Rep_default
            (consSigs : list consSig)
            (methSigs : list methSig)
            (consDefs : ilist (@consDef oldRep) consSigs)
            (methDefs : ilist (@methDef oldRep) methSigs) :
    refineADT
      (BuildADT consDefs methDefs)
      (BuildADT (imap _ absConsDef consDefs)
                (imap _ absMethDef methDefs)).
  Proof.
    eapply refineADT_Build_ADT_Rep with (SiR := SiR); eauto; intros.
    - unfold getConsDef.
      rewrite <- ith_Bounded_imap.
      unfold absConsDef, refineConstructor, refine; simpl; intros.
      inversion_by computes_to_inv; eauto.
    - unfold getMethDef.
      rewrite <- ith_Bounded_imap.
      unfold absMethDef, refineMethod, refine; simpl; intros.
      inversion_by computes_to_inv; eauto.
      destruct (H0 _ H) as [or' [Comp_or [SiR_or'' or''_eq] ] ];
        subst; repeat econstructor; eauto.
      destruct v; simpl in *; subst; econstructor.
  Qed.

End HoneRepresentation.

(* Honing tactic for refining the ADT representation which provides
   default metherver and consator implementations. *)

Tactic Notation "hone" "representation" "using" open_constr(SiR') :=
  eapply SharpenStep;
  [eapply refineADT_BuildADT_Rep_default with (SiR := SiR') |
   compute [imap absConsDef absConstructor
                 absMethDef absMethod]; simpl ].
