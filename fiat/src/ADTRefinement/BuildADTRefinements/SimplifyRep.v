Require Import Coq.Lists.List Fiat.Common
        Fiat.ADT.ADTSig Fiat.ADT.Core
        Fiat.ADTNotation.BuildADTSig Fiat.ADTNotation.BuildADT
        Fiat.Common.ilist Fiat.Common.BoundedLookup
        Fiat.ADTRefinement.Core Fiat.ADTRefinement.SetoidMorphisms
        Fiat.ADTRefinement.GeneralRefinements
        Fiat.ADTRefinement.Refinements.HoneRepresentation
        Fiat.ADTRefinement.BuildADTSetoidMorphisms
        Fiat.ADTRefinement.Refinements.SimplifyRep.

Section SimplifyRep.

  (* If a representation has extraneous information (perhaps intermediate
     data introduced during refinement), simplifying the representation
     is a valid refinement. *)

  Variable oldRep : Type. (* The old representation type. *)
  Variable newRep : Type. (* The new representation type. *)

  Variable simplifyf : oldRep -> newRep. (* The simplification function. *)
  Variable concretize : newRep -> oldRep. (* A map to the enriched representation. *)

  (* The abstraction relation between old and new representations. *)
  Variable AbsR : oldRep -> newRep -> Prop.
  Notation "ro ≃ rn" := (AbsR ro rn) (at level 70).

(*  Definition simplifyMethDef
             (Sig : methSig)
             (oldMeth : @methDef oldRep Sig)
  : @methDef newRep Sig :=
    {| methBody := simplifyMethod simplifyf concretize (methBody oldMeth) |}.

  Definition simplifyConstrDef
             (Sig : consSig)
             (oldConstr : @consDef oldRep Sig)
  : @consDef newRep Sig :=
    {| consBody := simplifyConstructor simplifyf (consBody oldConstr) |}.

  (*Lemma refineADT_BuildADT_Simplify
        {n n'}
        (constrSigs : list consSig)
        (methSigs : list methSig)
        (constrDefs : ilist (@consDef oldRep) constrSigs)
        (methDefs : ilist (@methDef oldRep) methSigs) :
    (forall r_o, r_o ≃ simplifyf r_o) ->
    (forall r_n r_o,
       (r_o ≃ r_n) ->
       forall idx n,
         refineEquiv (r_o'' <- getMethDef methDefs idx r_o n;
                      r_n' <- {r_n' | fst r_o'' ≃ r_n'};
                      ret (r_n', snd r_o''))
                     (r_o'' <- getMethDef methDefs idx (concretize r_n) n;
                      ret (simplifyf (fst r_o''), snd r_o''))) ->
    refineADT
      (BuildADT constrDefs methDefs)
      (BuildADT (imap _ simplifyConstrDef constrDefs)
                (imap _ simplifyMethDef methDefs)).
  Proof.
    econstructor 1 with (AbsR := AbsR); simpl in *; eauto; intros.
    - rewrite <- ith_Bounded_imap.
      unfold simplifyConstrDef, simplifyConstructor; simpl.
      intros v Comp_v; computes_to_inv;
      repeat computes_to_econstructor; try subst; eauto.
    - rewrite <- ith_Bounded_imap.
      rewrite H0; eauto; reflexivity.
  Qed. *) *)

End SimplifyRep.
