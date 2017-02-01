Require Import Coq.Lists.List Fiat.Common
        Fiat.Common.ilist
        Fiat.Common.BoundedLookup
        Fiat.Common.IterateBoundedIndex
        Fiat.ADT.ADTSig
        Fiat.ADT.Core
        Fiat.ADTNotation.BuildADTSig
        Fiat.ADTNotation.BuildADT
        Fiat.ADTRefinement.Core Fiat.ADTRefinement.SetoidMorphisms
        Fiat.ADTRefinement.GeneralRefinements
        Fiat.ADTRefinement.GeneralBuildADTRefinements
        Fiat.ADTRefinement.Refinements.HoneRepresentation
        Fiat.ADTRefinement.BuildADTSetoidMorphisms.

(* A generic refinement and honing tactic for switching the
    representation of an ADT built from [BuildADT]. *)

Section HoneRepresentation.

  Variable oldRep : Type. (* The old representation type. *)
  Variable newRep : Type. (* The new representation type. *)

  (* The abstraction relation between old and new representations. *)
  Variable AbsR : oldRep -> newRep -> Prop.

  (* When switching representations, we can always build a default
     implementation (computation?) for the methods of an ADT with
     using the old methods. *)

  Definition absMethDef
             (Sig : methSig)
             (oldCons : @methDef oldRep Sig)
  : @methDef newRep Sig :=
    {| methBody := absMethod AbsR (methBody oldCons) |}.

  Lemma refineADT_BuildADT_Rep_default
        {n}
        {methSigs : Vector.t methSig n }
        (methDefs : ilist (B := @methDef oldRep) methSigs) :
    refineADT
      (BuildADT methDefs)
      (BuildADT (imap absMethDef methDefs)).
  Proof.
    eapply refineADT_Build_ADT_Rep with (AbsR := AbsR); eauto; intros.
    - unfold getMethDef.
      rewrite <- ith_imap.
      apply refine_absMethod.
  Qed.

  Inductive refine_Methods :
    forall {n'} {methSigs : Vector.t methSig n'},
      ilist (B := @methDef oldRep) methSigs
      -> ilist (B := @methDef newRep) methSigs ->
           Prop :=
  | refine_Methods_nil : @refine_Methods _ (Vector.nil _) inil inil
  | refine_Methods_cons :
      forall n' methSig methSigs
             (meth_body : @methodType (methArity methSig) oldRep (methDom methSig) (methCod methSig))
             (refined_meth_body : @methodType (methArity methSig) newRep (methDom methSig) (methCod methSig))
             (methDefs : ilist (B := @methDef oldRep) methSigs)
             (refined_methDefs : ilist (B := @methDef newRep) methSigs),
        (let H := refined_meth_body in refineMethod AbsR _ meth_body H)
        -> refine_Methods methDefs refined_methDefs
        -> @refine_Methods
             _
             (Vector.cons _ methSig n' methSigs)
             (icons {| methBody := meth_body |} methDefs)
                          (icons {| methBody := refined_meth_body |} refined_methDefs).

  Definition refine_Methods_invert
             {n'} methSigs methDefs refined_methDefs
             (refine_meths : @refine_Methods n' methSigs methDefs refined_methDefs)
  : match methSigs in Vector.t _ n' return
          forall methDefs refined_methDefs
                 (refine_meths : @refine_Methods n' methSigs methDefs refined_methDefs),
            Prop
    with
      | Vector.nil => fun _ _ _ => True
      | Vector.cons methSig _ methSigs' =>
        fun methDefs refined_methDefs refine_meths =>
          refineMethod AbsR _ (ilist_hd methDefs) (ilist_hd refined_methDefs) /\
          refine_Methods (ilist_tl methDefs) (ilist_tl refined_methDefs)
    end methDefs refined_methDefs refine_meths.
  Proof.
    destruct refine_meths; eauto.
  Defined.

  (* This method is used to hone an ADT's representation and
     spawn off subgoals for each operation in one fell-swoop. *)
  Lemma refineADT_BuildADT_Rep_refine_All
        {n}
        (methSigs : Vector.t methSig n)
        (methDefs : ilist (B := @methDef oldRep) methSigs)
        (refined_methDefs : ilist (B := @methDef newRep) methSigs)
  :
    refine_Methods methDefs refined_methDefs
    -> refineADT
         (BuildADT methDefs)
         (BuildADT refined_methDefs).
  Proof.
    intros; eapply refineADT_Build_ADT_Rep with (AbsR := AbsR).
    - induction H; simpl.
      + intro; inversion obsIdx.
      + intro; revert IHrefine_Methods H; clear.
        revert methSig meth_body refined_meth_body
               methSigs methDefs refined_methDefs; pattern n', obsIdx.
        match goal with
          |- ?P n' obsIdx => simpl; apply (Fin.caseS P); simpl; intros; eauto
        end.
  Qed.

End HoneRepresentation.

(* Honing tactic for refining the ADT representation which provides
   default method and constructor implementations. *)

(* Honing tactic for refining the representation type and spawning new subgoals for
 each of the operations. *)
Tactic Notation "hone" "representation" "using" open_constr(AbsR') :=
  eapply SharpenStep;
  [eapply refineADT_BuildADT_Rep_refine_All with (AbsR := AbsR');
   [ repeat (first [eapply refine_Methods_nil
                    | eapply refine_Methods_cons;
                      [ intros; simpl; intros;
                        match goal with
                        |  |- refine _ (?E _ _ _ _ _ _ _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ ) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _ _ _ _ ) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _ _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _ _) => is_evar E; let H := fresh in fast_set (H := E)
                        |  |- refine _ (?E _) => is_evar E; let H := fresh in fast_set (H := E)
                          | _ => idtac
                        end | ]
                    ])]
  | ].
