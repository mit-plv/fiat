Require Import Coq.Lists.List Fiat.Common
        Fiat.Common.ilist
        Fiat.Common.BoundedLookup
        Fiat.Common.IterateBoundedIndex
        Fiat.ADT.ADTSig
        Fiat.ADT.Core
        Fiat.ADTNotation.BuildADTSig
        Fiat.ADTNotation.BuildADT
        Fiat.ADTRefinement.Core
        Fiat.ADTRefinement.SetoidMorphisms
        Fiat.ADTRefinement.StatefulADTRefinement
        Fiat.ADTRefinement.GeneralRefinements
        Fiat.ADTRefinement.GeneralBuildADTRefinements
        Fiat.ADTRefinement.Refinements.HoneRepresentation
        Fiat.ADTRefinement.BuildADTSetoidMorphisms.

(* A generic refinement and honing tactic for switching the
    representation of an ADT built from [BuildADT]. *)

Section sHoneRepresentation.

  Variable oldRep : Type. (* The old representation type. *)
  Variable newRep : Type. (* The new representation type. *)

  (* Type of state (heaps in the case of ByteString ADT). *)
  Variable ST : Type.

  (** Abstraction Relation *)
  Variable AbsR : oldRep -> newRep -> ST -> Prop.

  Definition sMethSig (mSig : methSig) : methSig :=
    {| methID := methID mSig;
       methArity := methArity mSig;
       methDom := ST :: methDom mSig;
       methCod := match methCod mSig with
                  | Some T => Some (prod ST T)
                  | None => Some ST
                  end |}.

  Inductive refine_Methods :
    forall {n'} {methSigs : Vector.t methSig n'},
      ilist (B := @methDef oldRep) methSigs
      -> ilist (B := @methDef newRep) (Vector.map sMethSig methSigs)
      -> Prop :=
  | refine_Methods_nil : @refine_Methods _ (Vector.nil _) inil inil
  | refine_Methods_cons :
      forall n' methSig methSigs
             (meth_body : @methodType (methArity methSig) oldRep (methDom methSig) (methCod methSig))
             (refined_meth_body : @methodType (methArity (sMethSig methSig)) newRep (methDom (sMethSig methSig))
                                              (methCod (sMethSig methSig)))
             (methDefs : ilist (B := @methDef oldRep) methSigs)
             (refined_methDefs : ilist (B := @methDef newRep) (Vector.map sMethSig methSigs)),
        (let H := refined_meth_body in sRefineMethod AbsR meth_body H)
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
          sRefineMethod AbsR (ilist_hd methDefs) (ilist_hd refined_methDefs) /\
          refine_Methods (ilist_tl methDefs) (ilist_tl refined_methDefs)
    end methDefs refined_methDefs refine_meths.
  Proof.
    destruct refine_meths; eauto.
  Defined.

  Fixpoint ith_map
           {A A' : Type}
           {B : A' -> Type}
           {m : nat}
           {As : Vector.t A m}
           (f : A -> A')
           (il : ilist (B := B) (Vector.map f As))
           (n : Fin.t m)
    : B (f (Vector.nth As n)) :=
    match n in Fin.t m return
          forall (As : Vector.t A m),
            ilist (B := B) (Vector.map f As)
            -> B (f (Vector.nth As n)) with
    | Fin.F1 k =>
      fun As => Vector.caseS (fun n As =>
                                ilist (Vector.map f As)
                                -> B (f (Vector.nth As Fin.F1)))
                             (fun n As t => ilist_hd) As
    | Fin.FS k n' =>
      fun As => Vector_caseS' Fin.t
                              (fun n As n' => ilist (Vector.map f As)
                                              -> B (f (Vector.nth As (@Fin.FS n n'))))
                              (fun h n t m il => ith_map f (ilist_tl il) m)
                              As n'
    end As il.

  Definition BuildsADT
          {Rep : Type}
          {n' : nat}
          {methSigs : Vector.t methSig n'}
          (methDefs : ilist (B := @methDef Rep)
                            (Vector.map sMethSig methSigs))
    : sADT ST (BuildADTSig methSigs) := 
    {| Rep := Rep;
       Methods := fun idx : MethodIndex (sSig ST (BuildADTSig methSigs)) => ith_map sMethSig methDefs idx |}.

  (* This method is used to hone an ADT's representation and
     spawn off subgoals for each operation in one fell-swoop. *)
  Lemma refinesADT_BuildADT_Rep_refine_All
        {n}
        (methSigs : Vector.t methSig n)
        (methDefs : ilist (B := @methDef oldRep) methSigs)
        (refined_methDefs : ilist (B := @methDef newRep) (Vector.map sMethSig methSigs))
    :
      refine_Methods methDefs refined_methDefs
      -> refine_sADT
           (BuildADT methDefs)
           (BuildsADT refined_methDefs).
  Proof.
    intros.
    econstructor 1 with (sAbsR := AbsR).
    induction H; simpl.
    + intro; inversion idx.
    + intro; revert methSigs methDefs refined_methDefs
                    IHrefine_Methods H H0; clear.
      pattern n', idx.
      apply Fin.caseS; simpl; intros; eauto.
  Qed.

End sHoneRepresentation.
