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
        Fiat.ADTRefinement.BuildADTRefinements.HoneRepresentation
        Fiat.ADTRefinement.BuildADTSetoidMorphisms.

(* A generic refinement and honing tactic for applying a *)
(* tactic to all the operations of an ADT built from [BuildADT]. *)

Section RefineAllMethods.

  Variable Rep : Type. (* The old representation type. *)

  Lemma refineMethod_eq_sound :
    forall arity Dom Cod
           (cDef refinedCDef : methodType arity Rep Dom Cod),
      refineMethod_eq _ arity cDef refinedCDef ->
      let H := refinedCDef in refineMethod eq _ cDef H.
  Proof.
    simpl; intros; subst.
    induction arity; simpl; intros.
    - induction Dom; simpl; intros.
      + destruct Cod; simpl in *.
        * etransitivity.        
          apply refine_under_bind; intros.
          refine pick val (fst a); eauto; simplify with monad laws.
          destruct a; simpl; finish honing.
          simpl; autorewrite with monad laws; eapply H.
        * etransitivity.
          apply refine_under_bind; intros.
          refine pick val a; eauto; simpl; finish honing.
          simpl; autorewrite with monad laws; eapply H.
      + eapply (IHDom (cDef d) (refinedCDef d)).
        unfold refineMethod_eq; intros; eapply H.
    - subst; simpl in *; eauto.
  Qed.

  Lemma refineADT_BuildADT_Rep_refine_All_eq
        {n}
        (methSigs : Vector.t methSig n)
        (methDefs : ilist (B := @methDef Rep) methSigs)
        (refined_methDefs : ilist (B := @methDef Rep) methSigs)
    : Iterate_Ensemble_BoundedIndex (fun idx => refineMethod_eq _ _ (ith methDefs idx) (ith refined_methDefs idx))
      -> refineADT
           (BuildADT methDefs)
           (BuildADT refined_methDefs).
  Proof.
    intros; eapply refineADT_BuildADT_Rep_refine_All with (AbsR := eq).
    - revert H; clear; induction methSigs; simpl in *;
      destruct methDefs; destruct refined_methDefs; try econstructor; simpl.
      intros; destruct H; destruct prim_fst; destruct prim_fst0; econstructor; eauto.
      destruct h; eapply (@refineMethod_eq_sound _ methDom methCod); eauto.
  Qed.

End RefineAllMethods.

Ltac ilist_of_evar1 B As k :=
  lazymatch As with
    | Vector.nil _ => k (@inil _ B)
    | Vector.cons _ ?a ?n ?As' =>
      makeEvar (B a)
               ltac:(fun b =>
                       ilist_of_evar1
                         B As'
                         ltac:(fun Bs' => k (icons (n := n) b Bs'))) 
  end.

Ltac refineEachMethod :=
  lazymatch goal with
  |- Sharpened (@BuildADT ?Rep _ _ ?consSigs ?methSigs ?consDefs ?methDefs) =>
  ilist_of_evar1
        (@methDef Rep)
        methSigs
        ltac:(fun rMeths =>
                eapply refineADT_BuildADT_Rep_refine_All_eq
                with (refined_methDefs := rMeths)                       
             ); unfold refineMethod_eq;
    simpl; repeat apply Build_prim_and; intros; 
    first [ instantiate (1 := {| methBody :=  _ |})
          | eauto ]; simpl
  end.

