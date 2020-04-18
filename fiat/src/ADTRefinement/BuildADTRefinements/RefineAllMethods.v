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

  Lemma refineConstructor_eq_sound :
    forall cSig
           (cDef refinedCDef : constructorType Rep cSig),
      refineConstructor_eq Rep cDef refinedCDef ->
      let H := refinedCDef in refineConstructor eq cDef H.
  Proof.
    induction cSig; simpl; intros.
    - etransitivity.
      + apply refine_under_bind; intros.
        refine pick val a; eauto; finish honing.
      + simpl; autorewrite with monad laws; eauto.
    - eapply IHcSig; eauto.
  Qed.

  Lemma refineMethod_eq_sound :
    forall Dom Cod
           (cDef refinedCDef : methodType Rep Dom Cod),
      refineMethod_eq cDef refinedCDef ->
      let H := refinedCDef in refineMethod eq cDef H.
  Proof.
    unfold refineMethod; simpl; intros; subst.
    induction Dom; simpl; intros.
    - destruct Cod; simpl in *.
      + etransitivity.        
        * apply refine_under_bind; intros.
          refine pick val (fst a); eauto; simplify with monad laws.
          destruct a; simpl; finish honing.
        * simpl; autorewrite with monad laws; eapply H.
      + etransitivity.
        * apply refine_under_bind; intros.
          refine pick val a; eauto; simpl; finish honing.
        * simpl; autorewrite with monad laws; eapply H.
    - eapply (IHDom (fun r_n => cDef r_n d) (fun r_n => refinedCDef r_n d)).
      unfold refineMethod_eq; intros; eapply H.
  Qed.

  Lemma refineADT_BuildADT_Rep_refine_All_eq
        {n n'}
        (consSigs : Vector.t consSig n)
        (methSigs : Vector.t methSig n')
        (consDefs : ilist (B := @consDef Rep) consSigs)
        (methDefs : ilist (B := @methDef Rep) methSigs)
        (refined_consDefs : ilist (B := @consDef Rep) consSigs)
        (refined_methDefs : ilist (B := @methDef Rep) methSigs)
    : Iterate_Ensemble_BoundedIndex (fun idx => refineConstructor_eq _ (ith consDefs idx) (ith refined_consDefs idx))
      -> Iterate_Ensemble_BoundedIndex (fun idx => refineMethod_eq (ith methDefs idx) (ith refined_methDefs idx))
      -> refineADT
           (BuildADT consDefs methDefs)
           (BuildADT refined_consDefs refined_methDefs).
  Proof.
    intros; eapply refineADT_BuildADT_Rep_refine_All with (AbsR := eq).
    - revert H; clear; induction consSigs; simpl in *;
      destruct consDefs; destruct refined_consDefs; try econstructor; simpl.
      intros; destruct H; destruct prim_fst; destruct prim_fst0; econstructor; eauto.
      destruct h; eapply (@refineConstructor_eq_sound consDom); eauto.
    - revert H0; clear; induction methSigs; simpl in *;
      destruct methDefs; destruct refined_methDefs; try econstructor; simpl.
      intros; destruct H0; destruct prim_fst; destruct prim_fst0; econstructor; eauto.
      destruct h; eapply (@refineMethod_eq_sound methDom methCod); eauto.
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
                ilist_of_evar1
                  (@consDef Rep)
                  consSigs
                  ltac:(fun rCons =>
                          eapply refineADT_BuildADT_Rep_refine_All_eq
                          with (refined_methDefs := rMeths)
                                 (refined_consDefs := rCons)
             )); unfold refineMethod_eq;
    simpl; repeat apply Build_prim_and; intros; 
    first [instantiate (1 := {| consBody :=  _ |})
          | instantiate (1 := {| methBody :=  _ |})
          | eauto ]; simpl
  end.

