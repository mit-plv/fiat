Require Import List Arith
        Common Computation ADT.ADTSig ADT.Core
        ADTNotation.StringBound Common.ilist
        ADTNotation.BuildADTSig ADTNotation.BuildADT
        ADTNotation.BuildADTReplaceMethods
        ADTRefinement.Core ADTRefinement.GeneralRefinements
        ADTRefinement.SetoidMorphisms ADTRefinement.BuildADTSetoidMorphisms.

(* Notation-friendly versions of the honing tactics in GeneralRefinements. *)

Section BuildADTRefinements.

  Require Import String.
  Local Hint Resolve string_dec.

  Lemma refineADT_BuildADT_ReplaceConstructor
            (Rep : Type)
            (AbsR : Rep -> Rep -> Prop)
            (consSigs : list consSig)
            (methSigs : list methSig)
            (consDefs : ilist (@consDef Rep) consSigs)
            (methDefs : ilist (@methDef Rep) methSigs)
            (idx : @BoundedString (List.map consID consSigs))
            (newDef : consDef (nth_Bounded consID consSigs idx))
  :
    (forall consIdx,
       refineConstructor AbsR (getConsDef consDefs consIdx) (getConsDef consDefs consIdx))
    -> (forall methIdx,
          refineMethod AbsR (getMethDef methDefs methIdx) (getMethDef methDefs methIdx))
    -> refineConstructor AbsR
                     (consBody (ith_Bounded _ consDefs idx ))
                     (consBody newDef)
    -> refineADT
      (BuildADT consDefs methDefs)
      (ADTReplaceConsDef consDefs methDefs idx newDef).
  Proof.
    intros; eapply refineADT_BuildADT_Rep with (AbsR := AbsR); eauto.
    intros; unfold getConsDef.
    unfold replaceConsDef.
    eapply ith_replace_BoundedIndex_ind; eauto.
  Qed.

  Corollary refineADT_BuildADT_ReplaceConstructor_eq
            (Rep : Type)
            (consSigs : list consSig)
            (methSigs : list methSig)
            (consDefs : ilist (@consDef Rep) consSigs)
            (methDefs : ilist (@methDef Rep) methSigs)
            (idx : @BoundedString (List.map consID consSigs))
            (newDef : consDef (nth_Bounded consID consSigs idx))
  :
    refineConstructor eq
                  (consBody (ith_Bounded _ consDefs idx))
                  (consBody newDef)
    -> refineADT
      (BuildADT consDefs methDefs)
      (ADTReplaceConsDef consDefs methDefs idx newDef).
  Proof.
    eapply refineADT_BuildADT_ReplaceConstructor;
    simpl; unfold refine; intros; subst; eauto.
    repeat econstructor; try destruct v; eauto.
  Qed.

  Corollary SharpenStep_BuildADT_ReplaceConstructor_eq
            (Rep : Type)
            (consSigs : list consSig)
            (methSigs : list methSig)
            (consDefs : ilist (@consDef Rep) consSigs)
            (methDefs : ilist (@methDef Rep) methSigs)
            (idx : @BoundedString (List.map consID consSigs))
            (newDef : consDef (nth_Bounded consID consSigs idx))
  :
    (forall d,
      refine (consBody (ith_Bounded consID consDefs idx) d) (consBody newDef d))
    -> Sharpened (ADTReplaceConsDef consDefs methDefs idx newDef)
    -> Sharpened (BuildADT consDefs methDefs).
  Proof.
    intros; eapply SharpenStep; eauto.
    destruct newDef; simpl.
    intros; eapply refineADT_BuildADT_ReplaceConstructor_eq;
    simpl; intros; subst; try reflexivity;
    setoid_rewrite refineEquiv_pick_eq'; simplify with monad laws;
    eauto.
  Defined.

  Lemma refineADT_BuildADT_ReplaceConstructor_sigma
        (RepT : Type)
        (RepInv : RepT -> Prop)
        `{forall x, IsHProp (RepInv x)}
        (consSigs : list consSig)
        (methSigs : list methSig)
        (consDefs : ilist (@consDef (sig RepInv)) consSigs)
        (methDefs : ilist (@methDef (sig RepInv)) methSigs)
        (idx : @BoundedString (List.map consID consSigs))
        (newDef : consDef (nth_Bounded consID consSigs idx))
  : refineConstructor (fun x y => proj1_sig x = proj1_sig y)
                  (consBody (ith_Bounded _ consDefs idx))
                  (consBody newDef)
    -> refineADT
         (BuildADT consDefs methDefs)
         (ADTReplaceConsDef consDefs methDefs idx newDef).
  Proof.
    intro H'.
    eapply refineADT_BuildADT_ReplaceConstructor_eq.
    simpl in *; intros; subst; eauto.
    etransitivity; [ | eapply_hyp; reflexivity ].
    eapply refine_bind; [ reflexivity | intro ].
    eapply refine_flip_impl_Pick;
      repeat intro;
      apply path_sig_hprop;
      assumption.
  Qed.

  Lemma refineADT_BuildADT_ReplaceMethod
            (Rep : Type)
            (consSigs : list consSig)
            (methSigs : list methSig)
            (consDefs : ilist (@consDef Rep) consSigs)
            (methDefs : ilist (@methDef Rep) methSigs)
            (idx : @BoundedString (List.map methID methSigs))
            (newDef : methDef (nth_Bounded _ methSigs idx))
            AbsR
            (AbsR_reflexive_constructor :
               forall consIdx,
                 refineConstructor AbsR (getConsDef consDefs consIdx) (getConsDef consDefs consIdx))
            (AbsR_reflexive_method :
               forall methIdx,
                 refineMethod AbsR (getMethDef methDefs methIdx) (getMethDef methDefs methIdx))
  : refineMethod AbsR
                   (methBody (ith_Bounded _ methDefs idx))
                   (methBody newDef)
    -> refineADT
         (BuildADT consDefs methDefs)
         (ADTReplaceMethDef consDefs methDefs idx newDef).
  Proof.
    intros; eapply refineADT_BuildADT_Rep with (AbsR := AbsR); trivial.
    intros; unfold getMethDef.
    unfold replaceMethDef.
    eapply ith_replace_BoundedIndex_ind; eauto.
  Qed.

  Lemma refineADT_BuildADT_ReplaceMethod_eq
            (Rep : Type)
            (consSigs : list consSig)
            (methSigs : list methSig)
            (consDefs : ilist (@consDef Rep) consSigs)
            (methDefs : ilist (@methDef Rep) methSigs)
            (idx : @BoundedString (List.map methID methSigs))
            (newDef : methDef (nth_Bounded _ methSigs idx))
  : refineMethod eq
                   (methBody (ith_Bounded _ methDefs idx))
                   (methBody newDef)
    -> refineADT
         (BuildADT consDefs methDefs)
         (ADTReplaceMethDef consDefs methDefs idx newDef).
  Proof.
    eapply refineADT_BuildADT_ReplaceMethod;
    reflexivity.
  Qed.

  Corollary SharpenStep_BuildADT_ReplaceMethod_eq
            (Rep : Type)
            (consSigs : list consSig)
            (methSigs : list methSig)
            (consDefs : ilist (@consDef Rep) consSigs)
            (methDefs : ilist (@methDef Rep) methSigs)
            (idx : @BoundedString (List.map methID methSigs))
            (newDef : methDef (nth_Bounded _ methSigs idx))
  :
    (forall r_n n,
      refine (methBody (ith_Bounded methID methDefs idx) r_n n) (methBody newDef r_n n))
    -> Sharpened (ADTReplaceMethDef consDefs methDefs idx newDef)
    -> Sharpened (BuildADT consDefs methDefs).
  Proof.
    intros; eapply SharpenStep; eauto.
    destruct newDef; simpl.
    intros; eapply refineADT_BuildADT_ReplaceMethod_eq;
    simpl; intros; subst; try reflexivity;
    setoid_rewrite H; setoid_rewrite refineEquiv_pick_eq';
    simplify with monad laws.
    econstructor; eauto.
    destruct v; simpl; econstructor.
  Qed.

  Lemma refineADT_BuildADT_ReplaceMethod_sigma
        (RepT : Type)
        (RepInv : RepT -> Prop)
        (consSigs : list consSig)
        (methSigs : list methSig)
        (consDefs : ilist (@consDef (sig RepInv)) consSigs)
        (methDefs : ilist (@methDef (sig RepInv)) methSigs)
        (idx : @BoundedString (List.map methID methSigs))
        (newDef : methDef (nth_Bounded _ methSigs idx))
        (AbsR_reflexive_method :
           forall methIdx,
             refineMethod (fun x y => proj1_sig x = proj1_sig y)
                          (getMethDef methDefs methIdx)
                          (getMethDef methDefs methIdx))
  : refineMethod (fun x y => proj1_sig x = proj1_sig y)
                   (methBody (ith_Bounded _ methDefs idx))
                   (methBody newDef)
    -> refineADT
         (BuildADT consDefs methDefs)
         (ADTReplaceMethDef consDefs methDefs idx newDef).
  Proof.
    intro H'.
    eapply refineADT_BuildADT_ReplaceMethod with
    (AbsR := fun r_o r_n => proj1_sig r_o = proj1_sig r_n); eauto;
    simpl in *; intros; subst; eauto.
    intro; econstructor; eauto.
  Qed.

End BuildADTRefinements.

(* Tactic Notation "hone" "method" constr(methIdx) "using" open_constr(methBod) :=
  let A :=
      match goal with
          |- Sharpened ?A => constr:(A) end in
  let ASig := match type of A with
                  ADT ?Sig => Sig
              end in
  let consSigs :=
      match ASig with
          BuildADTSig ?consSigs _ => constr:(consSigs) end in
  let methSigs :=
      match ASig with
          BuildADTSig _ ?methSigs => constr:(methSigs) end in
  let consDefs :=
        match A with
            BuildADT ?consDefs _  => constr:(consDefs) end in
  let methDefs :=
        match A with
            BuildADT _ ?methDefs  => constr:(methDefs) end in
  let Rep' :=
      match A with
          @BuildADT ?Rep _ _ _ _ => constr:(Rep) end in
  let ConstructorIndex' := eval simpl in (ConstructorIndex ASig) in
  let MethodIndex' := eval simpl in (MethodIndex ASig) in
  let MethodDomCod' := eval simpl in (MethodDomCod ASig) in
  let methIdxB := eval simpl in
  (@Build_BoundedIndex _ (List.map methID methSigs) methIdx _) in
    eapply SharpenStep;
    [eapply (@refineADT_BuildADT_ReplaceMethod_eq
               Rep' _ _ consDefs methDefs methIdxB
               (@Build_methDef Rep'
                              {| methID := methIdx;
                                 methDom := fst (MethodDomCod' methIdxB);
                                 methCod := snd (MethodDomCod' methIdxB)
                              |}
                              methBod
                              ))
    | idtac]; cbv beta in *; simpl in *;
    cbv beta delta [replace_BoundedIndex replace_Index] in *;
    simpl in *.

Tactic Notation "hone" "constructor" constr(consIdx) "using" open_constr(consBod) :=
  let A :=
      match goal with
          |- Sharpened ?A => constr:(A) end in
  let ASig := match type of A with
                  ADT ?Sig => Sig
              end in
  let consSigs :=
      match ASig with
          BuildADTSig ?consSigs _ => constr:(consSigs) end in
  let methSigs :=
      match ASig with
          BuildADTSig _ ?methSigs => constr:(methSigs) end in
  let consDefs :=
      match A with
          BuildADT ?consDefs _  => constr:(consDefs) end in
  let methDefs :=
      match A with
          BuildADT _ ?methDefs  => constr:(methDefs) end in
  let Rep' :=
      match A with
          @BuildADT ?Rep _ _ _ _ => constr:(Rep) end in
  let ConstructorIndex' := eval simpl in (ConstructorIndex ASig) in
  let MethodIndex' := eval simpl in (MethodIndex ASig) in
  let ConstructorDom' := eval simpl in (ConstructorDom ASig) in
  let consIdxB := eval simpl in
  (@Build_BoundedIndex _ (List.map consID consSigs) consIdx _) in
    eapply SharpenStep;
    [eapply (@refineADT_BuildADT_ReplaceConstructor_eq
               Rep'  _ _ consDefs methDefs consIdxB
               (@Build_consDef Rep'
                              {| consID := consIdx;
                                 consDom := ConstructorDom' consIdxB
                              |}
                              consBod
                              ))
    | idtac]; cbv beta in *; simpl in *;
    cbv beta delta [replace_BoundedIndex replace_Index] in *;
    simpl in *.

Tactic Notation "hone" "method" constr(methIdx) :=
  hone' method methIdx using _;
  [set_evars;
    simpl in *; intros; subst;
    simplify with monad laws
 | ].

Tactic Notation "hone" "constructor" constr(consIdx) :=
  hone' constructor consIdx using _;
  [set_evars;
    simpl in *; intros; subst;
    simplify with monad laws  | ].

Tactic Notation "hone" "constructor" constr(consIdx) :=
  let A :=
      match goal with
          |- Sharpened ?A => constr:(A) end in
  let ASig := match type of A with
                  ADT ?Sig => Sig
              end in
  let consSigs :=
      match ASig with
          BuildADTSig ?consSigs _ => constr:(consSigs) end in
  let methSigs :=
      match ASig with
          BuildADTSig _ ?methSigs => constr:(methSigs) end in
  let consDefs :=
      match A with
          BuildADT ?consDefs _  => constr:(consDefs) end in
  let methDefs :=
      match A with
          BuildADT _ ?methDefs  => constr:(methDefs) end in
  let Rep' :=
      match A with
          @BuildADT ?Rep _ _ _ _ => constr:(Rep) end in
  let ConstructorIndex' := eval simpl in (ConstructorIndex ASig) in
  let MethodIndex' := eval simpl in (MethodIndex ASig) in
  let ConstructorDom' := eval simpl in (ConstructorDom ASig) in
  let consIdxB := eval simpl in
  (@Build_BoundedIndex _ (List.map consID consSigs) consIdx _) in
      eapply (@SharpenStep_BuildADT_ReplaceConstructor_eq
               Rep'  _ _ consDefs methDefs consIdxB
               (@Build_consDef Rep'
                              {| consID := consIdx;
                                 consDom := ConstructorDom' consIdxB
                              |}
                              _
             ));
    [ intros; try (apply refine_pick_forall_Prop with
                   (P := fun r_n n r_o => _); intros);
      simpl in *; set_evars; simpl in *; subst |
        cbv beta in *; simpl in *;
        cbv beta delta [replace_BoundedIndex replace_Index] in *;
        simpl in *].

Tactic Notation "hone" "method" constr(methIdx) :=
  let A :=
      match goal with
          |- Sharpened ?A => constr:(A) end in
  let ASig := match type of A with
                  ADT ?Sig => Sig
              end in
  let consSigs :=
      match ASig with
          BuildADTSig ?consSigs _ => constr:(consSigs) end in
  let methSigs :=
      match ASig with
          BuildADTSig _ ?methSigs => constr:(methSigs) end in
  let consDefs :=
      match A with
          BuildADT ?consDefs _  => constr:(consDefs) end in
  let methDefs :=
      match A with
          BuildADT _ ?methDefs  => constr:(methDefs) end in
  let Rep' :=
      match A with
          @BuildADT ?Rep _ _ _ _ => constr:(Rep) end in
  let ConstructorIndex' := eval simpl in (ConstructorIndex ASig) in
  let MethodIndex' := eval simpl in (MethodIndex ASig) in
  let MethodDomCod' := eval simpl in (MethodDomCod ASig) in
  let methIdxB := eval simpl in
  (@Build_BoundedIndex _ (List.map methID methSigs) methIdx _) in
      eapply (@SharpenStep_BuildADT_ReplaceMethod_eq
                Rep'  _ _ consDefs methDefs methIdxB
                (@Build_methDef Rep'
                               {| methID := methIdx;
                                  methDom := fst (MethodDomCod' methIdxB);
                                  methCod := snd (MethodDomCod' methIdxB)
                               |}
                               _
                              ));
    [ intros; repeat (progress (try rewrite refine_pick_computes_to;
                                try apply refine_pick_forall_Prop with
                                (P := fun _ _ _ => _); intros));
      simpl in *; set_evars; simpl in *; subst |
          cbv beta in *; simpl in *;
          cbv beta delta [replace_BoundedIndex replace_Index] in *;
          simpl in *]. *)

Tactic Notation "finish" "honing" :=
  subst_body;
  first [higher_order_2_reflexivity | higher_order_1_reflexivity ].
