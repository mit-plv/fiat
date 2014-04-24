Require Import Common Computation ADT BuildADT ADTNotation List Arith.
Require Export ADTRefinement.Core ADTRefinement.GeneralRefinements
        ADTRefinement.SetoidMorphisms ADTRefinement.BuildADTSetoidMorphisms.

(* Notation-friendly versions of the honing tactics in GeneralRefinements. *)

Generalizable All Variables.
Set Implicit Arguments.

Section BuildADTRefinements.

  Lemma refineADT_BuildADT_ReplaceMutator
            (Rep : Type)
            (SiR : Rep -> Rep -> Prop)
            (mutSigs : list mutSig)
            (obsSigs : list obsSig)
            (mutDefs : ilist (@mutDef Rep) mutSigs)
            (obsDefs : ilist (@obsDef Rep) obsSigs)
            (idx : BoundedString (List.map mutID mutSigs))
            (newDef : mutDef (nth_Bounded mutID mutSigs idx))
  :
    (forall mutIdx,
       refineMutator SiR (getMutDef mutDefs mutIdx) (getMutDef mutDefs mutIdx))
    -> (forall obsIdx,
          refineObserver SiR (getObsDef obsDefs obsIdx) (getObsDef obsDefs obsIdx))
    -> refineMutator SiR
                     (mutBody (ith_Bounded _ mutDefs idx ))
                     (mutBody newDef)
    -> refineADT
      (BuildADT mutDefs obsDefs)
      (ADTReplaceMutDef mutDefs obsDefs idx newDef).
  Proof.
    intros; eapply refineADT_BuildADT_Rep with (SiR := SiR); eauto.
    intros; unfold getMutDef.
    unfold replaceMutDef.
    eapply ith_replace_BoundedIndex_ind; eauto.
  Qed.

  Corollary refineADT_BuildADT_ReplaceMutator_eq
            (Rep : Type)
            (mutSigs : list mutSig)
            (obsSigs : list obsSig)
            (mutDefs : ilist (@mutDef Rep) mutSigs)
            (obsDefs : ilist (@obsDef Rep) obsSigs)
            (idx : BoundedString (List.map mutID mutSigs))
            (newDef : mutDef (nth_Bounded mutID mutSigs idx))
  :
    refineMutator eq
                  (mutBody (ith_Bounded _ mutDefs idx))
                  (mutBody newDef)
    -> refineADT
      (BuildADT mutDefs obsDefs)
      (ADTReplaceMutDef mutDefs obsDefs idx newDef).
  Proof.
    eapply refineADT_BuildADT_ReplaceMutator;
    simpl; unfold refine; intros; subst; eauto.
  Qed.

  Lemma refineADT_BuildADT_ReplaceMutator_sigma
        (RepT : Type)
        (RepInv : RepT -> Prop)
        `{forall x, IsHProp (RepInv x)}
        (mutSigs : list mutSig)
        (obsSigs : list obsSig)
        (mutDefs : ilist (@mutDef (sig RepInv)) mutSigs)
        (obsDefs : ilist (@obsDef (sig RepInv)) obsSigs)
        (idx : BoundedString (List.map mutID mutSigs))
        (newDef : mutDef (nth_Bounded mutID mutSigs idx))
  : refineMutator (fun x y => proj1_sig x = proj1_sig y)
                  (mutBody (ith_Bounded _ mutDefs idx))
                  (mutBody newDef)
    -> refineADT
         (BuildADT mutDefs obsDefs)
         (ADTReplaceMutDef mutDefs obsDefs idx newDef).
  Proof.
    intro H'.
    eapply refineADT_BuildADT_ReplaceMutator_eq.
    simpl in *; intros; subst; eauto.
    etransitivity; [ | eapply_hyp; reflexivity ].
    eapply refine_bind; [ reflexivity | intro ].
    eapply refine_flip_impl_Pick;
      repeat intro;
      apply path_sig_hprop;
      assumption.
  Qed.

  Lemma refineADT_BuildADT_ReplaceObserver
            (Rep : Type)
            (mutSigs : list mutSig)
            (obsSigs : list obsSig)
            (mutDefs : ilist (@mutDef Rep) mutSigs)
            (obsDefs : ilist (@obsDef Rep) obsSigs)
            (idx : BoundedString (List.map obsID obsSigs))
            (newDef : obsDef (nth_Bounded _ obsSigs idx))
            SiR
            (SiR_reflexive_mutator : forall mutIdx,
                                       refineMutator SiR (getMutDef mutDefs mutIdx) (getMutDef mutDefs mutIdx))
            (SiR_reflexive_observer : forall obsIdx,
                                        refineObserver SiR (getObsDef obsDefs obsIdx) (getObsDef obsDefs obsIdx))
  : refineObserver SiR
                   (obsBody (ith_Bounded _ obsDefs idx))
                   (obsBody newDef)
    -> refineADT
         (BuildADT mutDefs obsDefs)
         (ADTReplaceObsDef mutDefs obsDefs idx newDef).
  Proof.
    intros; eapply refineADT_BuildADT_Rep with (SiR := SiR); trivial.
    intros; unfold getObsDef.
    unfold replaceObsDef.
    eapply ith_replace_BoundedIndex_ind; eauto.
  Qed.

  Lemma refineADT_BuildADT_ReplaceObserver_eq
            (Rep : Type)
            (mutSigs : list mutSig)
            (obsSigs : list obsSig)
            (mutDefs : ilist (@mutDef Rep) mutSigs)
            (obsDefs : ilist (@obsDef Rep) obsSigs)
            (idx : BoundedString (List.map obsID obsSigs))
            (newDef : obsDef (nth_Bounded _ obsSigs idx))
  : refineObserver eq
                   (obsBody (ith_Bounded _ obsDefs idx))
                   (obsBody newDef)
    -> refineADT
         (BuildADT mutDefs obsDefs)
         (ADTReplaceObsDef mutDefs obsDefs idx newDef).
  Proof.
    eapply refineADT_BuildADT_ReplaceObserver;
    reflexivity.
  Qed.

  Lemma refineADT_BuildADT_ReplaceObserver_sigma
        (RepT : Type)
        (RepInv : RepT -> Prop)
        (mutSigs : list mutSig)
        (obsSigs : list obsSig)
        (mutDefs : ilist (@mutDef (sig RepInv)) mutSigs)
        (obsDefs : ilist (@obsDef (sig RepInv)) obsSigs)
        (idx : BoundedString (List.map obsID obsSigs))
        (newDef : obsDef (nth_Bounded _ obsSigs idx))
  : refineObserver (fun x y => proj1_sig x = proj1_sig y)
                   (obsBody (ith_Bounded _ obsDefs idx))
                   (obsBody newDef)
    -> refineADT
         (BuildADT mutDefs obsDefs)
         (ADTReplaceObsDef mutDefs obsDefs idx newDef).
  Proof.
    intro H'.
    eapply refineADT_BuildADT_ReplaceObserver_eq.
    simpl in *; intros; subst; eauto.
  Qed.

End BuildADTRefinements.

Tactic Notation "hone'" "observer" constr(obsIdx) "using" open_constr(obsBod) :=
  let A :=
      match goal with
          |- Sharpened ?A => constr:(A) end in
  let ASig := match type of A with
                  ADT ?Sig => Sig
              end in
  let mutSigs :=
      match ASig with
          BuildADTSig ?mutSigs _ => constr:(mutSigs) end in
  let obsSigs :=
      match ASig with
          BuildADTSig _ ?obsSigs => constr:(obsSigs) end in
  let mutDefs :=
        match A with
            BuildADT ?mutDefs _  => constr:(mutDefs) end in
  let obsDefs :=
        match A with
            BuildADT _ ?obsDefs  => constr:(obsDefs) end in
    let Rep' :=
        match A with
            @BuildADT ?Rep _ _ _ _ => constr:(Rep) end in
    let MutatorIndex' := eval simpl in (MutatorIndex ASig) in
    let ObserverIndex' := eval simpl in (ObserverIndex ASig) in
    let ObserverDomCod' := eval simpl in (ObserverDomCod ASig) in
    let obsIdxB := eval simpl in
    (@Build_BoundedIndex (List.map obsID obsSigs) obsIdx _) in
      eapply SharpenStep;
      [eapply (@refineADT_BuildADT_ReplaceObserver
                 Rep' _ _ mutDefs obsDefs obsIdxB
                 (@Build_obsDef Rep'
                                {| obsID := obsIdx;
                                   obsDom := fst (ObserverDomCod' obsIdxB);
                                   obsCod := snd (ObserverDomCod' obsIdxB)
                                |}
                                obsBod
                                ))
      | idtac]; cbv beta in *; simpl in *.

  Tactic Notation "hone'" "mutator" constr(mutIdx) "using" open_constr(mutBod) :=
    let A :=
        match goal with
            |- Sharpened ?A => constr:(A) end in
    let ASig := match type of A with
                    ADT ?Sig => Sig
                end in
    let mutSigs :=
        match ASig with
            BuildADTSig ?mutSigs _ => constr:(mutSigs) end in
    let obsSigs :=
        match ASig with
            BuildADTSig _ ?obsSigs => constr:(obsSigs) end in
    let mutDefs :=
        match A with
            BuildADT ?mutDefs _  => constr:(mutDefs) end in
    let obsDefs :=
        match A with
            BuildADT _ ?obsDefs  => constr:(obsDefs) end in
    let Rep' :=
        match A with
            @BuildADT ?Rep _ _ _ _ => constr:(Rep) end in
    let MutatorIndex' := eval simpl in (MutatorIndex ASig) in
    let ObserverIndex' := eval simpl in (ObserverIndex ASig) in
    let MutatorDom' := eval simpl in (MutatorDom ASig) in
    let mutIdxB := eval simpl in
    (@Build_BoundedIndex (List.map mutID mutSigs) mutIdx _) in
      eapply SharpenStep;
      [eapply (@refineADT_BuildADT_ReplaceMutator_eq
                 Rep'  _ _ mutDefs obsDefs mutIdxB
                 (@Build_mutDef Rep'
                                {| mutID := mutIdx;
                                   mutDom := MutatorDom' mutIdxB
                                |}
                                mutBod
                                ))
      | idtac]; cbv beta in *; simpl in *.

  (* This applies reflexivity after refining a method. *)

Ltac higher_order_2_reflexivity :=
  let x := match goal with |- ?R ?x (?f ?a ?b) => constr:(x) end in
  let f := match goal with |- ?R ?x (?f ?a ?b) => constr:(f) end in
  let a := match goal with |- ?R ?x (?f ?a ?b) => constr:(a) end in
  let b := match goal with |- ?R ?x (?f ?a ?b) => constr:(b) end in
  let x' := (eval pattern a, b in x) in
  let f' := match x' with ?f' _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    reflexivity.

Tactic Notation "hone'" "observer" constr(obsIdx) :=
  hone' observer obsIdx using _;
  [set_evars | ].

Tactic Notation "hone'" "mutator" constr(mutIdx) :=
  hone' mutator mutIdx using _;
  [set_evars | ].
