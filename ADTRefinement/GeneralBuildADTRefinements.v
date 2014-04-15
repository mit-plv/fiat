Require Import Common Computation ADT BuildADT ADTNotation List.
Require Export ADTRefinement.Core ADTRefinement.GeneralRefinements
        ADTRefinement.SetoidMorphisms ADTRefinement.BuildADTSetoidMorphisms.

(* Notation-friendly versions of the honing tactics in GeneralRefinements. *)

Generalizable All Variables.
Set Implicit Arguments.

Section BuildADTRefinements.

  (* To define a notation-friendly version of honing individual
     methods, we use [ADTReplaceMutDef] and [ADTReplaceObsDef] to
     insert the new definition in the indexed list of method bodies.
   *)

  Lemma In_mutSigs_eq
    (mutSigs : list mutSig)
  : forall (idx : BoundedString (map mutID mutSigs))
           (mutIdx : String.string),
   mutSig_eq
     (nth (findIndex mutSig_eq mutSigs idx) mutSigs
        ("null" : rep × () → rep)%mutSig) mutIdx = true ->
   mutIdx = idx.
  Proof.
    intros.
    destruct (In_mutIdx _ idx) as [dom In_mutIdx].
    eapply In_AC_eq; eauto.
    unfold mutSig_eq; intros; repeat find_if_inside; congruence.
    unfold mutSig_eq; find_if_inside; simpl in *; congruence.
  Qed.

  Lemma In_mutSigs
        (mutSigs : list mutSig)
  : forall (idx : BoundedString (map mutID mutSigs)),
      List.In
        (nth (findIndex mutSig_eq mutSigs idx) mutSigs
             ("null" : rep × () → rep)%mutSig) mutSigs.
  Proof.
    intros; destruct (In_mutIdx _ idx) as [dom In_mutIdx].
    eapply In_As; eauto.
    unfold mutSig_eq; find_if_inside; simpl in *; congruence.
  Qed.

  Hint Resolve In_mutSigs.

  Lemma refineADT_BuildADT_ReplaceMutator
            (Rep : Type)
            (SiR : Rep -> Rep -> Prop)
            (mutSigs : list mutSig)
            (obsSigs : list obsSig)
            (mutDefs : ilist (@mutDef Rep) mutSigs)
            (obsDefs : ilist (@obsDef Rep) obsSigs)
            (idx : BoundedString (List.map mutID mutSigs))
            (newDef : mutDef (nth (findIndex mutSig_eq mutSigs idx)
                                  mutSigs _))
  :
    (forall mutIdx,
       refineMutator SiR (getMutDef mutDefs mutIdx) (getMutDef mutDefs mutIdx))
    -> (forall obsIdx,
          refineObserver SiR (getObsDef obsDefs obsIdx) (getObsDef obsDefs obsIdx))
    -> refineMutator SiR
                     (mutBody (ith mutSig_eq mutDefs idx _
                                   {| mutBody := (fun r _ => ret r) |}))
                     (mutBody newDef)
    -> refineADT
      (BuildADT mutDefs obsDefs)
      (ADTReplaceMutDef mutDefs obsDefs idx newDef).
  Proof.
    intros; eapply refineADT_BuildADT_Rep with (SiR := SiR); eauto.
    intros; unfold getMutDef.
    caseEq (mutSig_eq (nth (findIndex mutSig_eq mutSigs idx) mutSigs
                           ("null" : rep × () → rep)%mutSig) mutIdx).
    - generalize (In_mutSigs_eq _ _ _ H2); intros; subst.
      simpl; intros; erewrite ith_replace'; eauto.
    - simpl replaceMutDef.
      erewrite ith_replace; eauto.
  Qed.

  Corollary refineADT_BuildADT_ReplaceMutator_eq
            (Rep : Type)
            (mutSigs : list mutSig)
            (obsSigs : list obsSig)
            (mutDefs : ilist (@mutDef Rep) mutSigs)
            (obsDefs : ilist (@obsDef Rep) obsSigs)
            (idx : BoundedString (List.map mutID mutSigs))
            (newDef : mutDef (nth (findIndex mutSig_eq mutSigs idx)
                                  mutSigs _))
  :
    refineMutator eq
                  (mutBody (ith mutSig_eq mutDefs idx _
                                {| mutBody := (fun r _ => ret r) |}))
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
        (newDef : mutDef (nth (findIndex mutSig_eq mutSigs idx)
                              mutSigs _))
  : refineMutator (fun x y => proj1_sig x = proj1_sig y)
                  (mutBody (ith mutSig_eq mutDefs idx _
                                {| mutBody := (fun r _ => ret r) |}))
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

  Lemma In_obsSigs_eq
    (obsSigs : list obsSig)
  : forall (idx : BoundedString (map obsID obsSigs))
           (obsIdx : String.string),
   obsSig_eq
     (nth (findIndex obsSig_eq obsSigs idx) obsSigs
        ("null" : rep × () → ())%obsSig) obsIdx = true ->
   obsIdx = idx.
  Proof.
    intros.
    destruct (In_obsIdx _ idx) as [dom [cod In_obsIdx] ].
    eapply In_AC_eq; eauto.
    unfold obsSig_eq; intros; repeat find_if_inside; congruence.
    unfold obsSig_eq; find_if_inside; simpl in *; congruence.
  Qed.

  Lemma In_obsSigs
        (obsSigs : list obsSig)
  : forall (idx : BoundedString (map obsID obsSigs)),
      List.In
        (nth (findIndex obsSig_eq obsSigs idx) obsSigs
             ("null" : rep × () → ())%obsSig) obsSigs.
  Proof.
    intros; destruct (In_obsIdx _ idx) as [dom [cod In_obsIdx] ].
    eapply In_As; eauto.
    unfold obsSig_eq; find_if_inside; simpl in *; congruence.
  Qed.

  Hint Resolve In_obsSigs.

  Lemma refineADT_BuildADT_ReplaceObserver_generic
            (Rep : Type)
            (mutSigs : list mutSig)
            (obsSigs : list obsSig)
            (mutDefs : ilist (@mutDef Rep) mutSigs)
            (obsDefs : ilist (@obsDef Rep) obsSigs)
            (idx : BoundedString (List.map obsID obsSigs))
            (newDef : obsDef (nth (findIndex obsSig_eq obsSigs idx)
                                  obsSigs ("null" : rep × () → ())%obsSig))
            SiR
            (SiR_reflexive_mutator : forall mutIdx,
                                       refineMutator SiR (getMutDef mutDefs mutIdx) (getMutDef mutDefs mutIdx))
            (SiR_reflexive_observer : forall obsIdx,
                                        refineObserver SiR (getObsDef obsDefs obsIdx) (getObsDef obsDefs obsIdx))
  : refineObserver SiR
                   (obsBody (ith obsSig_eq obsDefs idx _
                                 (@Build_obsDef Rep ("null" : rep × () → ()) (fun r _ => ret tt))
                   ))
                   (obsBody newDef)
    -> refineADT
         (BuildADT mutDefs obsDefs)
         (ADTReplaceObsDef mutDefs obsDefs idx newDef).
  Proof.
    intros; eapply refineADT_BuildADT_Rep with (SiR := SiR);
    trivial.
    intro obsIdx.
    case_eq (obsSig_eq (nth (findIndex obsSig_eq obsSigs idx) obsSigs
                            ("null" : rep × () → ())%obsSig) obsIdx);
      intro H'.
    - generalize (In_obsSigs_eq _ _ _ H'); intros; subst.
      simpl; intros; erewrite ith_replace'; eauto.
    - simpl replaceObsDef; simpl getObsDef; erewrite ith_replace; eauto.
  Qed.

  Lemma refineADT_BuildADT_ReplaceObserver
            (Rep : Type)
            (mutSigs : list mutSig)
            (obsSigs : list obsSig)
            (mutDefs : ilist (@mutDef Rep) mutSigs)
            (obsDefs : ilist (@obsDef Rep) obsSigs)
            (idx : BoundedString (List.map obsID obsSigs))
            (newDef : obsDef (nth (findIndex obsSig_eq obsSigs idx)
                                  obsSigs ("null" : rep × () → ())%obsSig))
  : refineObserver eq
                   (obsBody (ith obsSig_eq obsDefs idx _
                                 (@Build_obsDef Rep ("null" : rep × () → ()) (fun r _ => ret tt))
                   ))
                   (obsBody newDef)
    -> refineADT
         (BuildADT mutDefs obsDefs)
         (ADTReplaceObsDef mutDefs obsDefs idx newDef).
  Proof.
    eapply refineADT_BuildADT_ReplaceObserver_generic;
    reflexivity.
  Qed.

  Lemma refineADT_BuildADT_ReplaceObserver_eq
            (Rep : Type)
            (mutSigs : list mutSig)
            (obsSigs : list obsSig)
            (mutDefs : ilist (@mutDef Rep) mutSigs)
            (obsDefs : ilist (@obsDef Rep) obsSigs)
            (idx : BoundedString (List.map obsID obsSigs))
            (newDef : obsDef (nth (findIndex obsSig_eq obsSigs idx) obsSigs _))
  : refineObserver eq
                  (obsBody (ith obsSig_eq obsDefs idx _
                                (@Build_obsDef Rep ("null" : rep × () → ()) (fun r _ => ret tt))
                                ))
                  (obsBody newDef)
    -> refineADT
         (BuildADT mutDefs obsDefs)
         (ADTReplaceObsDef mutDefs obsDefs idx newDef).
  Proof.
    eapply refineADT_BuildADT_ReplaceObserver;
    simpl; unfold refine; intros; subst; eauto.
  Qed.

  Lemma refineADT_BuildADT_ReplaceObserver_sigma
        (RepT : Type)
        (RepInv : RepT -> Prop)
        (mutSigs : list mutSig)
        (obsSigs : list obsSig)
        (mutDefs : ilist (@mutDef (sig RepInv)) mutSigs)
        (obsDefs : ilist (@obsDef (sig RepInv)) obsSigs)
        (idx : BoundedString (List.map obsID obsSigs))
        (newDef : obsDef (nth (findIndex obsSig_eq obsSigs idx)
                              obsSigs ("null" : rep × () → ())%obsSig))
  : refineObserver (fun x y => proj1_sig x = proj1_sig y)
                   (obsBody (ith obsSig_eq obsDefs idx _
                                 (@Build_obsDef (sig RepInv) ("null" : rep × () → ()) (fun r _ => ret tt))
                   ))
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
    (@Build_BoundedString (List.map obsID obsSigs) obsIdx _) in
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
    (@Build_BoundedString (List.map mutID mutSigs) mutIdx _) in
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
