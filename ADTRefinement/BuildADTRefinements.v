Require Import List Common Computation ADT Ensembles.
Require Export ADTRefinement.Core ADTRefinement.Specs ADTRefinement.Pick
        ADTRefinement.SetoidMorphisms ADTRefinement.GeneralRefinements
        ADTRefinement.BuildADTSetoidMorphisms.

Generalizable All Variables.
Set Implicit Arguments.

(* Refinements for working with ADTs built using BuildADT to have a
   nice syntax. *)

Section BuildADTRefinements.

  Definition absMutDef oldRep newRep
             (SiR : oldRep -> newRep -> Prop)
             (Sig : mutSig)
             (oldMut : @mutDef oldRep Sig)
  : @mutDef newRep Sig :=
    {| mutBody := absMutatorMethod SiR (mutBody oldMut) |}.

  Definition absObsDef oldRep newRep
             (SiR : oldRep -> newRep -> Prop)
             (Sig : obsSig)
             (oldMut : @obsDef oldRep Sig)
  : @obsDef newRep Sig :=
    {| obsBody := absObserverMethod SiR (obsBody oldMut) |}.

  Corollary refineADT_BuildADT_Rep_default
            (oldRep newRep : Type)
            (SiR : oldRep -> newRep -> Prop)
            (mutSigs : list mutSig)
            (obsSigs : list obsSig)
            (mutDefs : ilist (@mutDef oldRep) mutSigs)
            (obsDefs : ilist (@obsDef oldRep) obsSigs) :
    refineADT
      (BuildADT mutDefs obsDefs)
      (BuildADT (imap _ (absMutDef SiR) mutDefs)
                (imap _ (absObsDef SiR) obsDefs)).
  Proof.
    eapply refineADT_Build_ADT_Rep with (SiR := SiR); eauto; intros.
    unfold getMutDef.
    destruct (In_mutIdx _ mutIdx) as [dom In_mutIdx].
    rewrite In_ith with (a := {| mutID := mutIdx;
                                 mutDom := dom |})
                          (default_B :=
                             absMutDef SiR (def "null" `[r `: rep, _ `: ()]` : rep :=
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
                             absObsDef SiR (def "null" `[r `: rep, _ `: () ]` : () :=
                                              ret () )%obsDef); eauto.
    rewrite <- ith_imap; simpl; intros; eauto.
    unfold refine; intros.
    inversion_by computes_to_inv; eauto.
    unfold obsSig_eq; find_if_inside; eauto.
  Qed.

  Lemma In_mutSigs_eq
    (mutSigs : list mutSig)
  : forall (idx : BoundedString (map mutID mutSigs))
           (mutIdx : String.string),
   mutSig_eq
     (nth (findIndex mutSig_eq mutSigs idx) mutSigs
        ("null" : rep ✕ () → rep)%mutSig) mutIdx = true ->
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
             ("null" : rep ✕ () → rep)%mutSig) mutSigs.
  Proof.
    intros; destruct (In_mutIdx _ idx) as [dom In_mutIdx].
    eapply In_As; eauto.
    unfold mutSig_eq; find_if_inside; simpl in *; congruence.
  Qed.

  Hint Resolve In_mutSigs.

  Corollary refineADT_BuildADT_ReplaceMutator
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
    intros; eapply refineADT_BuildADT_Rep with (SiR := eq);
    try reflexivity.
    intros; unfold getMutDef.
    caseEq (mutSig_eq (nth (findIndex mutSig_eq mutSigs idx) mutSigs
                           ("null" : rep ✕ () → rep)%mutSig) mutIdx).
    - generalize (In_mutSigs_eq _ _ _ H0); intros; subst.
      simpl; intros; erewrite ith_replace'; eauto.
    - simpl replaceMutDef.
      erewrite ith_replace; eauto.
      reflexivity.
  Qed.

  Lemma In_obsSigs_eq
    (obsSigs : list obsSig)
  : forall (idx : BoundedString (map obsID obsSigs))
           (obsIdx : String.string),
   obsSig_eq
     (nth (findIndex obsSig_eq obsSigs idx) obsSigs
        ("null" : rep ✕ () → ())%obsSig) obsIdx = true ->
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
             ("null" : rep ✕ () → ())%obsSig) obsSigs.
  Proof.
    intros; destruct (In_obsIdx _ idx) as [dom [cod In_obsIdx] ].
    eapply In_As; eauto.
    unfold obsSig_eq; find_if_inside; simpl in *; congruence.
  Qed.

  Hint Resolve In_obsSigs.

  Corollary refineADT_BuildADT_ReplaceObserver
            (Rep : Type)
            (mutSigs : list mutSig)
            (obsSigs : list obsSig)
            (mutDefs : ilist (@mutDef Rep) mutSigs)
            (obsDefs : ilist (@obsDef Rep) obsSigs)
            (idx : BoundedString (List.map obsID obsSigs))
            (newDef : obsDef (nth (findIndex obsSig_eq obsSigs idx)
                                  obsSigs ("null" : rep ✕ () → ())%obsSig))
  : refineObserver eq
                  (obsBody (ith obsSig_eq obsDefs idx _
                                (@Build_obsDef Rep ("null" : rep ✕ () → ()) (fun r _ => ret tt))
                                ))
                  (obsBody newDef)
    -> refineADT
      (BuildADT mutDefs obsDefs)
      (ADTReplaceObsDef mutDefs obsDefs idx newDef).
  Proof.
    intros; eapply refineADT_BuildADT_Rep with (SiR := eq);
    try reflexivity.
    intros; unfold getObsDef.
    caseEq (obsSig_eq (nth (findIndex obsSig_eq obsSigs idx) obsSigs
                           ("null" : rep ✕ () → ())%obsSig) obsIdx).
    - generalize (In_obsSigs_eq _ _ _ H0); intros; subst.
      simpl; intros; erewrite ith_replace'; eauto.
    - simpl replaceObsDef; erewrite ith_replace; eauto.
      reflexivity.
  Qed.

(*  Section SimplifyRep.

    (* If a representation has extraneous information (perhaps intermediate
     data introduced during refinement), simplifying the representation
     is a valid refinement. *)
    Variable Sig : ADTSig.

    Variable oldRep : Type.
    Variable newRep : Type.

    Variable simplifyf : oldRep -> newRep.
    Variable concretize : newRep -> oldRep.
    Variable SiR : oldRep -> newRep -> Prop.

    Notation "ro ≃ rn" := (SiR ro rn) (at level 70).

    Definition absMutDef oldRep newRep
             (SiR : oldRep -> newRep -> Prop)
             (Sig : mutSig)
             (oldMut : @mutDef oldRep Sig)
  : @mutDef newRep Sig :=
    {| mutBody := absMutatorMethod SiR (mutBody oldMut) |}.

    Definition absObsDef oldRep newRep
               (SiR : oldRep -> newRep -> Prop)
               (Sig : obsSig)
               (oldMut : @obsDef oldRep Sig)
    : @obsDef newRep Sig :=
      {| obsBody := absObserverMethod SiR (obsBody oldMut) |}.

    Corollary refineADT_BuildADT_Rep_default
              (oldRep newRep : Type)
              (SiR : oldRep -> newRep -> Prop)
              (mutSigs : list mutSig)
              (obsSigs : list obsSig)
              (mutDefs : ilist (@mutDef oldRep) mutSigs)
              (obsDefs : ilist (@obsDef oldRep) obsSigs) :
      refineADT
        (BuildADT mutDefs obsDefs)
        (BuildADT (imap _ (absMutDef SiR) mutDefs)
                  (imap _ (absObsDef SiR) obsDefs)).
    Proof.

    Definition simplifyRep
               oldMuts oldObs :
      (forall r_n r_o,
         (r_o ≃ r_n) ->
         forall idx n,
           refineEquiv (r_o'' <- oldMuts idx r_o n;
                        {r_n' | r_o'' ≃ r_n'})
                       (r_o'' <- oldMuts idx (concretize r_n) n;
                        ret (simplifyf r_o''))) ->
      (forall r_n r_o,
         (r_o ≃ r_n) ->
         forall idx n,
           refineEquiv (oldObs idx r_o n)
                       (oldObs idx (concretize r_n) n)) ->
      refineADT
        (@Build_ADT Sig oldRep oldMuts oldObs)
        (@Build_ADT Sig newRep
                    (fun idx => simplifyMutatorMethod (oldMuts idx))
                    (fun idx => simplifyObserverMethod (oldObs idx))).
    Proof.
    econstructor 1 with
    (SiR := SiR); simpl; eauto.
    - unfold simplifyMutatorMethod; intros; eapply H; eauto.
    - unfold simplifyObserverMethod; intros; eapply H0; eauto.
  Qed.

  End SimplifyRep. *)

End BuildADTRefinements.

(* Honing tactic for refining the ADT representation which provides
   default observer and mutator implementations. *)

Tactic Notation "hone'" "representation" "using" constr(SiR') :=
    eapply SharpenStep;
    [eapply refineADT_BuildADT_Rep_default with (SiR := SiR') |
     compute [imap absMutDef absMutatorMethod
                   absObsDef absObserverMethod]; simpl ].

  Tactic Notation "hone'" "observer" constr(obsIdx) "using" constr(obsBod) :=
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
      | idtac]; cbv beta in *; simpl in * .

  Tactic Notation "hone'" "mutator" constr(mutIdx) "using" constr(mutBod) :=
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
      [eapply (@refineADT_BuildADT_ReplaceMutator
                 Rep' _ _ mutDefs obsDefs mutIdxB
                 (@Build_mutDef Rep'
                                {| mutID := mutIdx;
                                   mutDom := MutatorDom' mutIdxB
                                |}
                                mutBod
                                ))
      | idtac]; cbv beta in *; simpl in * .
