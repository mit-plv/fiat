Require Import List Common
        ADT.ADTSig ADT.Core
        ADTNotation.BuildADTSig ADTNotation.BuildADT
        Common.ilist ADTNotation.StringBound
        ADTRefinement.Core ADTRefinement.SetoidMorphisms
        ADTRefinement.GeneralRefinements
        ADTRefinement.GeneralBuildADTRefinements
        ADTRefinement.Refinements.HoneRepresentation
        ADTRefinement.BuildADTSetoidMorphisms.

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

  Definition absConsDef
             (Sig : consSig)
             (oldCons : @consDef oldRep Sig)
  : @consDef newRep Sig :=
    {| consBody := absConstructor AbsR (consBody oldCons) |}.

  Definition absMethDef
             (Sig : methSig)
             (oldCons : @methDef oldRep Sig)
  : @methDef newRep Sig :=
    {| methBody := absMethod AbsR (methBody oldCons) |}.

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
    eapply refineADT_Build_ADT_Rep with (AbsR := AbsR); eauto; intros.
    - unfold getConsDef.
      rewrite <- ith_Bounded_imap.
      unfold absConsDef, absConstructor, refineConstructor, refine; simpl; intros.
      inversion_by computes_to_inv; eauto.
    - unfold getMethDef.
      rewrite <- ith_Bounded_imap.
      unfold absMethDef, absMethod, refineMethod, refine; simpl; intros.
      inversion_by computes_to_inv; eauto.
      destruct (H0 _ H) as [or' [Comp_or [AbsR_or'' or''_eq] ] ];
        subst; repeat econstructor; eauto.
      destruct v; simpl in *; subst; econstructor.
  Qed.

  (* [refine_AbsMethod] can be applied when honing methods to
     get goals in a nicer form. *)

  Lemma refine_AbsMethod :
    forall Dom Cod oldMethod nr (d : Dom) refinedMeth,
      (forall or,
         AbsR or nr ->
         refine (or' <- oldMethod or d;
                 nr' <- { nr' | AbsR (fst or') nr'};
                 ret (nr', snd or'))
                (refinedMeth nr d))
      -> refine (absMethod (Cod := Cod) AbsR oldMethod nr d)
                (refinedMeth nr d).
  Proof.
    unfold absMethod, refine; intros * H v ComputesTo_v; econstructor;
    intros or AbsR_or.
    pose proof (H _ AbsR_or v ComputesTo_v); inversion_by computes_to_inv;
    subst.
    eexists; split; eauto.
  Qed.

  Lemma refine_AbsMethod' :
    forall Dom Cod oldMethod nr (d : Dom) refinedMeth,
      refine (absMethod (Cod := Cod) AbsR oldMethod nr d)
             (refinedMeth nr d)
      -> (forall or,
            AbsR or nr ->
            refine (or' <- oldMethod or d;
                    nr' <- { nr' | AbsR (fst or') nr'};
                    ret (nr', snd or'))
                   (refinedMeth nr d)).
  Proof.
    unfold absMethod, refine; intros * H or AbsR_or v ComputesTo_v.
    pose proof (H v ComputesTo_v); inversion_by computes_to_inv;
    subst.
    destruct (H0 _ AbsR_or); intuition; subst.
    repeat econstructor; eauto.
    rewrite H4; destruct v; econstructor.
  Qed.

  (* [refine_AbsConstructor] can be applied when honing constructors to
     get goals in a nicer form. *)

  Lemma refine_AbsConstructor :
    forall Dom oldConstructor (d : Dom) refinedConstructor,
      (refine (or' <- oldConstructor d;
               { nr' | AbsR or' nr'})
                (refinedConstructor d))
      -> refine (absConstructor AbsR oldConstructor d)
                (refinedConstructor d).
  Proof.
    unfold absConstructor, refine; intros * H v ComputesTo_v; econstructor.
    pose proof (H v ComputesTo_v); inversion_by computes_to_inv;
    subst.
    eexists; split; eauto.
  Qed.

  Lemma refine_AbsConstructor' :
    forall Dom oldConstructor (d : Dom) refinedConstructor,
      refine (absConstructor AbsR oldConstructor d)
             (refinedConstructor d)
      -> (refine (or' <- oldConstructor d;
                  { nr' | AbsR or' nr'})
                 (refinedConstructor d)).
  Proof.
    unfold absConstructor, refine; intros * H v ComputesTo_v.
    pose proof (H v ComputesTo_v); inversion_by computes_to_inv;
    subst.
    repeat econstructor; eauto.
  Qed.

End HoneRepresentation.

(* Honing tactic for refining the ADT representation which provides
   default method and constructor implementations. *)

Tactic Notation "hone" "representation" "using" open_constr(AbsR') :=
  eapply SharpenStep;
  [eapply refineADT_BuildADT_Rep_default with (AbsR := AbsR') |
   compute [imap absConsDef absMethDef]; simpl ].

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
    [ intros; simpl in *; set_evars; simpl in *;
      match goal with
        |  |- refine (absConstructor ?AbsR ?oldConstructor ?d)
                     (?H ?d) =>
           eapply (@refine_AbsConstructor _ _ AbsR _ oldConstructor)
        | _ => cbv [absConstructor]
      end
    |  cbv beta in *; simpl in *;
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
    [ intros;
      simpl in *; set_evars; simpl in *;
      match goal with
        |  |- refine (@absMethod ?oldRep ?newRep ?AbsR ?Dom ?Cod ?oldMethod ?nr ?d)
                     (?H ?nr ?d) => eapply (@refine_AbsMethod oldRep newRep AbsR Dom Cod oldMethod)
        | _ => cbv [absMethod]
      end; intros
    |
    cbv beta in *; simpl in *;
    cbv beta delta [replace_BoundedIndex replace_Index] in *;
    simpl in *].
