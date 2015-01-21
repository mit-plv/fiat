Require Import Coq.Lists.List Coq.Arith.Arith
        ADTSynthesis.Common ADTSynthesis.Computation ADTSynthesis.ADT.ADTSig ADTSynthesis.ADT.Core
        ADTSynthesis.ADT.ComputationalADT
        ADTSynthesis.Common.StringBound ADTSynthesis.Common.ilist ADTSynthesis.Common.IterateBoundedIndex
        ADTSynthesis.ADTNotation.BuildADTSig ADTSynthesis.ADTNotation.BuildADT
        ADTSynthesis.ADTNotation.BuildComputationalADT
        ADTSynthesis.ADTNotation.BuildADTReplaceMethods
        ADTSynthesis.ADTRefinement.Core ADTSynthesis.ADTRefinement.GeneralRefinements
        ADTSynthesis.ADTRefinement.SetoidMorphisms ADTSynthesis.ADTRefinement.BuildADTSetoidMorphisms.

(* Notation-friendly versions of the honing tactics in GeneralRefinements. *)

Section BuildADTRefinements.

  Require Import Coq.Strings.String.
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
  Defined.

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

  (* Notation-Friendly Lemmas for constructing an easily extractible
     ADT implementation. *)

  Definition Notation_Friendly_BuildMostlySharpenedcADT
             (consSigs : list consSig)
             (methSigs : list methSig)
             (DelegateSigs : list NamedADTSig)
             (rep : ilist (fun nadt  => cADT (namedADTSig nadt)) DelegateSigs
                    -> Type)
             (cConstructors :
                forall DelegateImpl : ilist (fun nadt  => cADT (namedADTSig nadt)) DelegateSigs,
                  ilist (fun Sig => cConstructorType (rep DelegateImpl) (consDom Sig)) consSigs)
             (cMethods :
                forall DelegateImpl : ilist (fun nadt  => cADT (namedADTSig nadt)) DelegateSigs,
                  ilist (fun Sig => cMethodType (rep DelegateImpl) (methDom Sig) (methCod Sig)) methSigs)
             (DelegateImpl : ilist (fun nadt => cADT (namedADTSig nadt))
                                    DelegateSigs)
  : cADT (BuildADTSig consSigs methSigs) :=
             @BuildcADT (rep DelegateImpl) consSigs methSigs
                        (imap _ (@Build_cConsDef (rep DelegateImpl)) (cConstructors DelegateImpl))
                        (imap _ (@Build_cMethDef (rep DelegateImpl)) (cMethods DelegateImpl)).

  Print refineMethod.

  Definition Notation_Friendly_FullySharpened_BuildMostlySharpenedcADT
             (RepT : Type)
             (consSigs : list consSig)
             (methSigs : list methSig)
             (consDefs : ilist (@consDef RepT) consSigs)
             (methDefs : ilist (@methDef RepT) methSigs)
             (DelegateSigs : list NamedADTSig)
             (rep : ilist (fun nadt  => cADT (namedADTSig nadt)) DelegateSigs
                    -> Type)
      (cConstructors :
         forall DelegateImpl : ilist (fun nadt  => cADT (namedADTSig nadt)) DelegateSigs,
           ilist (fun Sig => cConstructorType (rep DelegateImpl) (consDom Sig)) consSigs)
      (cMethods :
         forall DelegateImpl : ilist (fun nadt  => cADT (namedADTSig nadt)) DelegateSigs,
           ilist (fun Sig => cMethodType (rep DelegateImpl) (methDom Sig) (methCod Sig)) methSigs)
      (DelegateSpecs : ilist (fun nadt => ADT (namedADTSig nadt))
                             DelegateSigs)
      (cAbsR : forall DelegateImpl,
                 (forall idx,
                    refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                              (LiftcADT (ith_Bounded ADTSigname DelegateImpl idx)))
                 -> RepT -> rep DelegateImpl -> Prop)
    : (forall (DelegateImpl : ilist (fun nadt  => cADT (namedADTSig nadt)) DelegateSigs)
              (ValidImpl :
                 (forall idx,
                    refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                              (LiftcADT (ith_Bounded ADTSigname DelegateImpl idx)))),
         Iterate_Dep_Type_BoundedIndex
           (fun idx =>
              forall d ,
                exists r_o',
                cAbsR _ ValidImpl r_o' (ith_Bounded _ (cConstructors DelegateImpl) idx d) /\
                computes_to (getConsDef consDefs idx d) r_o'
                            ))
      -> (forall (DelegateImpl : ilist (fun nadt  => cADT (namedADTSig nadt)) DelegateSigs)
              (ValidImpl :
                 (forall idx,
                    refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                              (LiftcADT (ith_Bounded ADTSigname DelegateImpl idx)))),
            Iterate_Dep_Type_BoundedIndex
              (fun idx =>
                 forall d r_o r_n,
                   cAbsR _ ValidImpl r_o r_n ->
                   exists r_o',
                     cAbsR _ ValidImpl r_o' (fst (ith_Bounded _ (cMethods DelegateImpl) idx r_n d)) /\
                     computes_to (getMethDef methDefs idx r_o d)
                                 (r_o',
                                  (snd (ith_Bounded _ (cMethods DelegateImpl) idx r_n d)))))
      -> FullySharpenedUnderDelegates
           (BuildADT consDefs methDefs)
           {|
             Sharpened_DelegateSigs := DelegateSigs;
             Sharpened_Implementation := Notation_Friendly_BuildMostlySharpenedcADT rep
                                           cConstructors cMethods;
             Sharpened_DelegateSpecs := DelegateSpecs |}.
  Proof.
    intros * cConstructorsRefinesSpec cMethodsRefinesSpec
                                      DelegateImpl DelegateImplRefinesSpec.
    eapply (@refinesADT _ (BuildADT consDefs methDefs)
                        (LiftcADT (existT _ (rep DelegateImpl)
                                          {| pcConstructors := _;
                                             pcMethods := _|}))
                        (cAbsR DelegateImpl DelegateImplRefinesSpec)).
    - simpl; unfold ComputationalADT.cConstructors; simpl; intros.
      rewrite <- ith_Bounded_imap; eauto.
      destruct (Iterate_Dep_Type_BoundedIndex_equiv_1
              _ (cConstructorsRefinesSpec DelegateImpl DelegateImplRefinesSpec) idx d) as [c [AbsR_c computes_c]].
      unfold refine; intros; inversion_by computes_to_inv; subst.
      econstructor; eauto.
    - simpl; unfold ComputationalADT.cMethods; simpl; intros.
       rewrite <- ith_Bounded_imap.
       destruct (Iterate_Dep_Type_BoundedIndex_equiv_1
               _ (cMethodsRefinesSpec DelegateImpl DelegateImplRefinesSpec)
               idx d r_o r_n H) as [r_o' [AbsR_r_o' computes_r_o']].
       unfold refine; intros; inversion_by computes_to_inv; subst;
       econstructor; eauto.
       econstructor; eauto.
       case_eq ((ith_Bounded methID (cMethods DelegateImpl) idx r_n d));
         simpl; intros; eauto.
       rewrite H0; eauto.
  Qed.

  Definition Notation_Friendly_SharpenFully
    (RepT : Type)
    (consSigs : list consSig)
    (methSigs : list methSig)
    (consDefs : ilist (@consDef RepT) consSigs)
    (methDefs : ilist (@methDef RepT) methSigs)
    (DelegateSigs : list NamedADTSig)
    (rep : ilist (fun nadt  => cADT (namedADTSig nadt)) DelegateSigs
           -> Type)
    (cConstructors :
       forall DelegateImpl : ilist (fun nadt  => cADT (namedADTSig nadt)) DelegateSigs,
         ilist (fun Sig => cConstructorType (rep DelegateImpl) (consDom Sig)) consSigs)
    (cMethods :
       forall DelegateImpl : ilist (fun nadt  => cADT (namedADTSig nadt)) DelegateSigs,
         ilist (fun Sig => cMethodType (rep DelegateImpl) (methDom Sig) (methCod Sig)) methSigs)
    (DelegateSpecs : ilist (fun nadt => ADT (namedADTSig nadt))
                           DelegateSigs)
    (cAbsR : forall DelegateImpl,
               (forall idx,
                  refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                            (LiftcADT (ith_Bounded ADTSigname DelegateImpl idx)))
               -> RepT -> rep DelegateImpl -> Prop)
    (cConstructorsRefinesSpec :
       forall (DelegateImpl : ilist (fun nadt  => cADT (namedADTSig nadt)) DelegateSigs)
               (ValidImpl :
                  (forall idx,
                    refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                              (LiftcADT (ith_Bounded ADTSigname DelegateImpl idx)))),
         Iterate_Dep_Type_BoundedIndex
           (fun idx =>
              forall d ,
                exists r_o',
                cAbsR _ ValidImpl r_o' (ith_Bounded _ (cConstructors DelegateImpl) idx d) /\
                computes_to (getConsDef consDefs idx d) r_o'
           ))
  (cMethodsRefinesSpec :
     forall (DelegateImpl : ilist (fun nadt  => cADT (namedADTSig nadt)) DelegateSigs)
            (ValidImpl :
               (forall idx,
                  refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                            (LiftcADT (ith_Bounded ADTSigname DelegateImpl idx)))),
       Iterate_Dep_Type_BoundedIndex
         (fun idx =>
            forall d r_o r_n,
              cAbsR _ ValidImpl r_o r_n ->
              exists r_o',
                cAbsR _ ValidImpl r_o' (fst (ith_Bounded _ (cMethods DelegateImpl) idx r_n d)) /\
                computes_to (getMethDef methDefs idx r_o d)
                            (r_o',
                             (snd (ith_Bounded _ (cMethods DelegateImpl) idx r_n d)))))
  :  Sharpened (BuildADT consDefs methDefs)
    :=
      existT _ _
             (Notation_Friendly_FullySharpened_BuildMostlySharpenedcADT
                consDefs methDefs rep cConstructors cMethods
                DelegateSpecs cAbsR
                cConstructorsRefinesSpec cMethodsRefinesSpec).

End BuildADTRefinements.

Arguments Notation_Friendly_BuildMostlySharpenedcADT _ _ _ _ _ _ _ / .

Tactic Notation "extract" "implementation" "of" constr(adtImpl) "using" open_constr(delegateImpl) :=
  let Impl :=
      eval simpl in
  (Sharpened_Implementation (projT1 adtImpl) delegateImpl) in
      exact Impl.

(* A tactic for finishing a derivation. Probably needs a better name.*)
Tactic Notation "finish" "sharpening" constr(delegatees):=
  eexists; [ eapply reflexivityT
           | constructor 1 with (Sharpened_DelegateSpecs := delegatees); intros;
             split; simpl;
             match goal with
                 [|- forall idx : BoundedString, _] =>
                 let idx := fresh in
                 intro idx; pattern idx;
                 eapply Iterate_Ensemble_BoundedIndex_equiv;
                 unfold Iterate_Ensemble_BoundedIndex; simpl;
                 intuition;
                 repeat
                   (try simplify with monad laws;
                    first [constructor
                          | match goal with
                                |- context[if ?b then _ else _] =>
                                destruct b
                            end
                          ])
                    end ].

Tactic Notation "finish" "honing" :=
  subst_body;
  first [higher_order_2_reflexivity | higher_order_1_reflexivity ].

Ltac makeEvar T k :=
  let x := fresh in evar (x : T); let y := eval unfold x in x in clear x; k y.

Ltac ilist_of_evar C B As k :=
  match As with
    | nil => k (fun (c : C) => inil (B c))
    | cons ?a ?As' =>
      makeEvar (forall c, B c a)
               ltac:(fun b =>
                       ilist_of_evar
                         C B As'
                         ltac:(fun Bs' => k (fun c => icons a (b c) (Bs' c))))
  end.

Ltac FullySharpenEachMethod delegateSigs delegateSpecs :=
  match goal with
      |- Sharpened (@BuildADT ?Rep ?consSigs ?methSigs ?consDefs ?methDefs) =>
      ilist_of_evar
        (ilist ComputationalADT.cADT delegateSigs)
        (fun Sig => cMethodType Rep (methDom Sig) (methCod Sig))
        methSigs
        ltac:(fun cMeths => ilist_of_evar
                              (ilist ComputationalADT.cADT delegateSigs)
                              (fun Sig => cConstructorType Rep (consDom Sig))
                              consSigs
                              ltac:(fun cCons =>
                                      eapply Notation_Friendly_SharpenFully
                                      with (DelegateSpecs := delegateSpecs)
                                             (cConstructors := cCons)
                                             (cMethods := cMeths)));
        unfold Dep_Type_BoundedIndex_app_comm_cons; simpl;
        intros; repeat econstructor
  end.

Ltac BuildFullySharpenedConstructor :=
  intros;
  match goal with
      |- ret ?x ↝ ?Bod ?DelegateImpl ?d
      => let Bod' := eval pattern DelegateImpl, d in x in
                                                      match Bod' with
                                                        | (?Bod'' _ _) =>
                                                          unify Bod Bod''; constructor
                                                      end
  end.

Lemma SharpenIfComputesTo {A} :
  forall (cond : bool) (cT cE : Comp A) vT vE,
    cT ↝ vT
    -> cE ↝ vE
    -> (if cond then cT else cE) ↝ if cond then vT else vE.
Proof.
  destruct cond; eauto.
Qed.

Lemma ComputesToLiftcADT {Sig}
: forall (cadt : cADT Sig) idx r_n d,
    Methods (LiftcADT cadt) idx r_n d ↝ cMethods cadt idx r_n d.
Proof.
  unfold LiftcADT; simpl; intros.
  simpl; constructor.
Qed.

Lemma refineCallMethod {Sig}
: forall (adt : ADT Sig) (cadt : cADT Sig)
         (refineA : refineADT adt (LiftcADT cadt))  idx r_o r_n d,
    refine (r_o' <- Methods adt idx r_o d;
            r_n' <- Pick (fun r_n' : cRep cadt => AbsR refineA (fst r_o') r_n');
            ret (r_n', snd r_o'))
           (Methods (LiftcADT cadt) idx r_n d)
    -> exists r_o',
         refine (Methods adt idx r_o d) (ret r_o') /\
         refine {r_n' | AbsR refineA (fst r_o') r_n'}
                (ret (fst (cMethods cadt idx r_n d))) /\
         snd r_o' = snd (cMethods cadt idx r_n d)
         /\ AbsR refineA (fst r_o') (fst (cMethods cadt idx r_n d)).
Proof.
  intros.
  pose proof (H _ (ComputesToLiftcADT cadt idx r_n d));
    inversion_by computes_to_inv; subst.
  exists x; intuition.
  intros c Comp_v; inversion_by computes_to_inv; subst; auto.
  rewrite <- H3; refine pick val x0; simpl; eauto.
  reflexivity.
  rewrite <- H3; eauto.
  rewrite <- H3; eauto.
Qed.

(* *)
Ltac ilist_of_evar1 C B As k :=
  match As with
    | nil => k (fun c : C => inil B)
    | cons ?a ?As' =>
      makeEvar (forall c : C, B a)
               ltac:(fun b =>
                       ilist_of_evar1
                         C B As'
                         ltac:(fun Bs' => k (fun c : C => icons a (b c) (Bs' c))))
  end.

Ltac FullySharpenEachMethod1 delegateSigs delegateSpecs :=
    match goal with
      |- Sharpened (@BuildADT ?Rep ?consSigs ?methSigs ?consDefs ?methDefs) =>
      ilist_of_evar1
        (ilist (fun nadt => ComputationalADT.cADT (namedADTSig nadt)) delegateSigs)
        (fun Sig => ComputationalADT.cMethodType Rep (methDom Sig) (methCod Sig))
        methSigs
        ltac:(fun cMeths =>
                ilist_of_evar1
                  (ilist (fun nadt => ComputationalADT.cADT (namedADTSig nadt)) delegateSigs)
                  (fun Sig => ComputationalADT.cConstructorType Rep (consDom Sig))
                  consSigs
                  ltac:(fun cCons =>
                          eapply
                            (@Notation_Friendly_SharpenFully
                               Rep
                               consSigs
                               methSigs
                               consDefs
                               methDefs
                               delegateSigs
                               (fun _ => Rep)
                               cCons
                               cMeths
                               delegateSpecs
                               (fun (DelegateImpl : ilist
                                                      (fun nadt : NamedADTSig =>
                                                         ComputationalADT.cADT
                                                           (namedADTSig nadt)) _)
                                    (ValidImpl :
                                       (forall idx : BoundedIndex (map ADTSigname []),
                                          refineADT
                                            (ith_Bounded ADTSigname
                                                         (inil
                                                            (fun nadt : NamedADTSig => ADT (namedADTSig nadt)))
                                                         idx)
                                            (ComputationalADT.LiftcADT
                                               (ith_Bounded ADTSigname DelegateImpl idx)))) => @eq _))));
        unfold ADTSynthesis.Common.IterateBoundedIndex.Dep_Type_BoundedIndex_app_comm_cons; simpl;
        intuition; intros; subst
  end.

  Ltac make_computational_constructor :=
    let x := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(x) end in
    let f := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(f) end in
    let a := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(a) end in
    let b := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(b) end in
    let x' := (eval pattern a, b in x) in
    let f' := match x' with ?f' _ _ => constr:(f') end in
    unify f f';
      cbv beta;
      solve [apply reflexivity].

  Ltac make_computational_method' :=
    let x := match goal with |- ?R (ret ?x) (ret (?f ?a ?b ?c)) => constr:(x) end in
    let f := match goal with |- ?R (ret ?x) (ret (?f ?a ?b ?c)) => constr:(f) end in
    let a := match goal with |- ?R (ret ?x) (ret (?f ?a ?b ?c)) => constr:(a) end in
    let b := match goal with |- ?R (ret ?x) (ret (?f ?a ?b ?c)) => constr:(b) end in
    let c := match goal with |- ?R (ret ?x) (ret (?f ?a ?b ?c)) => constr:(c) end in
    let x' := (eval pattern a, b, c in x) in
    let f' := match x' with ?f' _ _ _ => constr:(f') end in
    unify f f';
      cbv beta;
      solve [apply reflexivity].

  Ltac make_computational_method_pair_rep :=
    let x := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(x) end in
    let f := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(f) end in
    let a := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(a) end in
    let b := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(b) end in
    let b' := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(b') end in
    let c := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(c) end in
    let x' := (eval pattern a, b, b', c in x) in
    let f' := match x' with ?f' _ _ _ _ => constr:(fun i a => f' i (fst a) (snd a)) end in
    unify f f';
      cbv beta;
      solve [apply reflexivity].

  Ltac make_computational_method_pair_args :=
    let x := match goal with |- ?R (ret ?x) (ret (?f ?a ?b (?c, ?c'))) => constr:(x) end in
    let f := match goal with |- ?R (ret ?x) (ret (?f ?a ?b (?c, ?c'))) => constr:(f) end in
    let a := match goal with |- ?R (ret ?x) (ret (?f ?a ?b (?c, ?c'))) => constr:(a) end in
    let b := match goal with |- ?R (ret ?x) (ret (?f ?a ?b (?c, ?c'))) => constr:(b) end in
    let c := match goal with |- ?R (ret ?x) (ret (?f ?a ?b (?c, ?c'))) => constr:(c) end in
    let c' := match goal with |- ?R (ret ?x) (ret (?f ?a ?b (?c, ?c'))) => constr:(c') end in
    let x' := (eval pattern a, b, c, c' in x) in
    let f' := match x' with ?f' _ _ _ _ => constr:(fun i a b => f' i a (fst b) (snd b)) end in
    unify f f';
      cbv beta;
      solve [apply reflexivity].

  Ltac make_computational_method :=
    match goal with
      | |- ?R (ret ?x) (ret (?f ?a ?b (?c, ?c'))) => make_computational_method_pair_args
      | |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => make_computational_method_pair_rep
      | |- ?R (ret ?x) (ret (?f ?a ?b ?c)) => make_computational_method'
    end.

Lemma refineIfret {A} :
  forall (cond : bool) (a a' : A),
    refine (if cond then ret a else ret a')
           (ret (if cond then a else a')).
Proof.
  destruct cond; reflexivity.
Qed.
