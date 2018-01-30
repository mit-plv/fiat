Require Import Coq.Lists.List Coq.Arith.Arith
        Fiat.Common Fiat.Computation Fiat.ADT.ADTSig Fiat.ADT.Core
        Fiat.ADT.ComputationalADT
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.IterateBoundedIndex
        Fiat.ADTNotation.BuildADTSig Fiat.ADTNotation.BuildADT
        Fiat.ADTNotation.BuildComputationalADT
        Fiat.ADTNotation.BuildADTReplaceMethods
        Fiat.ADTRefinement.Core
        Fiat.ADTRefinement.GeneralRefinements
        Fiat.ADTRefinement.SetoidMorphisms
        Fiat.ADTRefinement.BuildADTSetoidMorphisms.

(* Notation-friendly versions of the honing tactics in GeneralRefinements. *)

Section BuildADTRefinements.

  Require Import Coq.Strings.String.
  Local Hint Resolve string_dec.

  Lemma refineADT_BuildADT_ReplaceConstructor
        (Rep : Type)
        (AbsR : Rep -> Rep -> Prop)
        {n n'}
        (consSigs : Vector.t consSig n)
        (methSigs : Vector.t methSig n')
        (consDefs : ilist (B := @consDef Rep) consSigs)
        (methDefs : ilist (B := @methDef Rep) methSigs)
        (idx : @Fin.t n)
        (newDef : consDef (Vector.nth consSigs idx))
  :
    (forall consIdx,
       refineConstructor AbsR (getConsDef consDefs consIdx) (getConsDef consDefs consIdx))
    -> (forall methIdx,
          refineMethod AbsR (getMethDef methDefs methIdx) (getMethDef methDefs methIdx))
    -> refineConstructor AbsR
                         (consBody (ith consDefs idx ))
                         (consBody newDef)
    -> refineADT
         (BuildADT consDefs methDefs)
         (ADTReplaceConsDef consDefs methDefs idx newDef).
  Proof.
    intros; eapply refineADT_BuildADT_Rep with (AbsR := AbsR); eauto.
    intros; unfold getConsDef.
    unfold replaceConsDef.
    destruct (fin_eq_dec consIdx idx); subst.
    rewrite ith_replace_Index_eq; eauto.
    rewrite ith_replace_Index_neq; eauto.
  Qed.

  Corollary SharpenStep_BuildADT_ReplaceConstructor_eq
            (Rep : Type)
            {n n'}
            (consSigs : Vector.t consSig n)
            (methSigs : Vector.t methSig n')
            (consDefs : ilist (B := @consDef Rep) consSigs)
            (methDefs : ilist (B := @methDef Rep) methSigs)
            (idx : @Fin.t n)
            (newDef : consDef (Vector.nth consSigs idx))
            adt''
    :
    (let H := consBody newDef in refineConstructor eq (consBody (ith consDefs idx)) H)
    -> refineADT (ADTReplaceConsDef consDefs methDefs idx newDef) adt''
    -> refineADT (BuildADT consDefs methDefs) adt''.
  Proof.
    intros; eapply SharpenStep; try exact X.
    eapply refineADT_BuildADT_ReplaceConstructor with (AbsR := eq);
    simpl; unfold refine; intros; subst; eauto.
    - reflexivity.
    - reflexivity.
  Qed.

  Corollary FullySharpenStep_BuildADT_ReplaceConstructor_eq
            (Rep : Type)
            {n n'}
            (consSigs : Vector.t consSig n)
            (methSigs : Vector.t methSig n')
            (consDefs : ilist (B := @consDef Rep) consSigs)
            (methDefs : ilist (B := @methDef Rep) methSigs)
            (idx : @Fin.t n)
            (newDef : consDef (Vector.nth consSigs idx))
            adt''
    :
      (let H := consBody newDef in refineConstructor eq (consBody (ith consDefs idx)) H)
    -> FullySharpenedUnderDelegates (ADTReplaceConsDef consDefs methDefs idx newDef) adt''
    -> FullySharpenedUnderDelegates (BuildADT consDefs methDefs) adt''.
  Proof.
    intros; eapply FullySharpenStep; try exact X.
    eapply refineADT_BuildADT_ReplaceConstructor with (AbsR := eq);
    simpl; unfold refine; intros; subst; eauto.
    - reflexivity.
    - reflexivity.
  Qed.

  (*Corollary SharpenStep_BuildADT_ReplaceConstructor_eq
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
    apply refineADT_BuildADT_ReplaceConstructor_eq; eauto.
  Defined. *)

  (*

Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = f_equal f (eissect x)
}.

Arguments eisretr {A B} f {_} _.
Arguments eissect {A B} f {_} _.
Arguments eisadj {A B} f {_} _.

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : forall x, f x = g x
  := fun x => match h with eq_refl => eq_refl end.

Class Funext :=
  { isequiv_apD10 :> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }.

(* We'll just assume functional extensionality for now. *)
Axiom IsHProp : Type -> Type.
Existing Class IsHProp.
Instance : forall A, IsHProp (IsHProp A).
Admitted.

Axiom allpath_hprop : forall `{H : IsHProp A} (x y : A), x = y.
Axiom hprop_allpath : forall (A : Type), (forall (x y : A), x = y) -> IsHProp A.

Global Instance trunc_forall `{P : A -> Type} `{forall a, IsHProp (P a)}
  : IsHProp (forall a, P a) | 100.
Admitted.

Instance trunc_prod `{IsHProp A, IsHProp B} : IsHProp (A * B).
Admitted.

Record hProp := hp { hproptype :> Type ; isp : IsHProp hproptype}.
Existing Instance isp.

Instance : forall A : hProp, IsHProp A.
Admitted.

Lemma path_sig_hprop {A} {P : A -> Prop} `{forall x : A, IsHProp (P x)}
      (x y : sig P)
: proj1_sig x = proj1_sig y -> x = y.
Proof.
  destruct_head sig; intros; subst; f_equal; apply allpath_hprop.
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
  Qed. *)

  Lemma refineADT_BuildADT_ReplaceMethod
        (Rep : Type)
        {n n'}
        (consSigs : Vector.t consSig n)
        (methSigs : Vector.t methSig n')
        (consDefs : ilist (B := @consDef Rep) consSigs)
        (methDefs : ilist (B := @methDef Rep) methSigs)
        (idx : @Fin.t n')
        (newDef : methDef (Vector.nth methSigs idx))
        AbsR
        (AbsR_reflexive_constructor :
           forall consIdx,
             refineConstructor AbsR (getConsDef consDefs consIdx) (getConsDef consDefs consIdx))
        (AbsR_reflexive_method :
           forall methIdx,
             refineMethod AbsR (getMethDef methDefs methIdx) (getMethDef methDefs methIdx))
  : refineMethod AbsR
                 (methBody (ith methDefs idx))
                 (methBody newDef)
    -> refineADT
         (BuildADT consDefs methDefs)
         (ADTReplaceMethDef consDefs methDefs idx newDef).
  Proof.
    intros; eapply refineADT_BuildADT_Rep with (AbsR := AbsR); trivial.
    intros; unfold getMethDef.
    unfold replaceMethDef.
    destruct (fin_eq_dec methIdx idx); subst.
    rewrite ith_replace_Index_eq; eauto.
    rewrite ith_replace_Index_neq; eauto.
  Qed.

  Corollary SharpenStep_BuildADT_ReplaceMethod_eq
        (Rep : Type)
        {n n'}
        (consSigs : Vector.t consSig n)
        (methSigs : Vector.t methSig n')
        (consDefs : ilist (B := @consDef Rep) consSigs)
        (methDefs : ilist (B := @methDef Rep) methSigs)
        (idx : @Fin.t n')
        (newDef : methDef (Vector.nth methSigs idx))
        adt''
    :
      (let H := methBody newDef in refineMethod eq (methBody (ith methDefs idx)) newDef)
      -> refineADT (ADTReplaceMethDef consDefs methDefs idx newDef) adt''
      -> refineADT (BuildADT consDefs methDefs) adt''.
  Proof.
    intros; eapply SharpenStep.
    eapply refineADT_BuildADT_ReplaceMethod with (AbsR := eq);
    simpl; unfold refine; intros; subst; eauto; reflexivity.
    exact X.
  Qed.

  Lemma FullySharpenStep_BuildADT_ReplaceMethod_eq
        (Rep : Type)
        {n n'}
        (consSigs : Vector.t consSig n)
        (methSigs : Vector.t methSig n')
        (consDefs : ilist (B := @consDef Rep) consSigs)
        (methDefs : ilist (B := @methDef Rep) methSigs)
        (idx : @Fin.t n')
        (newDef : methDef (Vector.nth methSigs idx))
        adt''
    :
      (let H := methBody newDef in refineMethod eq (methBody (ith methDefs idx)) newDef)
      -> FullySharpenedUnderDelegates
           (ADTReplaceMethDef consDefs methDefs idx newDef)
           adt''
      -> FullySharpenedUnderDelegates
           (BuildADT consDefs methDefs)
           adt''.
  Proof.
    intros; eapply FullySharpenStep.
    eapply refineADT_BuildADT_ReplaceMethod with (AbsR := eq);
    simpl; unfold refine; intros; subst; eauto; reflexivity.
    exact X.
  Qed.

  (*Corollary SharpenStep_BuildADT_ReplaceMethod_eq
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
    intros; eapply refineADT_BuildADT_ReplaceMethod_eq; eauto.
  Defined. *)

  (*Lemma refineADT_BuildADT_ReplaceMethod_sigma
        (RepT : Type)
        (RepInv : RepT -> Prop)
        {n n'}
        (consSigs : Vector.t consSig n)
        (methSigs : Vector.t methSig n')
        (consDefs : ilist (B := @consDef (sig RepInv)) consSigs)
        (methDefs : ilist (B := @methDef (sig RepInv)) methSigs)
        (idx : @Fin.t n')
        (newDef : methDef (Vector.nth methSigs idx))
        (AbsR_reflexive_method :
           forall methIdx,
             refineMethod (fun x y => proj1_sig x = proj1_sig y)
                          (getMethDef methDefs methIdx)
                          (getMethDef methDefs methIdx))
  : refineMethod (fun x y => proj1_sig x = proj1_sig y)
                 (methBody (ith methDefs idx))
                 (methBody newDef)
    -> refineADT
         (BuildADT consDefs methDefs)
         (ADTReplaceMethDef consDefs methDefs idx newDef).
  Proof.
    intro H'.
    eapply refineADT_BuildADT_ReplaceMethod with
    (AbsR := fun r_o r_n => proj1_sig r_o = proj1_sig r_n); eauto;
    simpl in *; intros; subst; eauto.
    computes_to_econstructor; eauto.
  Qed. *)

  (* Notation-Friendly Lemmas for constructing an easily extractible
     ADT implementation. *)

  Definition Notation_Friendly_BuildMostlySharpenedcADT
             {n n'}
             {consSigs : Vector.t consSig n}
             {methSigs : Vector.t methSig n'}
             (DelegateIDs : nat)
             (DelegateSigs : Fin.t DelegateIDs -> ADTSig)
             (rep : (Fin.t DelegateIDs -> Type) -> Type)
             (cConstructors :
                forall
                  (DelegateReps : Fin.t DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx)),
                  ilist
                    (B := fun Sig : consSig =>
                            ComputationalADT.cConstructorType (rep DelegateReps) (consDom Sig))
                    consSigs)
             (cMethods :
                forall
                  (DelegateReps : Fin.t DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx)),
                  ilist
                    (B := fun Sig : methSig =>
                       ComputationalADT.cMethodType (rep DelegateReps)
                                                    (methDom Sig) (methCod Sig)) methSigs)
             (DelegateReps : Fin.t DelegateIDs -> Type)
             (DelegateImpls : forall idx,
                                ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
  : ComputationalADT.cADT (BuildADTSig consSigs methSigs) :=
    BuildcADT
      (imap (Build_cConsDef (rep DelegateReps))
            (cConstructors DelegateReps DelegateImpls))
      (imap (Build_cMethDef (Rep:=rep DelegateReps))
            (cMethods DelegateReps DelegateImpls)).

  Definition Notation_Friendly_FullySharpened_BuildMostlySharpenedcADT
             (RepT : Type)
             {n n'}
             {consSigs : Vector.t consSig n}
             {methSigs : Vector.t methSig n'}
             (consDefs : ilist consSigs)
             (methDefs : ilist methSigs)
             (DelegateIDs : nat)
             (DelegateSigs : Fin.t DelegateIDs -> ADTSig)
             (rep : (Fin.t DelegateIDs -> Type) -> Type)
             (cConstructors :
                forall
                  (DelegateReps : Fin.t DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx)),
                  ilist
                    (B := fun Sig : consSig =>
                       ComputationalADT.cConstructorType
                         (rep DelegateReps) (consDom Sig)) consSigs)
             (cMethods :
                forall
                  (DelegateReps : Fin.t DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx)),
                  ilist
                    (B := fun Sig : methSig =>
                       ComputationalADT.cMethodType
                         (rep DelegateReps) (methDom Sig)
                         (methCod Sig)) methSigs)
             (DelegateSpecs : forall idx, ADT (DelegateSigs idx))
             (cAbsR :
                forall
                  (DelegateReps : Fin.t DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                  (ValidImpls
                   : forall idx : Fin.t DelegateIDs,
                       refineADT (DelegateSpecs idx)
                                 (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                  RepT -> rep DelegateReps -> Prop)
             (cConstructorsRefinesSpec : forall
                                           (DelegateReps : Fin.t DelegateIDs -> Type)
                                           (DelegateImpls : forall idx,
                                                              ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                           (ValidImpls
                                            : forall idx : Fin.t DelegateIDs,
                                                refineADT (DelegateSpecs idx)
                                                          (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                 Iterate_Dep_Type_BoundedIndex
                   (fun idx  =>
                      @refineConstructor
                        (RepT) (rep DelegateReps) (cAbsR _ _ ValidImpls)
                        (consDom (Vector.nth consSigs idx))
                        (getConsDef consDefs idx)
                        (LiftcConstructor _ _ (ith (cConstructors DelegateReps DelegateImpls) idx))))
             (cMethodsRefinesSpec : forall
                                      (DelegateReps : Fin.t DelegateIDs -> Type)
                                      (DelegateImpls : forall idx,
                                                         ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                      (ValidImpls
                                       : forall idx : Fin.t DelegateIDs,
                                           refineADT (DelegateSpecs idx)
                                                     (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                                      Iterate_Dep_Type_BoundedIndex
                                        (fun idx =>
                                           @refineMethod
                                             RepT (rep DelegateReps)
                                             (cAbsR _ _ ValidImpls)
                                             (methDom (Vector.nth methSigs idx))
                                             (methCod (Vector.nth methSigs idx))
                                             (getMethDef methDefs idx)
                                             (LiftcMethod (ith (cMethods DelegateReps DelegateImpls) idx))))
  : FullySharpenedUnderDelegates (BuildADT consDefs methDefs)
                                 {|
                                   Sharpened_DelegateSigs := DelegateSigs;
                                   Sharpened_Implementation := Notation_Friendly_BuildMostlySharpenedcADT
                                                                 _ rep cConstructors cMethods;
                                   Sharpened_DelegateSpecs := DelegateSpecs |}.
  Proof.
    intros * DelegateReps DelegateImpls DelegateImplRefinesSpec.
    eapply (@refinesADT _ (BuildADT consDefs methDefs)
                        (LiftcADT (existT _ (rep DelegateReps)
                                          {| pcConstructors := _;
                                             pcMethods := _|}))
                        (cAbsR DelegateReps DelegateImpls DelegateImplRefinesSpec)).
    - simpl; unfold ComputationalADT.cConstructors; simpl; intros.
      rewrite <- ith_imap; eauto.
      apply (Lookup_Iterate_Dep_Type
                 _ (cConstructorsRefinesSpec DelegateReps DelegateImpls DelegateImplRefinesSpec) idx).
        (*as [c [AbsR_c computes_c] ].
      unfold refine; intros; inversion_by computes_to_inv; subst.
      econstructor; eauto. *)
    - simpl; unfold ComputationalADT.cMethods; simpl; intros.
      rewrite <- ith_imap.
      apply (Lookup_Iterate_Dep_Type
                  _ (cMethodsRefinesSpec DelegateReps DelegateImpls DelegateImplRefinesSpec)).
        (* as [r_o' [AbsR_r_o' computes_r_o'] ].
      unfold refine; intros; inversion_by computes_to_inv; subst;
      econstructor; eauto.
      econstructor; eauto.
      case_eq ((ith_Bounded methID (cMethods DelegateReps DelegateImpls) idx r_n d));
        simpl; intros; eauto.
      rewrite H0; eauto. *)
  Qed.

  Definition Notation_Friendly_SharpenFully'
             (RepT : Type)
             {n n'}
             (consSigs : Vector.t consSig n)
             (methSigs : Vector.t methSig n')
             (consDefs : ilist consSigs)
             (methDefs : ilist methSigs)
             (DelegateIDs : nat)
             (DelegateSigs : Fin.t DelegateIDs -> ADTSig)
             (rep : (Fin.t DelegateIDs -> Type) -> Type)
             (cConstructors :
                forall
                  (DelegateReps : Fin.t DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx)),
                  ilist
                    (B := fun Sig : consSig =>
                       ComputationalADT.cConstructorType
                         (rep DelegateReps) (consDom Sig)) consSigs)
             (cMethods :
                forall
                  (DelegateReps : Fin.t DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx)),
                  ilist
                    (B := fun Sig : methSig =>
                       ComputationalADT.cMethodType
                         (rep DelegateReps) (methDom Sig)
                         (methCod Sig)) methSigs)
             (DelegateSpecs : forall idx, ADT (DelegateSigs idx))
             (cAbsR :
                forall
                  (DelegateReps : Fin.t DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                  (ValidImpls
                   : forall idx : Fin.t DelegateIDs,
                       refineADT (DelegateSpecs idx)
                                 (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                  RepT -> rep DelegateReps -> Prop)
             (cConstructorsRefinesSpec : forall
                                           (DelegateReps : Fin.t DelegateIDs -> Type)
                                           (DelegateImpls : forall idx,
                                                              ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                           (ValidImpls
                                            : forall idx : Fin.t DelegateIDs,
                                                refineADT (DelegateSpecs idx)
                                                          (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                                           Iterate_Dep_Type_BoundedIndex
                                             (fun idx  =>
                                                @refineConstructor
                                                  (RepT) (rep DelegateReps) (cAbsR _ _ ValidImpls)
                                                  (consDom (Vector.nth consSigs idx))
                                                  (getConsDef consDefs idx)
                                                  (LiftcConstructor _ _ (ith (cConstructors DelegateReps DelegateImpls) idx))))
             (cMethodsRefinesSpec : forall
                                      (DelegateReps : Fin.t DelegateIDs -> Type)
                                      (DelegateImpls : forall idx,
                                                         ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                      (ValidImpls
                                       : forall idx : Fin.t DelegateIDs,
                                           refineADT (DelegateSpecs idx)
                                                     (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                                      Iterate_Dep_Type_BoundedIndex
                                        (fun idx  =>
                                           @refineMethod
                                             RepT (rep DelegateReps)
                                             (cAbsR _ _ ValidImpls)
                                             (methDom (Vector.nth methSigs idx))
                                             (methCod (Vector.nth methSigs idx))
                                             (getMethDef methDefs idx)
                                             (LiftcMethod (ith (cMethods DelegateReps DelegateImpls) idx ))))
  : FullySharpenedUnderDelegates
      (BuildADT consDefs methDefs)
      {|
        Sharpened_DelegateSigs := DelegateSigs;
        Sharpened_Implementation := Notation_Friendly_BuildMostlySharpenedcADT _ rep
                                                                               cConstructors cMethods;
        Sharpened_DelegateSpecs := DelegateSpecs |} :=
                                 (Notation_Friendly_FullySharpened_BuildMostlySharpenedcADT consDefs
                                                                      methDefs _ rep cConstructors cMethods DelegateSpecs cAbsR
                                                                      cConstructorsRefinesSpec cMethodsRefinesSpec).

  Record NamedDelegatee :=
    { delegateeSig : ADTSig;
      delegateeRep : Type }.

  Definition Build_NamedDelegatees
           {n}
           (DelegateSigs : Vector.t ADTSig n)
           (DelegateReps : Vector.t Type n)
  : Vector.t NamedDelegatee n.
      pattern n, DelegateReps, DelegateSigs.
      match goal with
        |- ?P n DelegateReps DelegateSigs =>
        simpl; refine (Vector.rect2
                         P
                         (Vector.nil _)
                         (fun n DelegateReps DelegateSigs Delegatees Rep Sig =>
                            (Vector.cons
                               _
                               {| delegateeSig := Sig; delegateeRep := Rep |}
                               _ Delegatees))
                         DelegateReps DelegateSigs)
      end.
  Defined.

  Definition Notation_Friendly_SharpenFully
             (RepT : Type)
             {m n n'}
             (consSigs : Vector.t consSig n)
             (methSigs : Vector.t methSig n')
             (consDefs : ilist consSigs)
             (methDefs : ilist methSigs)
             (DelegateSigs' : Vector.t ADTSig m)
             (DelegateReps' : Vector.t Type m)
             (Delegatees := Build_NamedDelegatees DelegateSigs' DelegateReps')
             (DelegateIDs := m)
             (DelegateSigs := fun idx =>
                                delegateeSig (Vector.nth Delegatees idx))
             (DelegateReps := fun idx =>
                                delegateeRep (Vector.nth Delegatees idx))
             (rep : (Fin.t DelegateIDs -> Type) -> Type)
             (cConstructors :
                forall
                  (DelegateReps : Fin.t DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx)),
                  ilist
                    (B := fun Sig : consSig =>
                       ComputationalADT.cConstructorType
                         (rep DelegateReps) (consDom Sig)) consSigs)
             (cMethods :
                forall
                  (DelegateReps : Fin.t DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx)),
                  ilist
                    (B := fun Sig : methSig =>
                       ComputationalADT.cMethodType
                         (rep DelegateReps) (methDom Sig)
                         (methCod Sig)) methSigs)
             (DelegateSpecs' : ilist (B := fun nadt => ADT (delegateeSig nadt)) Delegatees )
             (DelegateSpecs := ith DelegateSpecs')
             (cAbsR :
                forall
                  (DelegateReps : Fin.t DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                  (ValidImpls
                   : forall idx : Fin.t DelegateIDs,
                       refineADT (DelegateSpecs idx)
                                 (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                  RepT -> rep DelegateReps -> Prop)
             (cConstructorsRefinesSpec : forall
                                           (DelegateReps : Fin.t DelegateIDs -> Type)
                                           (DelegateImpls : forall idx,
                                                              ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                           (ValidImpls
                                            : forall idx : Fin.t DelegateIDs,
                                                refineADT (DelegateSpecs idx)
                                                          (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                                           Iterate_Dep_Type_BoundedIndex
                                             (fun idx =>
                                                @refineConstructor
                                                  (RepT) (rep DelegateReps) (cAbsR _ _ ValidImpls)
                                                  (consDom (Vector.nth consSigs idx))
                                                  (getConsDef consDefs idx)
                                                  (LiftcConstructor _ _ (ith (cConstructors DelegateReps DelegateImpls) idx))))
             (cMethodsRefinesSpec : forall
                                      (DelegateReps : Fin.t DelegateIDs -> Type)
                                      (DelegateImpls : forall idx,
                                                         ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                      (ValidImpls
                                       : forall idx : Fin.t DelegateIDs,
                                           refineADT (DelegateSpecs idx)
                                                     (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                                      Iterate_Dep_Type_BoundedIndex
                                        (fun idx =>
                                           @refineMethod
                                             RepT (rep DelegateReps)
                                             (cAbsR _ _ ValidImpls)
                                             (methDom (Vector.nth methSigs idx))
                                             (methCod (Vector.nth methSigs idx))
                                             (getMethDef methDefs idx)
                                             (LiftcMethod (ith (cMethods DelegateReps DelegateImpls) idx))))
  : FullySharpenedUnderDelegates
      (BuildADT consDefs methDefs)
      {|
        Sharpened_DelegateSigs := DelegateSigs;
        Sharpened_Implementation := Notation_Friendly_BuildMostlySharpenedcADT _ rep
                                                                               cConstructors cMethods;
        Sharpened_DelegateSpecs := DelegateSpecs |}.
      refine (Notation_Friendly_FullySharpened_BuildMostlySharpenedcADT consDefs
                                                                      methDefs _ rep cConstructors cMethods DelegateSpecs cAbsR
                                                                      cConstructorsRefinesSpec cMethodsRefinesSpec).
  Defined.

End BuildADTRefinements.

Arguments Notation_Friendly_BuildMostlySharpenedcADT _ _ _ _ _ _ _ _ _ _ _  / .

Ltac extract_delegate_free_impl :=
  cbv beta; simpl;
    match goal with
        |- forall idx : Fin.t 0,
             refineADT
               (ith inil idx)
               (ComputationalADT.LiftcADT
                  (existT
                     (ComputationalADT.pcADT
                        (delegateeSig _))
                     (?DelegateReps idx) (?DelegateSpecs idx))) =>
        unify DelegateReps (fun idx : Fin.t 0 => False);
          let P' := match type of DelegateSpecs with
                    | forall idx, @?P' idx => P'
                    end in
          unify DelegateSpecs (fun idx : Fin.t 0 => Fin.case0 P' idx);
            apply Fin.case0
          end.

Tactic Notation "extract" "delegate-free" "implementation" :=
  extract_delegate_free_impl.

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
  repeat match goal with
  | |- ?R _ (?H _ _ _ _ _) =>
    subst H
  | |- ?R _ (?H _ _ _ _ ) =>
    subst H
  | |- ?R _ (?H _ _ _ ) =>
    subst H
  | |- ?R _ (?H _ _) =>
    subst H
  | |- ?R _ (?H _ ) =>
    subst H
  | |- ?R _ (?H ) =>
    subst H
  end; higher_order_reflexivity.

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

(*Ltac FullySharpenEachMethod delegateSigs delegateSpecs :=
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
        simpl;
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
  end. *)

Lemma SharpenIfComputesTo {A} :
  forall (cond : bool) (cT cE : Comp A) vT vE,
    cT ↝ vT
    -> cE ↝ vE
    -> (if cond then cT else cE) ↝ if cond then vT else vE.
Proof.
  destruct cond; eauto.
Qed.

(*Lemma ComputesToLiftcADT {Sig}
: forall (cadt : cADT Sig) idx r_n d,
    Methods (LiftcADT cadt) idx r_n d ↝ cMethods cadt idx r_n d.
Proof.
  unfold LiftcADT; simpl; intros.
  simpl; constructor.
Qed. *)

(*Lemma refineCallMethod {Sig}
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
    computes_to_inv; subst.
  eexists v ; intuition.
  intros c Comp_v; computes_to_inv; subst; auto.
  rewrite <- H0''; refine pick val _; simpl; eauto.
  reflexivity.
  rewrite <- H0''; eauto.
  rewrite <- H0''; eauto.
Qed. *)

Ltac ilist_of_evar_dep n C D B As k :=
  match n with
  | 0 => k (fun (c : C) (d : D c) => @inil _ B)
  | S ?n' =>
    makeEvar (forall (c : C) (d : D c), B (Vector.hd As))
             ltac:(fun b =>
                           ilist_of_evar_dep n'
                                             C D B (Vector.tl As)
                                             ltac:(fun Bs' => k (fun (c : C) (d : D c) => icons (a := Vector.hd As) (b c d) (Bs' c d))))
  end.

Ltac FullySharpenEachMethod DelegateSigs DelegateReps delegateSpecs :=
    let Delegatees := constr:(Build_NamedDelegatees DelegateSigs DelegateReps) in
    let DelegateSpecs := constr:(ith delegateSpecs) in
    let NumDelegates := match type of DelegateSigs with
                        | Vector.t _ ?n => n
                        end in
    match goal with
      |- FullySharpenedUnderDelegates (@BuildADT ?Rep ?n ?n' ?consSigs ?methSigs ?consDefs ?methDefs) _ =>
      ilist_of_evar_dep n
        (Fin.t NumDelegates -> Type)
        (fun D =>
           forall idx,
             ComputationalADT.pcADT (delegateeSig (Vector.nth Delegatees idx)) (D idx))
        (fun Sig => ComputationalADT.cConstructorType Rep (consDom Sig))
        consSigs
        ltac:(fun cCons =>
                ilist_of_evar_dep n'
                                  (Fin.t NumDelegates -> Type)
                                  (fun D =>
                                     forall idx,
             ComputationalADT.pcADT (delegateeSig (Vector.nth Delegatees idx)) (D idx))
        (fun Sig => ComputationalADT.cMethodType Rep (methDom Sig) (methCod Sig))
        methSigs
        ltac:(fun cMeths =>
                eapply (@Notation_Friendly_SharpenFully
                          Rep NumDelegates n n'
                          consSigs methSigs
                          consDefs methDefs
                          DelegateSigs DelegateReps
                          (fun _ => Rep)
                          cCons cMeths
                          delegateSpecs
                          (fun
                         (DelegateReps'' : Fin.t NumDelegates -> Type)
                         (DelegateImpls'' : forall idx,
                             ComputationalADT.pcADT (delegateeSig (Vector.nth Delegatees idx)) (DelegateReps'' idx))
                         (ValidImpls''
                          : forall idx : Fin.t NumDelegates,
                             refineADT (DelegateSpecs idx)
                                       (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls'' idx))))
                            => @eq _)
             )))
    end; try (simpl; repeat split; intros; subst).

Ltac Implement_If_Then_Else :=
  match goal with
    | |- refine (If_Then_Else ?i (ret ?t) (ret ?e)) _ =>
      apply (refine_If_Then_Else_ret i t e)

    | |- refine (Bind (If ?i Then ?t Else ?e) ?k) _ =>
      etransitivity;
        [ apply (refine_If_Then_Else_Bind i t e k)
        | etransitivity;
          [ apply refine_If_Then_Else;
            [
              | ]
          | eapply refine_If_Then_Else_ret
          ]
        ]
  end.

Ltac Implement_If_Opt_Then_Else :=
  match goal with
    | |- refine (Ifopt ?i as a Then (ret (@?t a)) Else (ret ?e)) _ =>
      apply (refine_If_Opt_Then_Else_ret i t e)

    | |- refine (Bind (Ifopt ?i as a Then (@?t a) Else ?e) ?k) _ =>
      etransitivity;
        [ apply (refine_If_Opt_Then_Else_Bind i t e k)
        | etransitivity;
          [ apply refine_If_Opt_Then_Else;
            [ unfold pointwise_relation; intros
              | ]
          | eapply refine_If_Opt_Then_Else_ret
          ]
        ]
  end.

Ltac finish_SharpeningADT_WithoutDelegation :=
  eapply FullySharpened_Finish;
  [ FullySharpenEachMethod
      (@Vector.nil ADTSig)
      (@Vector.nil Type)
      (ilist.inil (B := fun nadt => ADT (delegateeSig nadt)));
    try simplify with monad laws; simpl; try refine pick eq; try simplify with monad laws;
    try first [ simpl];
    (* Guard setoid rewriting with [refine_if_If] to only occur when there's
    actually an [if] statement in the goal.  This prevents [setoid_rewrite] from
    uselessly descending into folded definitions. *)
    repeat lazymatch goal with
             | [ |- context [ if _ then _ else _ ] ] =>
               setoid_rewrite refine_if_If at 1
           end;
    repeat first [
             higher_order_reflexivity
           | simplify with monad laws
           | Implement_If_Then_Else
           | Implement_If_Opt_Then_Else ]
  | extract_delegate_free_impl
  | simpl; higher_order_reflexivityT ].

Lemma refineIfret {A} :
  forall (cond : bool) (a a' : A),
    refine (if cond then ret a else ret a')
           (ret (if cond then a else a')).
Proof.
  destruct cond; reflexivity.
Qed.
