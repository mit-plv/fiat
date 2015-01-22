Require Import Coq.Lists.List Coq.Strings.String
        ADTSynthesis.Common
        ADTSynthesis.Common.ilist
        ADTSynthesis.Common.i2list
        ADTSynthesis.Common.StringBound
        ADTSynthesis.ADT.Core ADTSynthesis.ADT.ComputationalADT
        ADTSynthesis.ADTRefinement.Core
        ADTSynthesis.ADTRefinement.SetoidMorphisms.

(* To derive an ADT interactively from a specification [spec], we can
   build a dependent product [ {adt : _ & refineADT spec adt} ]. The
   derivation flow has the form:

   1. Apply a refinement.
   2. Discharge any side conditions.
   3. Repeat steps 1-2 until adt is completely specialized.

   My (Ben's) current thought is that to make this as pleasant as
   possible, the refinements used in the first step should be
   implemented using tactics which present the user with 'nice' side
   conditions. (In particular, this lets us be careful about not
   having any dangling existential variables at the end of a
   derivation).

   Aside on notation:
   When naming these tactics, I wanted one which
   wasn't already used by a tactic- refine, specialize, and replace
   were taken. The thesaurus suggested 'hone'.  This kind of agrees
   with 'Bedrock' (in as much as a Whetstone is used to sharpen
   knives), so I'm carrying on the naming convention with a
   'Sharpened' notation for the dependent products. *)

Notation FullySharpened spec := {adt : _ & refineADT spec (LiftcADT adt)}.

Record NamedADTSig :=
  { ADTSigname : string;
    namedADTSig : ADTSig }.

Record SharpenedUnderDelegates (Sig : ADTSig)
  : Type
  := Build_SharpenedUnderDelegates
       { Sharpened_DelegateIDs : list string;
         Sharpened_DelegateSigs : @BoundedString Sharpened_DelegateIDs -> ADTSig;
         Sharpened_Implementation :
           forall (DelegateReps : @BoundedString Sharpened_DelegateIDs -> Type)
                  (DelegateImpls : forall idx,
                                      ComputationalADT.pcADT (Sharpened_DelegateSigs idx) (DelegateReps idx)),
             ComputationalADT.cADT Sig;
         Sharpened_DelegateSpecs : forall idx, ADT (Sharpened_DelegateSigs idx) }.

Definition FullySharpenedUnderDelegates
           (Sig : ADTSig)
           (spec : ADT Sig)
           (adt : SharpenedUnderDelegates Sig)
  := forall (DelegateReps : @BoundedString (Sharpened_DelegateIDs adt) -> Type)
            (DelegateImpls : forall idx,
                               ComputationalADT.pcADT (Sharpened_DelegateSigs adt idx) (DelegateReps idx))
            (ValidImpls
             : forall idx : @BoundedString (Sharpened_DelegateIDs adt),
                 refineADT (Sharpened_DelegateSpecs adt idx)
                           (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
       refineADT spec
                 (ComputationalADT.LiftcADT (Sharpened_Implementation adt DelegateReps DelegateImpls)).

(* Old Deprecated Sharpened Definition *)
(* Notation Sharpened spec := {adt : _ & refineADT spec adt}. *)

(* Shiny New Sharpened Definition includes proof that the
   ADT produced is sharpened modulo a set of 'Delegated ADTs'. *)

Notation Sharpened spec :=
  {adt : _ & @FullySharpenedUnderDelegates _ spec adt}.

(* A single refinement step. *)
Definition SharpenStep Sig adt :
  forall adt',
    refineADT (Sig := Sig) adt adt' ->
    Sharpened adt' ->
    Sharpened adt.
Proof.
  intros adt' refineA adt''.
  exists (projT1 adt'').
  unfold FullySharpenedUnderDelegates in *.
  intros * idx; eapply transitivityT;
  [ eassumption | exact (projT2 adt'' _ DelegateImpls idx)].
Defined.

Lemma projT1_SharpenStep
: forall Sig adt adt' refine_adt_adt' Sharpened_adt',
    projT1 (@SharpenStep Sig adt adt' refine_adt_adt' Sharpened_adt') =
    projT1 Sharpened_adt'.
Proof.
  reflexivity.
Qed.

(* Definition for constructing an easily extractible ADT implementation. *)

Definition BuildMostlySharpenedcADT
           Sig
           (DelegateIDs : list string)
           (DelegateSigs : @BoundedString Sharpened_DelegateIDs -> ADTSig)
           (rep : @BoundedString Sharpened_DelegateIDs -> ADTSig) Type)
           (cConstructors :
              forall
                (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
                (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps) idx,
                cConstructorType
                  (rep DelegateReps)
                  (ConstructorDom Sig idx))
           (cMethods :
              forall
                (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
                (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps) idx,
                cMethodType
                  (rep DelegateReps)
                  (fst (MethodDomCod Sig idx))
                  (snd (MethodDomCod Sig idx)))
           (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
           (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps)
: cADT Sig :=
  existT _ (rep DelegateReps)
         {| pcConstructors := cConstructors DelegateReps DelegateImpls;
            pcMethods      := cMethods DelegateReps DelegateImpls |}.

(* Proof component of the ADT is Qed-ed. *)
Lemma FullySharpened_BuildMostlySharpenedcADT {Sig}
: forall
    (spec : ADT Sig)
    (DelegateSigs : list NamedADTSig)
    (rep : ilist (fun nadt : NamedADTSig => Type) DelegateSigs -> Type)
    (cConstructors :
       forall
         (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
         (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps) idx,
         cConstructorType
           (rep DelegateReps)
           (ConstructorDom Sig idx))
    (cMethods :
       forall
         (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
         (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps) idx,
         cMethodType
           (rep DelegateReps)
           (fst (MethodDomCod Sig idx))
           (snd (MethodDomCod Sig idx)))
    (DelegateSpecs : ilist (fun nadt => ADT (namedADTSig nadt)) DelegateSigs)
    (cAbsR :
       forall
         (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
         (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps),
         (forall idx : BoundedIndex (map ADTSigname DelegateSigs),
            refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                      (ComputationalADT.LiftcADT
                         (existT _ _ (i2th_Bounded ADTSigname DelegateImpls idx)))) ->
         Rep spec -> rep DelegateReps -> Prop),
    (forall
        (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
        (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps)
        (ValidImpls
         : forall idx : BoundedIndex (map ADTSigname DelegateSigs),
             refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                       (ComputationalADT.LiftcADT
                          (existT _ _ (i2th_Bounded ADTSigname DelegateImpls idx)))),
      forall idx : ConstructorIndex Sig,
        @refineConstructor
          (Rep spec) (rep DelegateReps) (cAbsR _ _ ValidImpls)
          (ConstructorDom Sig idx)
          (Constructors spec idx)
         (fun d => ret (cConstructors DelegateReps DelegateImpls idx d)))
    -> (forall
           (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
           (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps)
           (ValidImpls
            : forall idx : BoundedIndex (map ADTSigname DelegateSigs),
                refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                          (ComputationalADT.LiftcADT
                             (existT _ _ (i2th_Bounded ADTSigname DelegateImpls idx)))),
        forall idx,
          @refineMethod
            (Rep spec) (rep DelegateReps) (cAbsR _ _ ValidImpls)
            (fst (MethodDomCod Sig idx)) (snd (MethodDomCod Sig idx))
            (Methods spec idx)
            (fun r_n d => ret (cMethods DelegateReps DelegateImpls idx r_n d)))
    -> FullySharpenedUnderDelegates
         spec
         {| Sharpened_DelegateSigs := DelegateSigs;
            Sharpened_Implementation := BuildMostlySharpenedcADT Sig rep cConstructors
                                                                 cMethods;
            Sharpened_DelegateSpecs := DelegateSpecs |}.
Proof.
  intros * cConstructorsRefinesSpec cMethodsRefinesSpec DelegateReps DelegateImpls DelegateImplRefinesSpec.
  eapply (@refinesADT Sig spec (LiftcADT (existT _ (rep DelegateReps)
                                         {| pcConstructors := _;
                                            pcMethods := _|}))
                      (cAbsR DelegateReps DelegateImpls DelegateImplRefinesSpec)).
  - simpl; intros;
    eapply (cConstructorsRefinesSpec _ _ DelegateImplRefinesSpec idx d).
  - simpl; intros.
    eapply (cMethodsRefinesSpec _ _ DelegateImplRefinesSpec); eauto.
Qed.

Definition SharpenFully {Sig}
           (spec : ADT Sig)
           (DelegateSigs : list NamedADTSig)
           (rep : ilist (fun nadt : NamedADTSig => Type) DelegateSigs -> Type)
    (cConstructors :
       forall
         (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
         (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps) idx,
         cConstructorType
           (rep DelegateReps)
           (ConstructorDom Sig idx))
    (cMethods :
       forall
         (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
         (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps) idx,
         cMethodType
           (rep DelegateReps)
           (fst (MethodDomCod Sig idx))
           (snd (MethodDomCod Sig idx)))
    (DelegateSpecs : ilist (fun nadt => ADT (namedADTSig nadt)) DelegateSigs)
    (cAbsR :
       forall
         (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
         (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps),
         (forall idx : BoundedIndex (map ADTSigname DelegateSigs),
            refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                      (ComputationalADT.LiftcADT
                         (existT _ _ (i2th_Bounded ADTSigname DelegateImpls idx)))) ->
         Rep spec -> rep DelegateReps -> Prop)
    (cConstructorsRefinesSpec :
       forall
         (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
         (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps)
         (ValidImpls
          : forall idx : BoundedIndex (map ADTSigname DelegateSigs),
              refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                        (ComputationalADT.LiftcADT
                           (existT _ _ (i2th_Bounded ADTSigname DelegateImpls idx)))),
       forall idx : ConstructorIndex Sig,
         @refineConstructor
           (Rep spec) (rep DelegateReps) (cAbsR _ _ ValidImpls)
           (ConstructorDom Sig idx)
           (Constructors spec idx)
           (fun d => ret (cConstructors DelegateReps DelegateImpls idx d)))
    (cMethodsRefinesSpec
     : forall
         (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
         (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps)
         (ValidImpls
          : forall idx : BoundedIndex (map ADTSigname DelegateSigs),
              refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                        (ComputationalADT.LiftcADT
                           (existT _ _ (i2th_Bounded ADTSigname DelegateImpls idx)))),
       forall idx,
         @refineMethod
           (Rep spec) (rep DelegateReps) (cAbsR _ _ ValidImpls)
           (fst (MethodDomCod Sig idx)) (snd (MethodDomCod Sig idx))
           (Methods spec idx)
           (fun r_n d => ret (cMethods DelegateReps DelegateImpls idx r_n d)))
    : Sharpened spec :=
  existT _ _ (FullySharpened_BuildMostlySharpenedcADT spec rep cConstructors
                                                      cMethods DelegateSpecs cAbsR
                                                      cConstructorsRefinesSpec cMethodsRefinesSpec).

Definition Extract_is_computationalADT
           {Sig}
           (adt : ADT Sig)
           (adt_is_comp : is_computationalADT adt)
: cADT Sig :=
  existT _ (Rep adt)
         {| pcConstructors :=
              fun idx arg =>
                CallComputationalConstructor adt_is_comp idx arg;
            pcMethods :=
              fun idx arg rep =>
                CallComputationalMethod adt_is_comp idx arg rep
         |}.

(* Honing tactic for refining the observer method with the specified index.
     This version of the tactic takes the new implementation as an argument. *)

Tactic Notation "hone'" "method" constr(obsIdx) "using" constr(obsBody) :=
  let A :=
      match goal with
          |- Sharpened ?A => constr:(A) end in
  let ASig := match type of A with
                  ADT ?Sig => Sig
              end in
  let mutIdx_eq' := fresh in
  let Rep' := eval simpl in (Rep A) in
  let ConstructorIndex' := eval simpl in (ConstructorIndex ASig) in
  let MethodIndex' := eval simpl in (MethodIndex ASig) in
  let Methods' := eval simpl in (Methods A) in
    assert (forall idx idx' : MethodIndex', {idx = idx'} + {idx <> idx'})
      as obsIdx_eq' by (decide equality);
    eapply SharpenStep;
    [eapply (@refineADT_Build_ADT_Method
               Rep' _ _ _
               (fun idx : MethodIndex ASig => if (obsIdx_eq' idx ()) then
                             obsBody
                           else
                             Methods' idx))
    | idtac]; cbv beta in *; simpl in *.

(* Honing tactic for refining the constructor method with the specified index.
   This version of the tactic takes the new implementation as an argument. *)
Tactic Notation "hone'" "constructor" constr(mutIdx) "using" constr(mutBody) :=
  let A :=
      match goal with
          |- Sharpened ?A => constr:(A) end in
  let ASig := match type of A with
                  ADT ?Sig => Sig
              end in
  let mutIdx_eq' := fresh in
  let Rep' := eval simpl in (Rep A) in
  let ConstructorIndex' := eval simpl in (ConstructorIndex ASig) in
  let MethodIndex' := eval simpl in (MethodIndex ASig) in
  let Constructors' := eval simpl in (Constructors A) in
    assert (forall idx idx' : ConstructorIndex', {idx = idx'} + {idx <> idx'})
      as mutIdx_eq' by (decide equality);
    eapply SharpenStep;
      [eapply (@refineADT_Build_ADT_Constructors Rep'
                 _
                 _
                 _
                 (fun idx : ConstructorIndex ASig => if (mutIdx_eq' idx mutIdx) then
                               mutBody
                             else
                               Constructors' idx))
      | idtac]; cbv beta in *; simpl in *.
