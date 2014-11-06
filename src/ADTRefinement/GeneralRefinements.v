Require Import Coq.Lists.List ADTSynthesis.Common ADTSynthesis.Common.ilist ADTSynthesis.ADT.Core ADTSynthesis.ADT.ComputationalADT
        ADTSynthesis.ADTRefinement.Core ADTSynthesis.ADTRefinement.SetoidMorphisms.

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

Record SharpenedUnderDelegates Sig :=
  { Sharpened_DelegateSigs : list ADTSig;
    Sharpened_Implementation :
      ilist cADT Sharpened_DelegateSigs
      -> cADT Sig;
    Sharpened_DelegateSpecs : ilist ADT Sharpened_DelegateSigs
  }.

(* Old Deprecated Sharpened Definition *)
(* Notation Sharpened spec := {adt : _ & refineADT spec adt}. *)

(* Shiny New Sharpened Definition includes proof that the
   ADT produced is sharpened modulo a set of 'Delegated ADTs'. *)

Definition FullySharpenedUnderDelegates
           {Sig}
           (spec : ADT Sig)
           (adt : SharpenedUnderDelegates Sig) :=
  forall (DelegateImpl : ilist cADT (Sharpened_DelegateSigs adt)),
    (forall n, Dep_Option_elim_T2
                 (fun Sig adt1 adt2 => @refineADT Sig adt1 (LiftcADT adt2))
                 (ith_error (Sharpened_DelegateSpecs adt) n)
                 (ith_error DelegateImpl n))
        -> refineADT spec (LiftcADT (Sharpened_Implementation adt DelegateImpl)).

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
  intros DI X; eapply transitivityT; [ eassumption | exact (projT2 adt'' DI X)].
Defined.

Lemma projT1_SharpenStep
: forall Sig adt adt' refine_adt_adt' Sharpened_adt',
    projT1 (@SharpenStep Sig adt adt' refine_adt_adt' Sharpened_adt') =
    projT1 Sharpened_adt'.
Proof.
  reflexivity.
Qed.

(* Definition for constructing an easily extractible ADT implementation. *)
Definition BuildMostlySharpenedcADT Sig
           (DelegateSigs : list ADTSig)
           (rep : ilist cADT DelegateSigs -> Type)
           (cConstructors :
              forall (DelegateImpl : ilist cADT DelegateSigs) idx,
                cConstructorType
                  (rep DelegateImpl)
                  (ConstructorDom Sig idx))
           (cMethods :
              forall (DelegateImpl : ilist cADT DelegateSigs) idx,
                cMethodType
                  (rep DelegateImpl)
                  (fst (MethodDomCod Sig idx))
                  (snd (MethodDomCod Sig idx)))
           (DelegateImpl : ilist cADT DelegateSigs)
  : cADT Sig :=
    {| cRep          := rep DelegateImpl;
       cConstructors := cConstructors DelegateImpl;
       cMethods      := cMethods DelegateImpl |}.

(* Proof component of the ADT is Qed-ed. *)
Lemma FullySharpened_BuildMostlySharpenedcADT {Sig}
: forall (spec : ADT Sig)
         (DelegateSigs : list ADTSig)
         (rep : ilist cADT DelegateSigs -> Type)
         (cConstructors :
            forall (DelegateImpl : ilist cADT DelegateSigs) idx,
              cConstructorType
                (rep DelegateImpl)
                (ConstructorDom Sig idx))
         (cMethods :
            forall (DelegateImpl : ilist cADT DelegateSigs) idx,
              cMethodType
                (rep DelegateImpl)
                (fst (MethodDomCod Sig idx))
                (snd (MethodDomCod Sig idx)))
         (DelegateSpecs : ilist ADT DelegateSigs)
         (cAbsR : forall DelegateImpl,
                    (forall n, Dep_Option_elim_T2
                                 (fun Sig adt adt' => @refineADT Sig adt (LiftcADT adt'))
                                 (ith_error DelegateSpecs n)
                                 (ith_error DelegateImpl n))
                    -> Rep spec -> rep DelegateImpl -> Prop),
    (forall (DelegateImpl : ilist cADT DelegateSigs)
            (ValidImpl : forall n, Dep_Option_elim_T2
                                     (fun Sig adt adt' => @refineADT Sig adt (LiftcADT adt'))
                                     (ith_error DelegateSpecs n)
                                     (ith_error DelegateImpl n)),
     forall idx : ConstructorIndex Sig,
       @refineConstructor
         (Rep spec) (rep DelegateImpl) (cAbsR _ ValidImpl)
         (ConstructorDom Sig idx)
         (Constructors spec idx)
         (fun d => ret (cConstructors DelegateImpl idx d)))
    -> (forall (DelegateImpl : ilist cADT DelegateSigs)
               (ValidImpl : forall n, Dep_Option_elim_T2
                                        (fun Sig adt adt' => @refineADT Sig adt (LiftcADT adt'))
                                        (ith_error DelegateSpecs n)
                                        (ith_error DelegateImpl n)),
        forall idx,
       @refineMethod
         (Rep spec) (rep DelegateImpl) (cAbsR _ ValidImpl)
         (fst (MethodDomCod Sig idx)) (snd (MethodDomCod Sig idx))
         (Methods spec idx)
         (fun r_n d => ret (cMethods DelegateImpl idx r_n d)))
    -> FullySharpenedUnderDelegates
         spec
         {| Sharpened_DelegateSigs := DelegateSigs;
            Sharpened_Implementation := BuildMostlySharpenedcADT Sig rep cConstructors
                                                                 cMethods;
            Sharpened_DelegateSpecs := DelegateSpecs |}.
Proof.
  intros * cConstructorsRefinesSpec cMethodsRefinesSpec DelegateImpl DelegateImplRefinesSpec.
  eapply (@refinesADT Sig spec (LiftcADT {|cRep := rep DelegateImpl;
                                           cConstructors := _;
                                           cMethods := _|})
                      (cAbsR DelegateImpl DelegateImplRefinesSpec)).
  - simpl; intros; 
    eapply (cConstructorsRefinesSpec _ DelegateImplRefinesSpec idx d).
  - simpl; intros. 
    eapply (cMethodsRefinesSpec _ DelegateImplRefinesSpec); eauto. 
Qed.

Definition SharpenFully {Sig}
           (spec : ADT Sig)
         (DelegateSigs : list ADTSig)
         (rep : ilist cADT DelegateSigs -> Type)
         (cConstructors :
            forall (DelegateImpl : ilist cADT DelegateSigs) idx,
              cConstructorType
                (rep DelegateImpl)
                (ConstructorDom Sig idx))
         (cMethods :
            forall (DelegateImpl : ilist cADT DelegateSigs) idx,
              cMethodType
                (rep DelegateImpl)
                (fst (MethodDomCod Sig idx))
                (snd (MethodDomCod Sig idx)))
         (DelegateSpecs : ilist ADT DelegateSigs)
         (cAbsR : forall DelegateImpl,
                    (forall n, Dep_Option_elim_T2
                                 (fun Sig adt adt' => @refineADT Sig adt (LiftcADT adt'))
                                 (ith_error DelegateSpecs n)
                                 (ith_error DelegateImpl n))
                    -> Rep spec -> rep DelegateImpl -> Prop)
         (cConstructorsRefinesSpec :
            forall (DelegateImpl : ilist cADT DelegateSigs)
                   (ValidImpl :
                      forall n, Dep_Option_elim_T2
                                  (fun Sig adt adt' => @refineADT Sig adt (LiftcADT adt'))
                                  (ith_error DelegateSpecs n)
                                  (ith_error DelegateImpl n)),
            forall idx : ConstructorIndex Sig,
              @refineConstructor
                (Rep spec) (rep DelegateImpl) (cAbsR _ ValidImpl)
                (ConstructorDom Sig idx)
                (Constructors spec idx)
                (fun d => ret (cConstructors DelegateImpl idx d)))
         (cMethodsRefinesSpec :
            forall (DelegateImpl : ilist cADT DelegateSigs)
                   (ValidImpl :
                      forall n,
                        Dep_Option_elim_T2
                          (fun Sig adt adt' => @refineADT Sig adt (LiftcADT adt'))
                          (ith_error DelegateSpecs n)
                          (ith_error DelegateImpl n)),
            forall idx,
              @refineMethod
                (Rep spec) (rep DelegateImpl) (cAbsR _ ValidImpl)
                (fst (MethodDomCod Sig idx)) (snd (MethodDomCod Sig idx))
                (Methods spec idx)
                (fun r_n d => ret (cMethods DelegateImpl idx r_n d)))
: Sharpened spec :=
  existT _ _ (FullySharpened_BuildMostlySharpenedcADT spec rep cConstructors
                                                    cMethods DelegateSpecs cAbsR
                                                    cConstructorsRefinesSpec cMethodsRefinesSpec).

Definition Extract_is_computationalADT
           {Sig}
           (adt : ADT Sig)
           (adt_is_comp : is_computationalADT adt)
: cADT Sig :=
  {| cRep := Rep adt;
     cConstructors :=
       fun idx arg =>
         CallComputationalConstructor adt_is_comp idx arg;
     cMethods :=
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
