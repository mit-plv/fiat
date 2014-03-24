Require Import Common Computation ADT Ensembles ADTRefinement.Core
        ADTRefinement.GeneralRefinements Pick.

Section DelegateMethods.

  (* One way to implement some common functionality is to delegate it
     to the methods of some ADT.

     The first step in this process is to augment the representation
     of the delegating ADT with an instance of the ADT to delegate to.
     *)

  (* Signature of the ADT doing the delegating. *)
  Variable delegatorSig : ADTSig.

  (* ADT doing the delegating. *)
  Variable delegatorADT : ADT delegatorSig.


  (* Indices of the methods that will be delegated to. *)
  Variable delegateIndex : Type.

  (* Domain and codomain of the new methods. *)
  Variable delegateDomCod : delegateIndex -> Type * Type.

  (* Signature of the ADT being delegated to. *)
  Definition delegateSig :=
    {| MutatorIndex := MutatorIndex delegatorSig;
       ObserverIndex := delegateIndex;
       MutatorDom := MutatorDom delegatorSig;
       ObserverDomCod := delegateDomCod
    |}.

  (* ADT being delegated to. *)
  Variable delegateADT : ADT delegateSig.

  Definition ADTwDelegatedMethods : ADT delegatorSig :=
    {| Rep := Rep delegatorADT * Rep delegateADT;
       MutatorMethods idx r x :=
         (r1 <- MutatorMethods delegatorADT idx (fst r) x;
          r2 <- MutatorMethods delegateADT idx (snd r) x;
          ret (r1, r2))%comp;
       ObserverMethods idx r :=
         ObserverMethods delegatorADT idx (fst r)
    |}.

  Lemma refineADT_DelegatedMethods :
    refineADT delegatorADT ADTwDelegatedMethods.
  Proof.
    unfold ADTwDelegatedMethods; destruct delegatorADT;
    eapply refineADT_Build_ADT_Rep with
    (SiR := fun or nr => or = fst nr); simpl; intros; subst.
    - unfold refine; intros; inversion_by computes_to_inv; subst;
      econstructor; eauto.
    - reflexivity.
  Qed.

End DelegateMethods.

(*Section SwapDelegate.

  (* Signature of the ADT doing the delegating. *)
  Variable delegatorSig : ADTSig.
  (* ADT doing the delegating. *)
  Variable delegatorADT : ADT delegatorSig.


  (* Indices of the methods that will be delegated to. *)
  Variable delegateIndex : Type.
  (* Domain and codomain of the new methods. *)
  Variable delegateDomCod : delegateIndex -> Type * Type.


  (* Reference ADT to delegate to. *)
  Variable refDelegateADT : ADT (delegateSig delegatorSig delegateDomCod).
  (* Implementation ADT to delegate to. *)
  Variable implDelegateADT : ADT (delegateSig delegatorSig delegateDomCod).



  (* The reference representation of the specification of the ADT
     being delegated to. (A natural candidate is the representation of
     [delegatorADT].) *)
  Variable delegateRefRep : Type.

  (* The specification of the mutators of the delegate ADT
  specification. (If [delegateRefRep] is [delegatorADT], these are
  simply specifications of the mutators of the latter. ) *)

  Variable delegateMutatorSpecs :
    forall idx,
      mutatorMethodSpec delegateRefRep (MutatorDom delegateSig idx).

  (* The specification of the mutators of the delegate ADT
  specification. *)
  Variable delegateObserverSpecs :
    forall idx,
      observerMethodSpec delegateRefRep
                         (fst (ObserverDomCod delegateSig idx))
                         (snd (ObserverDomCod delegateSig idx)).

  (* The refinement assumes that [delegateADT] implements the above
   spec. *)
  Hypothesis refinesdelegateADTRefRep :
    refineADT (pickImpl _ delegateMutatorSpecs delegateObserverSpecs)
              delegateADT.

  Definition SiR_refineADT {Sig}
             {adt1 adt2 : ADT Sig}
             (refines_adt1_adt2 : refineADT adt1 adt2)
  : exists SiR : Rep adt1 -> Rep adt2 -> Prop,
      forall idx : ObserverIndex Sig,
        refineObserver SiR (ObserverMethods adt1 idx)
                       (ObserverMethods adt2 idx).
    destruct refines_adt1_adt2; eauto.
  Defined.

  Check (SiR_refineADT refinesdelegateADTRefRep).

  Print ex_intro.

  Lemma refinesDelegatedMethodPick :
    forall (idx : delegateIndex)
           (r : Rep delegateADT)
           (x : (fst (ObserverDomCod delegateSig idx)))
           (SiR' r' r ->
       delegateObserverSpecs idx r' x c -> P c
       end) ->
      refine {c | P c} (ObserverMethods delegateADT idx r x).
  Proof.
    intros. *)
