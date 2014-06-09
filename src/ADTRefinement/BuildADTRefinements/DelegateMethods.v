Require Import Common Computation ADT ADTNotation Ensembles ADTRefinement.Core
        ADTRefinement.GeneralRefinements Pick.

Section DelegateMethods.

  (* One way to implement some common functionality is to delegate it
     to the methods of some ADT.

     The first step in this process is to augment the representation
     of the delegating ADT with an instance of the ADT to delegate to.
     *)

  (* Original representation type. *)
  Variable origRep : Type.
  (* Signatures of the original set of mutators. *)
  Variable mutSigs : list mutSig.
  (* Signatures of the original set of observers. *)
  Variable obsSigs : list obsSig.

  (* Signatures of the observers to be delegated to. *)
  Variable delegateSigs : list obsSig.

  (* Signature of the ADT being delegated to. *)
  Definition delegateSig := BuildADTSig mutSigs delegateSigs.

  (* ADT being delegated to. *)
  Variable delegateADT : ADT delegateSig.

  Definition delegatorRep := prod origRep (Rep delegateADT).

  Definition delegateMut {Dom : Type}
             (origMut : mutatorMethodType origRep Dom)
             (delMut : mutatorMethodType (Rep delegateADT) Dom)
  : mutatorMethodType delegatorRep Dom :=
    fun dr (n : Dom) =>
      (origR <- origMut (fst dr) n;
      delR <- delMut (snd dr) n;
      ret (origR, delR))%comp.

  Definition delegateMutDef
             (Sig : mutSig)
             (oldMut : @mutDef origRep Sig)
             (delMut : mutatorMethodType (Rep delegateADT) (mutDom Sig))
  : @mutDef delegatorRep Sig :=
    {| mutBody := delegateMut (mutBody oldMut) delMut |}.

  Definition delegateObsDef
             (Sig : obsSig)
             (oldObs : @obsDef origRep Sig)
  : @obsDef delegatorRep Sig :=
    {| obsBody := fun dr => obsBody oldObs (fst dr) |}.

  Program Fixpoint BuildDelegateADT'
           (Rep : Type)
           (mutSigs' : list mutSig)
           (mutators :
              forall idx : String.string,
                List.In idx (List.map mutID mutSigs') ->
                mutatorMethodType Rep
                                  (mutDom
                                     (List.nth (findIndex mutSig_eq mutSigs' idx) mutSigs'
                                               ("null" : rep × () → rep)%mutSig)))
           {struct mutSigs'} : ilist (@mutDef Rep) mutSigs' :=
    match mutSigs' as mutSigs' return
          (forall idx : String.string,
             List.In idx (List.map mutID mutSigs') ->
            mutatorMethodType Rep
                              (mutDom
                                 (List.nth (findIndex mutSig_eq mutSigs' idx) mutSigs'
                                           ("null" : rep × () → rep)%mutSig)))
          -> ilist (@mutDef Rep) mutSigs' with
        | nil => fun mutators => inil _
        | cons mutSig mutSigs'' => fun mutators => (fun H => _) (@BuildDelegateADT' Rep mutSigs'')
    end mutators.
  Next Obligation.
    econstructor.
    econstructor.
    generalize (mutators0 (mutID mutSig) ).
    unfold mutSig_eq; simpl.
    destruct (String.string_dec (mutID mutSig) (mutID mutSig)); eauto.
    congruence.
    eapply H.
    intros; generalize (mutators0
    intros;
    simpl; find_if_inside; auto.


  Lemma refineADT_DelegatedMethods
            (mutDefs : ilist (@mutDef origRep) mutSigs)
            (obsDefs : ilist (@obsDef origRep) obsSigs) :
    refineADT
      (BuildADT mutDefs obsDefs)
      (BuildADT (imap _ (fun Sig (oldMut : mutDef Sig) =>
                           delegateMutDef oldMut (MutatorMethods delegateADT (mutID Sig))
                      mutDefs)
                (imap _ delegateObsDef obsDefs))).
  Proof.

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
    (AbsR := fun or nr => or = fst nr); simpl; intros; subst.
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

  Definition AbsR_refineADT {Sig}
             {adt1 adt2 : ADT Sig}
             (refines_adt1_adt2 : refineADT adt1 adt2)
  : exists AbsR : Rep adt1 -> Rep adt2 -> Prop,
      forall idx : ObserverIndex Sig,
        refineObserver AbsR (ObserverMethods adt1 idx)
                       (ObserverMethods adt2 idx).
    destruct refines_adt1_adt2; eauto.
  Defined.

  Check (AbsR_refineADT refinesdelegateADTRefRep).

  Print ex_intro.

  Lemma refinesDelegatedMethodPick :
    forall (idx : delegateIndex)
           (r : Rep delegateADT)
           (x : (fst (ObserverDomCod delegateSig idx)))
           (AbsR' r' r ->
       delegateObserverSpecs idx r' x c -> P c
       end) ->
      refine {c | P c} (ObserverMethods delegateADT idx r x).
  Proof.
    intros. *)
