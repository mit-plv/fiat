Require Import ADTSynthesis.Common ADTSynthesis.Computation
        ADTSynthesis.ADT.ADTSig ADTSynthesis.ADT.Core
        ADTSynthesis.ADTRefinement.Core ADTSynthesis.ADTRefinement.GeneralRefinements
        ADTSynthesis.ADTRefinement.SetoidMorphisms.

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

  (* Codomain of the new methods. *)
  Variable delegateCod : MethodIndex delegatorSig -> Type.

  (* Signature of the ADT being delegated to. *)
  Definition delegateSig :=
    {| ConstructorIndex := ConstructorIndex delegatorSig;
       MethodIndex := MethodIndex delegatorSig;
       ConstructorDom := ConstructorDom delegatorSig;
       MethodDomCod idx :=
         (fst (MethodDomCod delegatorSig idx), delegateCod idx)
    |}.

  (* ADT being delegated to. *)
  Variable delegateADT : ADT delegateSig.

  Local Open Scope comp.

  Definition ADTwDelegatedMethods : ADT delegatorSig :=
    {| Rep := Rep delegatorADT * Rep delegateADT;
       Constructors idx x :=
         (r1 <- Constructors delegatorADT idx x;
          r2 <- Constructors delegateADT idx x;
          ret (r1, r2));
       Methods idx r x :=
         (r1 <- Methods delegatorADT idx (fst r) x;
          r2 <- Methods delegateADT idx (snd r) x;
          ret ((fst r1, fst r2), snd r1 ))
    |}.

  Lemma refineADT_DelegatedMethods :
    refineADT delegatorADT ADTwDelegatedMethods.
  Proof.
    unfold ADTwDelegatedMethods; destruct delegatorADT;
    eapply refineADT_Build_ADT_Rep with
    (AbsR := fun or nr => or = fst nr); simpl; intros; subst.
    - unfold refine; intros; computes_to_inv; subst;
      computes_to_econstructor; eauto.
    - f_equiv; unfold pointwise_relation, refine; intros.
      computes_to_inv; subst.
      repeat computes_to_econstructor; eauto.
  Qed.

End DelegateMethods.
