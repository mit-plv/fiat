Require Import Fiat.Common Fiat.Computation Coq.Sets.Ensembles
        Fiat.ADT.ADTSig Fiat.ADT.Core
        Fiat.ADTRefinement.Core Fiat.ADTRefinement.SetoidMorphisms
        Fiat.ADTRefinement.GeneralRefinements.

Generalizable All Variables.
Set Implicit Arguments.

(** Oftentimes in order to show that a refinement is valid, we need
    some invariant to hold on an ADT's representation- a value cached
    in an ADT's representation should be the result of running an
    observer on the current state, for example.


    One solution to this problem is to use dependent products to
    package proofs of an invariant into an ADT's representation: [
    {rep | Invariant rep} ].
    While conceptually simple, this forces methods to be 'internally'
    verified- mutator methods in particular have to simultaneously
    produce a new state /and/ a proof that it satisfies the ADT's
    invariant.  This can make derivations more painful while
    potentially being bewildering to those unfamiliar with dependent
    products.

    Dependent products introduce another wrinkle to refinement: since
    an ADT refinement can change the proof produced by a method, we
    can't always use equality as the abstraction relation in
    [ADTrefine]. (As an example of a case where the proof changes, a
    refinement might use a cached value instead of running a method on
    the current state.)

    An alternative approach is to have the [ADT] include invariants
    and the corresponding proofs that methods maintain them as a
    separate fields. This more familiar presentation allows method
    refinements to be defined and then verified interactively during a
    derivation, at the cost of polluting ADT definitions with extra
    fields. Since proofs aren't packaged into the representation in
    this approach, equality suffices for expressing method refinement.

    Yet another approach is to use the abstract relation to derive
    an ad hoc invariant for a particular refinement step. The basic
    idea is that the abstraction relation relates two equal states for
    which the invariant holds. By baking the invariant into the
    abstraction relation, it becomes a hypothesis to all of our
    refinement proofs.  The cost of this approach is that it requires
    a proof that each mutator preserves the invariant on an ad hoc
    basis, which could leave to some duplicate proofs (One way to
    mitigate this would be to include invariant hypotheses around in
    the context, which we could bake into the honing
    tactics). Otherwise, I would argue it includes the best of
    both worlds- there's no need to pollute the definition of [ADT]
    with [repInv] /and/ methods don't have to bother with maintaining
    proofs.

 *)

Section RepInv.

  Variable rep : Type.
  Variable repInv : Ensemble rep.

  (** This is the abstraction relation we use to mimic invariants- the
      representations are always the same /and/ the invariant
      holds. *)

  Definition repInvAbsR (r_o r_n : rep) :=
    r_o = r_n /\ repInv r_n.

  (** Refining an adt using the [repInvAbsR] relation allows us to
      utilize [repInv] when proving method refinement. Of course, we
      also have to show that mutators preserve the invariant.
      Hopefully we can include additional information into the honing
      tactics to avoid reproving invariant preservation.  *)

  Lemma refineADT_Build_ADT_RepInv
        Sig
    : forall meth meth',
      (forall idx, @refineMethod _ _ repInvAbsR
                                 (fst (fst (MethodDomCod Sig idx)))
                                 (snd (fst (MethodDomCod Sig idx)))
                                 (snd (MethodDomCod Sig idx))
                                 (meth idx) (meth' idx))
      -> refineADT (@Build_ADT Sig rep meth)
                   (@Build_ADT Sig rep meth').
  Proof.
    intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
  Qed.

  Lemma refine_pick_repInvAbsR :
    forall r_o, repInv r_o ->
    refineEquiv {r_n | repInvAbsR r_o r_n}
                (ret r_o).
  Proof.
    unfold repInvAbsR; split; intros v CompV; computes_to_inv; intuition;
    subst; computes_to_econstructor; eauto.
  Qed.

  Lemma refine_pick_repInvAbsR' :
    forall r_n, repInv r_n ->
    refineEquiv {r_o | repInvAbsR r_o r_n}
                (ret r_n).
  Proof.
    unfold repInvAbsR; split; intros v CompV; computes_to_inv; intuition;
    subst; econstructor; eauto.
  Qed.

End RepInv.

(* A more user-friendly version of [refineADT_Build_ADT_Rep]. *)

(*Lemma refinesADTRepInv Sig
      (adt : ADT Sig)
      (repInv : Ensemble (Rep adt))
      Constructors'
      Methods'
      (RefConstr : forall idx d,
                  refine
                    (r_o' <- Constructors adt idx d;
                      {r_n  | r_o' = r_n /\ repInv r_n})
                    (Constructors' idx d))
      (RefMeth : forall idx (r : Rep adt) n,
                  repInv r ->
                  refine
                    (r' <- Methods adt idx r n;
                     r'' <- {r'' : Rep adt |
                             repInvAbsR repInv (fst r') r''};
                    ret (r'', snd r'))
                    (Methods' idx r n))
      (cachedIndex : ConstructorIndex Sig)
: refineADT adt
            {| Rep := Rep adt;
               Constructors := Constructors';
               Methods := Methods'
            |}.
Proof.
  destruct adt.
  eapply refineADT_Build_ADT_RepInv with
  (repInv := repInv); unfold pointwise_relation, repInvAbsR in *;
  simpl in *; intros; intuition; subst; eauto.
Qed.

Tactic Notation "hone" "method" constr(mutIdx) "using" constr(mutBody)
       "under" "invariant" constr(repInv) :=
    let A :=
        match goal with
            |- Sharpened ?A => constr:(A) end in
    let ASig := match type of A with
                    ADT ?Sig => Sig
                end in
    let mutIdx_eq' := fresh in
    let Rep' := eval simpl in (Rep A) in
    let MethodIndex' := eval simpl in (MethodIndex ASig) in
    let ConstructorIndex' := eval simpl in (ConstructorIndex ASig) in
    let Methods' := eval simpl in (Methods A) in
    let Constructors' := eval simpl in (Constructors A) in
      assert (forall idx idx' : MethodIndex', {idx = idx'} + {idx <> idx'})
        as mutIdx_eq' by (decide equality);
      eapply SharpenStep;
        [eapply (@refineADT_Build_ADT_RepInv Rep' repInv
                   _
                   _
                   (fun idx : MethodIndex ASig => if (mutIdx_eq' idx mutIdx) then
                                 mutBody
                               else
                                 Methods' idx));
          try instantiate (1 := Constructors')
        | idtac]; cbv beta in *; simpl in *. *)
