Require Import Common Computation ADT Ensembles ADTRefinement.

Generalizable All Variables.
Set Implicit Arguments.

(* Oftentimes in order to show that a refinement is valid, we
   need some invariant to hold on an ADT's representation- a value
   cached in an ADT's representation should be the result of running
   an observer on the current state, for example.


   One solution to this problem is to use dependent products to package
   proofs of an invariant into an ADT's representation: [ {rep | Invariant rep} ].
   While conceptually simple, this forces methods to be 'internally'
   verified- mutator methods in particular have to simultaneously produce
   a new state /and/ a proof that it satisfies the ADT's invariant.
   This can make derivations more painful while potentially being
   bewildering to those unfamiliar with dependent products.

   Dependent products introduce another wrinkle to refinement:
   since an ADT refinement can change the proof produced by a method,
   we can't always use equality as the bisimulation relation in
   [ADTrefine]. (As an example of a case where the proof changes,
   a refinement might use a cached value instead of running
   a method on the current state.)

   An alternative approach is to have the [ADT] include invariants
   and the corresponding proofs that methods maintain them as a separate
   fields. This more familiar presentation allows method refinements
   to be defined and then verified interactively during a derivation,
   at the cost of polluting ADT definitions with extra fields. Since
   proofs aren't packaged into the representation in this approach,
   equality suffices for expressing method refinement.

   Yet another approach is to use the bisimulation relation to derive
   an ad hoc invariant for a particular refinement step. The basic idea
   is that the bisimulation relation relates two equal states for which
   the invariant holds. By baking the invariant into the bisimulation
   relation, it becomes a hypothesis to all of our refinement proofs.
   The cost of this approach is that it requires a proof that each mutator
   preserves the invariant on an ad hoc basis, which could leave to some
   duplicate proofs (One way to mitigate this would be to include invariant
   hypotheses around in the context, which we could bake into the honing
   tactics). Otherwise, I [Ben] would argue it includes the best
   of both worlds- there's no need to pollute the definition of [ADT]
   with [repInv] /and/ methods don't have to bother with maintaining
   proofs.

 *)

Section RepInv.

  Variable rep : Type.
  Variable repInv : Ensemble rep.

  (* This is the bisimulation relation we use to mimic invariants-
     the representations are always the same /and/ the invariant holds. *)

  Definition repInvBiR (r_o r_n : rep) :=
    r_o = r_n /\ repInv r_n.

  (* Refining an adt using the [repInvBiR] relation allows us to
   utilize [repInv] when proving method refinement. Of course,
   we also have to show that mutators preserve the invariant.
   Hopefully we can include additional information into the honing
   tactics to avoid reproving invariant preservation.  *)

  Add Parametric Morphism
      mutIdx obsIdx
  : (@Build_ADT rep mutIdx obsIdx)
      with signature
      (pointwise_relation _ (@refineMutator _ _ repInvBiR))
        ==> (pointwise_relation _ (@refineObserver _ _ repInvBiR))
        ==> refineADT
        as refineADT_Build_ADT_RepInv.
  Proof.
    intros; eapply refineADT_Build_ADT_Rep; eauto; reflexivity.
  Qed.

  Lemma refine_pick_repInvBiR :
    forall r_o, repInv r_o ->
    refineEquiv {r_n | repInvBiR r_o r_n}
                (ret r_o).
  Proof.
    unfold repInvBiR; split; intros v CompV; inversion_by computes_to_inv; intuition;
    subst; econstructor; eauto.
  Qed.

  Lemma refine_pick_repInvBiR' :
    forall r_n, repInv r_n ->
    refineEquiv {r_o | repInvBiR r_o r_n}
                (ret r_n).
  Proof.
    unfold repInvBiR; split; intros v CompV; inversion_by computes_to_inv; intuition;
    subst; econstructor; eauto.
  Qed.

End RepInv.

(* A more user-friendly version of [refineADT_Build_ADT_Rep]. *)

Lemma refinesADTRepInv
      adt
      (repInv : Ensemble (Rep adt))
      ObserverMethods'
      MutatorMethods'
      (RefMut : forall idx (r : Rep adt) n,
                  repInv r ->
                  refine
                    (r' <- MutatorMethods adt idx r n;
                     {r'' : Rep adt | repInvBiR repInv r' r''})
                    (MutatorMethods' idx r n))
      (RefObv : forall idx (r : Rep adt) n,
                  repInv r ->
                  refine
                    (ObserverMethods adt idx r n)
                    (ObserverMethods' idx r n))
      (cachedIndex : ObserverIndex adt)
: refineADT adt
            {| Rep := Rep adt;
               MutatorMethods := MutatorMethods';
               ObserverMethods := ObserverMethods'
            |}.
Proof.
  destruct adt.
  eapply refineADT_Build_ADT_RepInv with
  (repInv := repInv); unfold pointwise_relation, repInvBiR in *;
  simpl in *; intros; intuition; subst; eauto.
Qed.

(* Tactic for refining mutators under an invariant. *)

Tactic Notation "hone" "mutator" constr(mutIdx) "using" constr(mutBody)
       "under" "invariant" constr(repInv) :=
    let A :=
        match goal with
            |- Sharpened ?A => constr:(A) end in
    let mutIdx_eq' := fresh in
    let Rep' := eval simpl in (Rep A) in
    let MutatorIndex' := eval simpl in (MutatorIndex A) in
    let ObserverIndex' := eval simpl in (ObserverIndex A) in
    let MutatorMethods' := eval simpl in (MutatorMethods A) in
    let ObserverMethods' := eval simpl in (ObserverMethods A) in
      assert (forall idx idx' : MutatorIndex', {idx = idx'} + {idx <> idx'})
        as mutIdx_eq' by (decide equality);
      let RefineH := fresh in
      assert (pointwise_relation MutatorIndex' (refineMutator (repInvBiR repInv))
                                 (MutatorMethods')
                                 (fun idx => if (mutIdx_eq' idx ()) then
                                               mutBody
                                             else
                                               MutatorMethods' idx)) as RefineH;
        [let mutIdx' := fresh in
         unfold pointwise_relation; intro mutIdx';
         destruct (mutIdx_eq' mutIdx' ()); simpl; intros;
         [idtac | (* Replaced mutator case left to user*)
          subst; idtac] (* Otherwise, they are the same *)
        | eapply SharpenStep;
          [eapply (@refineADT_Build_ADT_RepInv
                     Rep' repInv MutatorIndex' ObserverIndex'
                     MutatorMethods'
                     (fun idx => if (mutIdx_eq' idx ()) then
                                   mutBody
                                 else
                                   MutatorMethods' idx)
                     RefineH
                     ObserverMethods'
                     ObserverMethods')
          | idtac] ]; cbv beta in *; simpl in *.
