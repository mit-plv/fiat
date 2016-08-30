Require Import
        Coq.Lists.List
        Fiat.Common
        Fiat.Common.ilist2
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.QueryStructure.Specification.Constraints.tupleAgree
        Fiat.QueryStructure.Specification.Constraints.DuplicateFree
        Fiat.Computation.Core
        Fiat.Computation.Refinements.General
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.QueryStructure.Specification.Operations.Query
        Fiat.QueryStructure.Implementation.Constraints.ConstraintChecksRefinements
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.QueryStructure.Automation.Common.

Local Open Scope QuerySpec_scope.

Lemma tupleAgree_equivalence' :
  forall {h} tup1 tup2 attrlist,
    @tupleAgree_computational h tup1 tup2 attrlist <->
    @tupleAgree_computational' h tup1 tup2 attrlist.
Proof.
  induction attrlist; simpl; intros.
  - intuition eauto.
  - destruct attrlist; simpl.
    + intuition.
    + simpl in *; intuition eauto.
Qed.

Lemma agreeAllAttributes_eq
  : forall heading tup tup',
    tupleAgree_computational' tup tup'
                             (allAttributes heading) <-> tup = tup'.
Proof.
  setoid_rewrite <- tupleAgree_equivalence'.
  destruct heading.
  induction AttrList; unfold RawTuple; simpl; intros.
  - destruct tup; destruct tup'; intuition.
  - destruct tup; destruct tup'; simpl.
    intuition.
    + unfold GetAttributeRaw in H0; simpl in H0; unfold ilist2_hd in H0;
      simpl in H0; subst.
      unfold allAttributes in IHAttrList.
      rewrite (proj1 (IHAttrList prim_snd prim_snd0)); eauto; simpl.
      revert H1.
      induction (BuildFinUpTo n); simpl; intuition.
    + injections; eauto.
    + injections.
      generalize (proj2 (IHAttrList prim_snd0 prim_snd0) eq_refl); clear.
      induction (BuildFinUpTo n); simpl; intuition.
Qed.

Lemma refine_DuplicateFree
      {qsSchema}
  : forall (qs : UnConstrQueryStructure qsSchema) Ridx tup',
    (forall tup , tup = tup' \/ tup <> tup')
    -> refine
      {b : bool |
       decides b
               (forall tup : IndexedElement,
                   GetUnConstrRelation qs Ridx tup ->
                   DuplicateFree tup' (indexedElement tup))}
      (xs <- For (UnConstrQuery_In qs Ridx
                           (fun tup => Where (tupleAgree_computational' tup tup' (allAttributes _) )
                                             Return tup));
       ret (If_Opt_Then_Else (hd_error xs) (fun _ => false) true))%comp.
Proof.
  unfold refine; intros.
  computes_to_inv; subst.
  destruct v0; simpl; computes_to_econstructor; simpl; intros.
  unfold not; intro.
  unfold UnConstrQuery_In in H0; simpl; subst.
  apply (For_computes_to_nil (fun tup0 => (tupleAgree_computational' tup0
                                                                    (indexedElement tup)
                        (allAttributes
                           (GetNRelSchemaHeading (qschemaSchemas qsSchema)
                              Ridx)))) _ H0 _ H1).
  apply agreeAllAttributes_eq; eauto.
  intro.
  apply For_computes_to_In with (x := r) in H0; intuition.
  destruct_ex; intuition; subst.
  apply H1 in H3.
  apply agreeAllAttributes_eq in H2; unfold DuplicateFree in *.
  rewrite <- H2 in H3; apply H3; reflexivity.
  rewrite agreeAllAttributes_eq; eapply (H a).
Qed.

Lemma DeleteDuplicateFreeOK {qsSchema}
  : forall (qs : UnConstrQueryStructure qsSchema)
           (Ridx :Fin.t _)
           DeletedTuples,
      refine {b | (forall tup tup',
                      elementIndex tup <> elementIndex tup'
                      -> GetUnConstrRelation qs Ridx tup
                      -> GetUnConstrRelation qs Ridx tup'
                      -> (DuplicateFree (indexedElement tup) (indexedElement tup')))
                  -> decides b (Mutate.MutationPreservesTupleConstraints
                                  (EnsembleDelete (GetUnConstrRelation qs Ridx) DeletedTuples)
                                  DuplicateFree
             )}
             (ret true).
Proof.
  unfold Mutate.MutationPreservesTupleConstraints, DuplicateFree;
  intros * v Comp_v;  computes_to_inv; subst.
  computes_to_constructor; simpl.
  intros.
  unfold EnsembleDelete in *; destruct H1; destruct H2; eauto.
Qed.

Lemma refine_DuplicateFree_symmetry
      {qsSchema}
  : forall (qs : UnConstrQueryStructure qsSchema) Ridx tup' b',
    computes_to {b : bool | decides b
                                     (forall tup : IndexedElement,
                                         GetUnConstrRelation qs Ridx tup ->
                                         DuplicateFree tup' (indexedElement tup)  )} b'
    -> refine
         {b : bool |
          decides b
                  (forall tup : IndexedElement,
                      GetUnConstrRelation qs Ridx tup ->
                      DuplicateFree (indexedElement tup) tup')}
         (ret b').
Proof.
  intros.
  repeat computes_to_inv; computes_to_econstructor.
  computes_to_inv; subst.
  destruct v; simpl in *; unfold DuplicateFree in *; intros.
  intuition eauto.
  intuition eauto.
Qed.

Ltac implement_DuplicateFree :=
  match goal with
    |- refine {b : bool |
                 decides b
                         (forall tup' : IndexedElement,
                             GetUnConstrRelation ?r ?Ridx tup' ->
                                 DuplicateFree ?tup (indexedElement tup'))} _ =>
    rewrite (@refine_DuplicateFree _ r Ridx); [ | intros; repeat decide equality]
  end.

Ltac implement_DuplicateFree_symmetry :=
  match goal with
    |- context [{b : bool |
                 decides b
                         (forall tup' : IndexedElement,
                             GetUnConstrRelation ?r ?Ridx tup' ->
                                 DuplicateFree  (indexedElement tup') ?tup)}] =>
    rewrite (@refine_DuplicateFree_symmetry _ r Ridx)
  end.

Ltac RemoveDeleteDuplicateFreeCheck :=
    match goal with
        |- context[{b | (forall tup tup',
                           elementIndex tup <> elementIndex tup'
                           -> GetUnConstrRelation ?qs ?Ridx tup
                           -> GetUnConstrRelation ?qs ?Ridx tup'
                           -> (DuplicateFree (indexedElement tup) (indexedElement tup')))
                        -> decides b (Mutate.MutationPreservesTupleConstraints
                                        (EnsembleDelete (GetUnConstrRelation ?qs ?Ridx) ?DeletedTuples)
                                        DuplicateFree
                                     )}] =>
        let refinePK := fresh in
        pose proof (DeleteDuplicateFreeOK qs Ridx DeletedTuples) as refinePK;
          simpl in refinePK; pose_string_hyps_in refinePK; pose_heading_hyps_in refinePK;
          setoid_rewrite refinePK; clear refinePK;
          try setoid_rewrite refineEquiv_bind_unit
    end.

Ltac dropDuplicateFree_step :=
  first [
      simplify with monad laws; simpl
    | implement_DuplicateFree; eauto
    | implement_DuplicateFree_symmetry; [ | solve [ eauto] ]
    | rewrite !refine_if_If
    | rewrite refine_If_Then_Else_Duplicate
    | rewrite refine_pick_eq' by eauto
    ].

Ltac dropDuplicateFree :=
  subst; doAny ltac:(dropDuplicateFree_step)
                      rewrite_drill
                      ltac:(try simplify with monad laws; finish honing).
