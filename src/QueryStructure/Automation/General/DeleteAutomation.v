Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Fiat.Common.List.ListFacts
        Fiat.Computation
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.ADT
        Fiat.ADTRefinement Fiat.ADTNotation
        Fiat.QueryStructure.Specification.Representation.Schema
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.QueryStructure.Specification.Operations.Query
        Fiat.QueryStructure.Specification.Operations.Delete
        Fiat.QueryStructure.Specification.Operations.Mutate
        Fiat.QueryStructure.Implementation.Constraints.ConstraintChecks.DuplicateFree
        Fiat.QueryStructure.Implementation.Constraints.ConstraintChecksRefinements
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.DecideableEnsembles
        Fiat.Common.List.PermutationFacts
        Fiat.QueryStructure.Implementation.Operations.General.QueryRefinements
        Fiat.QueryStructure.Implementation.Operations.General.MutateRefinements
        Fiat.QueryStructure.Implementation.Operations.General.DeleteRefinements
        Fiat.QueryStructure.Automation.Common
        Fiat.Common.Ensembles.EnsembleListEquivalence.

Ltac RemoveDeleteFunctionalDependencyCheck :=
    match goal with
        |- context[{b | (forall tup tup',
                           elementIndex tup <> elementIndex tup'
                           -> GetUnConstrRelation ?qs ?Ridx tup
                           -> GetUnConstrRelation ?qs ?Ridx tup'
                           -> (FunctionalDependency_P ?attrlist1 ?attrlist2 (indexedElement tup) (indexedElement tup')))
                        -> decides b (Mutate.MutationPreservesTupleConstraints
                                        (EnsembleDelete (GetUnConstrRelation ?qs ?Ridx) ?DeletedTuples)
                                        (FunctionalDependency_P ?attrlist1 ?attrlist2)
                                     )}] =>
        let refinePK := fresh in
        pose proof (DeletePrimaryKeysOK qs Ridx DeletedTuples attrlist1 attrlist2) as refinePK;
          simpl in refinePK; pose_string_hyps_in refinePK; pose_heading_hyps_in refinePK;
          setoid_rewrite refinePK; clear refinePK;
          try setoid_rewrite refineEquiv_bind_unit
    end.

  Ltac ImplementDeleteForeignKeysCheck :=
    match goal with
        [ |- context [{b' |
                       ?P ->
                       decides b'
                               (Mutate.MutationPreservesCrossConstraints
                                  (@GetUnConstrRelation ?qs_schema ?qs ?Ridx')
                                  (EnsembleDelete (GetUnConstrRelation ?qs ?Ridx) ?DeletedTuples)
                                  (ForeignKey_P ?attr' ?attr ?tupmap))}] ]
        =>
        let refineFK := fresh in
        pose proof  (@DeleteForeignKeysCheck qs_schema qs Ridx Ridx' DeletedTuples
                                             _ attr attr' tupmap) as refineFK;
          simpl in refineFK;  pose_string_hyps_in refineFK; pose_heading_hyps_in refineFK;
          setoid_rewrite refineFK;
          [ clear refineFK; try simplify with monad laws
          | let tup := fresh "tup" in
            let tup' := fresh "tup'" in
            let tupAgree' := fresh "tupAgree'" in
            let tupIn := fresh "tupIn" in
            unfold tupleAgree; intros tup tup' tupAgree' tupIn;
            rewrite tupAgree' in *;
            [ eauto
            | simpl; intuition]
          | auto with typeclass_instances
          | clear; intuition
          | clear; simpl; intros; congruence ]
  end.

Tactic Notation "remove" "trivial" "deletion" "checks" :=
  repeat rewrite refineEquiv_bind_bind;
  etransitivity;
  [ repeat (apply refine_bind;
            [reflexivity
            | match goal with
                | |- context [Bind (Delete _ from _ ! _ where _)%QuerySpec _] =>
                  unfold pointwise_relation; intros
              end
           ] );
    (* Pull out the relation we're inserting into and then
     rewrite [QSInsertSpec] *)
    match goal with
        H : DropQSConstraints_AbsR ?r_o ?r_n
        |- context [QSDelete ?qs ?R ?P] =>
        (* If we try to eapply [QSInsertSpec_UnConstr_refine] directly
                   after we've drilled under a bind, this tactic will fail because
                   typeclass resolution breaks down. Generalizing and applying gets
                   around this problem for reasons unknown. *)
        let H' := fresh "H'" in
        pose proof (@QSDeleteSpec_UnConstr_refine_opt
                      _ r_n R P r_o H) as H';
          simpl in H'; fold_heading_hyps_in H'; fold_string_hyps_in H';
          apply H'
    end
  | pose_string_hyps; pose_heading_hyps;
    cbv beta iota delta [tupleConstraints attrConstraints map app
                                          relName schemaHeading];
    simpl; simplify with monad laws;
    repeat rewrite <- GetRelDropConstraints;
    repeat match goal with
             | H : DropQSConstraints_AbsR ?qs ?uqs |- _ =>
               rewrite H in *
           end
  ].

Ltac drop_constraints_from_delete :=
remove trivial deletion checks;
    (* Implement constraint checks. *)
    repeat
      first [RemoveDeleteFunctionalDependencyCheck
            | ImplementDeleteForeignKeysCheck
            | setoid_rewrite refine_trivial_if_then_else; simplify with monad laws];
    pose_string_hyps; pose_heading_hyps; finish honing.

Tactic Notation "drop" "constraints" "from" "delete" constr(methname) :=
  hone method methname;
  [ drop_constraints_from_delete
  | ].

Ltac implement_QSDeleteSpec :=
  match goal with
    H : DropQSConstraints_AbsR ?r_o ?r_n
    |- refine (u <- QSDelete ?r_o ?Ridx ?DeletedTuples;
               @?k u) _ =>
    eapply (@QSDeleteSpec_refine_subgoals _ _ r_o r_n Ridx _ _ _ _ DeletedTuples k); try exact H
  end; try set_refine_evar;
  [ simpl;
    repeat first
           [ rewrite decides_2_True
           | RemoveDeleteDuplicateFreeCheck
           | RemoveDeleteFunctionalDependencyCheck]
  | simpl;
    repeat first
           [ rewrite decides_2_True
           | ImplementDeleteForeignKeysCheck ]
  | simpl; intros; set_refine_evar
  | simpl; intros; set_refine_evar
  ].
