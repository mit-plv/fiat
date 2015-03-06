Require Import Coq.Strings.String Coq.Lists.List Coq.Sorting.Permutation
        Coq.Bool.Bool Coq.Sets.Ensembles
        Coq.Logic.FunctionalExtensionality
        ADTSynthesis.ADTNotation ADTSynthesis.Common
        ADTSynthesis.Common.List.ListFacts
        ADTSynthesis.Common.Ensembles.IndexedEnsembles
        ADTSynthesis.Common.DecideableEnsembles
        ADTSynthesis.Computation
        ADTSynthesis.ADTRefinement.BuildADTRefinements
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureSchema
        ADTSynthesis.QueryStructure.Specification.Operations.FlattenCompList
        ADTSynthesis.QueryStructure.Specification.Operations.Query
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructure
        ADTSynthesis.QueryStructure.Implementation.Operations.General.QueryRefinements.

Tactic Notation "drop" "constraints" "from" "query" constr(methname) :=
  hone method methname;
  [ simplify with monad laws;
    subst_strings; repeat (setoid_rewrite DropQSConstraintsQuery_In; simpl);
    repeat setoid_rewrite DropQSConstraintsQuery_In_UnderBinder;
    simpl; pose_string_ids;
    setoid_rewrite refineEquiv_pick_eq';
    simplify with monad laws; cbv beta; simpl;
    match goal with
        H : DropQSConstraints_AbsR _ _ |- _ =>
        unfold DropQSConstraints_AbsR in H; rewrite H
    end;
    finish honing | ].
