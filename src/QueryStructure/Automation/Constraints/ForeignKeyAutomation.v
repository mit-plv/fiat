Require Export ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureNotations ADTSynthesis.QueryStructure.Specification.Operations.Query.
Require Import Coq.Lists.List Coq.Arith.Compare_dec Coq.Bool.Bool Coq.Strings.String
        ADTSynthesis.Common.BoolFacts
        ADTSynthesis.Common.List.PermutationFacts
        ADTSynthesis.Common.List.ListMorphisms
        ADTSynthesis.QueryStructure.Specification.Operations.FlattenCompList
        ADTSynthesis.Common.Ensembles.EnsembleListEquivalence
        ADTSynthesis.QueryStructure.Implementation.Operations.General.QueryRefinements
        ADTSynthesis.Common.IterateBoundedIndex
        ADTSynthesis.Common.List.ListFacts
        ADTSynthesis.Common.LogicFacts
        ADTSynthesis.Common.DecideableEnsembles
        ADTSynthesis.QueryStructure.Specification.Constraints.tupleAgree
        ADTSynthesis.QueryStructure.Specification.Operations.Mutate
        ADTSynthesis.QueryStructure.Implementation.Constraints.ConstraintChecksRefinements
        ADTSynthesis.QueryStructure.Automation.Common.

Ltac foreignToQuery :=
      match goal with
    | [ |- context[{ b' | decides b' (ForeignKey_P ?AttrID ?AttrID' ?tupmap ?n (@GetUnConstrRelation ?qs_schema ?or ?TableID))}] ]
      =>
      let H' := fresh in
      pose (@refine_constraint_check_into_query
                        qs_schema TableID
                        (fun tup : Tuple => GetAttribute n AttrID = tupmap (GetAttribute tup AttrID')) or _) as H';
        unfold QSGetNRelSchemaHeading in H';
        simpl in *;
        pose_string_hyps; pose_heading_hyps;
        fold_string_hyps_in H'; fold_heading_hyps_in H';
        setoid_rewrite H'; simplify with monad laws; cbv beta; simpl; clear H'
  end.
