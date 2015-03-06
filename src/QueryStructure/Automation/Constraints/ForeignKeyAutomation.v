Require Export ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureNotations ADTSynthesis.QueryStructure.Specification.Operations.Query.
Require Import Coq.Lists.List Coq.Arith.Compare_dec Coq.Bool.Bool String
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
        ADTSynthesis.QueryStructure.Implementation.Constraints.ConstraintChecksRefinements.

Ltac foreignToQuery :=
  match goal with
    | [ |- context[{ b' | decides b' (ForeignKey_P ?AttrID ?AttrID' ?tupmap ?n (@GetUnConstrRelation ?qs_schema ?or ?TableID))}] ]
      =>
      setoid_rewrite (@refine_constraint_check_into_query
                        qs_schema TableID
                        (fun tup : Tuple => n AttrID = tupmap (tup AttrID')) or _);
        simplify with monad laws; cbv beta; simpl
  end.
