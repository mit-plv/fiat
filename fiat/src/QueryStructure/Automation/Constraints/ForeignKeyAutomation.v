Require Export Fiat.QueryStructure.Specification.Representation.QueryStructureNotations Fiat.QueryStructure.Specification.Operations.Query.
Require Import Coq.Lists.List Coq.Arith.Compare_dec Coq.Bool.Bool Coq.Strings.String
        Fiat.Common.BoolFacts
        Fiat.Common.List.PermutationFacts
        Fiat.Common.List.ListMorphisms
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.QueryStructure.Specification.Operations.FlattenCompList
        Fiat.Common.Ensembles.EnsembleListEquivalence
        Fiat.QueryStructure.Implementation.Operations.General.QueryRefinements
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.List.ListFacts
        Fiat.Common.LogicFacts
        Fiat.Common.DecideableEnsembles
        Fiat.QueryStructure.Specification.Constraints.tupleAgree
        Fiat.QueryStructure.Specification.Operations.Mutate
        Fiat.QueryStructure.Implementation.Constraints.ConstraintChecksRefinements
        Fiat.QueryStructure.Automation.Common.

Ltac foreignToQuery :=
  match goal with
  | [ |- context[{ b' | decides b' (ForeignKey_P ?AttrID ?AttrID' ?tupmap ?n (@GetUnConstrRelation ?qs_schema ?or ?TableID))}] ]
    =>
    let H' := fresh in
    let H' :=
        eval simpl in (@refine_constraint_check_into_query
                         qs_schema TableID
                         (fun tup : RawTuple => GetAttributeRaw n AttrID = tupmap (GetAttributeRaw tup AttrID')) or _) in
        pose_string_hyps; pose_heading_hyps;
                      (* fold_string_hyps_in H'; fold_heading_hyps_in H'; *)
                      setoid_rewrite H'; simplify with monad laws; cbv beta; simpl
  end.

Ltac foreignToQuery' :=
  match goal with
  | [ |- context[{ b' | decides b' (@ForeignKey_P ?heading ?relSchema ?AttrID ?AttrID' ?tupmap ?n (@GetUnConstrRelation ?qs_schema ?or ?TableID))}] ]
    =>
    let H' := fresh in
    (* This let gets around a weird bug in type checking the refine_constraint_check_into_query *)
    let f := constr:(fun tup : @RawTuple heading => @GetAttributeRaw heading n AttrID = tupmap (@GetAttributeRaw relSchema tup AttrID')) in
    let H' :=
        eval simpl in
    (@refine_constraint_check_into_query
       qs_schema TableID
       f or _) in
        pose_string_hyps; pose_heading_hyps;
    (* fold_string_hyps_in H'; fold_heading_hyps_in H'; *)
    setoid_rewrite H'; try simplify with monad laws; cbv beta; simpl
  end.
