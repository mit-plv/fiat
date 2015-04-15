Require Import Coq.Strings.String Coq.Lists.List Coq.Sorting.Permutation
        Coq.Bool.Bool Coq.Sets.Ensembles
        Coq.Logic.FunctionalExtensionality
        Fiat.ADTNotation Fiat.Common
        Fiat.Common.List.ListFacts
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Common.DecideableEnsembles
        Fiat.Computation
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Specification.Operations.FlattenCompList
        Fiat.QueryStructure.Specification.Operations.Query
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.QueryStructure.Implementation.Operations.General.QueryRefinements
        Fiat.QueryStructure.Automation.Common.

Tactic Notation "drop" "constraints" "from" "query" :=
  simplify with monad laws;
  repeat match goal with
             |- appcontext[@Query_In ?ResultT ?qs ?R] =>
             let H' := fresh in
             pose (@DropQSConstraintsQuery_In ResultT qs R) as H';
               simpl in H'; fold_string_hyps_in H'; fold_heading_hyps_in H';
               setoid_rewrite H'; clear H'
         end;
  repeat match goal with
             |- context[fun b :?B => @Query_In ?ResultT ?qs ?R (@?bod b)] =>
             let H' := fresh in
             pose (@DropQSConstraintsQuery_In_UnderBinder ResultT B qs R bod) as H';
               simpl in H'; fold_string_hyps_in H'; fold_heading_hyps_in H';
               setoid_rewrite H'; clear H'
         end;
    simpl;
    setoid_rewrite refineEquiv_pick_eq';
    simplify with monad laws; cbv beta; simpl;
    match goal with
        H : DropQSConstraints_AbsR _ _ |- _ =>
        unfold DropQSConstraints_AbsR in H; rewrite H
    end; pose_string_hyps; pose_heading_hyps;
    finish honing.
