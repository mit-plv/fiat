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
        ADTSynthesis.QueryStructure.Implementation.Constraints.ConstraintChecksRefinements.

Ltac dec_tauto :=
    clear; intuition eauto;
    eapply Tuple_Agree_eq_dec;
    match goal with
      | [ |- ?E = true ] => case_eq E; intuition idtac; [ exfalso ]
    end;
    match goal with
      | [ H : _ |- _ ] => apply Tuple_Agree_eq_dec' in H; solve [ eauto ]
    end.

Ltac prove_decidability_for_functional_dependencies :=
  simpl; econstructor; intros;
  try setoid_rewrite <- eq_nat_dec_bool_true_iff;
  try setoid_rewrite <- eq_N_dec_bool_true_iff;
  try setoid_rewrite <- eq_Z_dec_bool_true_iff;
  try setoid_rewrite <- string_dec_bool_true_iff;
  setoid_rewrite and_True;
  repeat progress (
           try setoid_rewrite <- andb_true_iff;
           try setoid_rewrite not_true_iff_false;
           try setoid_rewrite <- negb_true_iff);
  rewrite bool_equiv_true;
  reflexivity.

Hint Extern 100 (DecideableEnsemble _) => prove_decidability_for_functional_dependencies : typeclass_instances.

Tactic Notation "refine" "existence" "check" "into" "query" :=
      match goal with
          |- context[{b | decides b
                                  (exists tup : @IndexedTuple ?heading,
                                     (@GetUnConstrRelation ?qs_schema ?qs ?tbl tup /\ @?P tup))}]
          =>
          let H1 := fresh in
          let H2 := fresh in
            makeEvar (Ensemble (@Tuple heading))
                     ltac:(fun P' => assert (Same_set (@IndexedTuple heading) (fun t => P' (indexedElement t)) P) as H1;
            [unfold Same_set, Included, Ensembles.In;
              split; [intros x H; pattern (indexedElement x);
                      match goal with
                          |- ?P'' (indexedElement x) => unify P' P'';
                            simpl; eauto
                      end
                     | eauto]
            |
            assert (DecideableEnsemble P') as H2;
              [ simpl; eauto with typeclass_instances (* Discharge DecideableEnsemble w/ intances. *)
              | setoid_rewrite (@refine_constraint_check_into_query' qs_schema tbl qs P P' H2 H1); clear H1 H2 ] ]) end.

Ltac fundepToQuery :=
  match goal with
    | [ |- context[Pick
                     (fun b => decides
                                 b
                                 (forall tup', GetUnConstrRelation ?or ?Ridx _
                                               -> @FunctionalDependency_P ?heading ?attrlist1 ?attrlist2 ?n _))] ] =>
      let H' := fresh in
      let H'' := fresh in
      let refine_fundep := fresh in
      assert ((forall tup' : IndexedTuple,
                 GetUnConstrRelation or Ridx tup'
                 -> @FunctionalDependency_P heading attrlist1 attrlist2 n (indexedElement tup'))
              <-> (forall tup' : IndexedTuple,
                     ~ (GetUnConstrRelation or Ridx tup'
                        /\ tupleAgree n (indexedElement tup') attrlist2
                        /\ ~ tupleAgree n (indexedElement tup') attrlist1))) as H'
          by (unfold FunctionalDependency_P; dec_tauto);
        assert (DecideableEnsemble (fun x : Tuple =>
                                      tupleAgree_computational n x attrlist2 /\
                                      ~ tupleAgree_computational n x attrlist1)) as H''
          by prove_decidability_for_functional_dependencies;
        pose proof (@refine_functional_dependency_check_into_query _ _ n attrlist2 attrlist1 or H'' H')
          as refine_fundep; simpl in refine_fundep; setoid_rewrite refine_fundep; clear refine_fundep H'' H'
    | [ |- context[Pick
                     (fun b => decides
                                 b
                                 (forall tup', GetUnConstrRelation ?or ?Ridx _
                                               -> @FunctionalDependency_P ?heading ?attrlist1 ?attrlist2 _ ?n ))] ] =>
      let H' := fresh in
      let H'' := fresh in
      let refine_fundep := fresh in
      assert ((forall tup' : IndexedTuple,
                 GetUnConstrRelation or Ridx tup'
                 -> @FunctionalDependency_P heading attrlist1 attrlist2 (indexedElement tup') n)
              <-> (forall tup' : IndexedTuple,
                     ~ (GetUnConstrRelation or Ridx tup'
                        /\ tupleAgree (indexedElement tup') n attrlist2
                        /\ ~ tupleAgree (indexedElement tup') n attrlist1))) as H'
          by (unfold FunctionalDependency_P; dec_tauto);
        assert (DecideableEnsemble (fun x : Tuple =>
                                      tupleAgree_computational x n attrlist2 /\
                                      ~ tupleAgree_computational x n attrlist1)) as H''
          by prove_decidability_for_functional_dependencies;
        pose proof (@refine_functional_dependency_check_into_query' _ _ n attrlist2 attrlist1 or H'' H') as refine_fundep; simpl in refine_fundep; setoid_rewrite refine_fundep; clear refine_fundep H'' H'
  end; try simplify with monad laws.
