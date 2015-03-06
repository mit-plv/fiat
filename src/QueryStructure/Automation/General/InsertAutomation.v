Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List
        Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        ADTSynthesis.Computation
        ADTSynthesis.ADT
        ADTSynthesis.ADTRefinement
        ADTSynthesis.ADTNotation
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureSchema
        ADTSynthesis.ADTRefinement.BuildADTRefinements
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructure
        ADTSynthesis.Common.Ensembles.IndexedEnsembles
        ADTSynthesis.Common.IterateBoundedIndex
        ADTSynthesis.QueryStructure.Specification.Operations.Query
        ADTSynthesis.QueryStructure.Specification.Operations.Insert
        ADTSynthesis.QueryStructure.Implementation.Constraints.ConstraintChecksRefinements
        ADTSynthesis.QueryStructure.Implementation.Operations.General.InsertRefinements
        ADTSynthesis.QueryStructure.Automation.Constraints.TrivialConstraintAutomation
        ADTSynthesis.QueryStructure.Automation.Constraints.FunctionalDependencyAutomation
        ADTSynthesis.QueryStructure.Automation.Constraints.ForeignKeyAutomation.

(* When we insert a tuple into a relation which has another relation has
     a foreign key into, we need to show that we haven't messed up any
     references (which is, of course, trivial. We should bake this into
     our the [QSInsertSpec_refine'] refinement itself by filtering out the
     irrelevant constraints somehow, but for now we can use the following
     tactic to rewrite them away. *)

  Ltac remove_trivial_insertion_constraints :=
    match goal with
        |- context[EnsembleInsert _ (GetUnConstrRelation _ _) ] =>
        match goal with
            AbsR : @DropQSConstraints_AbsR ?schm ?or ?nr
            |- context [
                   Pick
                     (fun b =>
                        decides
                          b
                          (forall tup' : @IndexedTuple ?heading,
                             (@GetUnConstrRelation ?schm ?r ?Ridx) tup' ->
                             ForeignKey_P (relSchema := ?heading') ?attr ?attr' ?tup_map
                                          (indexedElement tup')
                                          (EnsembleInsert ?tup (GetUnConstrRelation ?r ?Ridx'))))] =>
            let neq := fresh in
            assert (Ridx <> Ridx') by (subst_strings; discriminate);
              let ForeignKeys_OK := fresh in
              assert (forall tup' : @IndexedTuple heading,
                        (@GetUnConstrRelation schm r Ridx) tup' ->
                        ForeignKey_P (heading := heading) (relSchema := heading') attr attr' tup_map
                                     (indexedElement tup')
                                     (GetUnConstrRelation r Ridx')) as
                  ForeignKeys_OK by
                    (intro tup'; rewrite <- AbsR, !GetRelDropConstraints;
                     eapply (@crossConstr _ or Ridx Ridx' tup'); discriminate);
                let refine_trivial := fresh in
                pose
                  (@InsertForeignKeysCheck schm nr Ridx Ridx' attr attr' tup_map tup
                                           ForeignKeys_OK neq) as refine_trivial;
                  subst_strings; setoid_rewrite refine_trivial; clear refine_trivial;
                  pose_string_ids; simplify with monad laws
        end end.

Tactic Notation "remove" "trivial" "insertion" "checks" :=
  (* Move all the binds we can outside the exists / computes
   used for abstraction, stopping when we've rewritten
         the bind in [QSInsertSpec]. *)
  repeat rewrite refineEquiv_bind_bind;
  etransitivity;
  [ repeat (apply refine_bind;
            [reflexivity
            | match goal with
                | |- context [Bind (Insert _ into _)%QuerySpec _] =>
                  unfold pointwise_relation; intros
                    end
                 ] );
    (* Pull out the relation we're inserting into and then
     rewrite [QSInsertSpec] *)
    match goal with
        H : DropQSConstraints_AbsR _ ?r_n
        |- context [(QSInsert _ ?R ?n)%QuerySpec] =>
        let H' := fresh in
          (* If we try to eapply [QSInsertSpec_UnConstr_refine] directly
                   after we've drilled under a bind, this tactic will fail because
                   typeclass resolution breaks down. Generalizing and applying gets
                   around this problem for reasons unknown. *)
        let H' := fresh in
        pose proof (@QSInsertSpec_UnConstr_refine_opt
                      _ r_n R n _ H) as H';
          apply H'
    end
  | cbv beta; simpl tupleConstraints; simpl attrConstraints; cbv iota;
    simpl map; simpl app;
    simpl relName in *; simpl schemaHeading in *;
    pose_string_ids; simpl;
    simplify with monad laws;
    try rewrite <- GetRelDropConstraints;
    repeat match goal with
             | H : DropQSConstraints_AbsR ?qs ?uqs |- _ =>
               rewrite H in *
           end
  ].

Tactic Notation "Split" "Constraint" "Checks" :=
  repeat (let b := match goal with
                     | [ |- context[if ?X then _ else _] ] => constr:(X)
                     | [ H : context[if ?X then _ else _] |- _ ]=> constr:(X)
                   end in
          let b_eq := fresh in
          eapply (@refine_if _ _ b); intros b_eq;
          simpl in *; repeat rewrite b_eq; simpl).

Tactic Notation "implement" "failed" "insert" :=
  repeat (rewrite refine_pick_val, refineEquiv_bind_unit; eauto);
  reflexivity.

Ltac drop_constraints_from_insert methname :=
  hone method methname;
  [ remove trivial insertion checks;
    (* The trivial insertion checks involve the fresh id,
       so we need to drill under the binder before
       attempting to remove them. *)
    rewrite refine_bind;
    [ | reflexivity |
      unfold pointwise_relation; intros; subst_strings;
      repeat remove_trivial_insertion_constraints;
      subst_strings;
      (* These simplify and implement nontrivial constraint checks *)
      repeat first
             [setoid_rewrite FunctionalDependency_symmetry at 1;
               try setoid_rewrite if_duplicate_cond_eq
             | fundepToQuery; try simplify with monad laws
             | foreignToQuery; try simplify with monad laws
             | setoid_rewrite refine_trivial_if_then_else; simplify with monad laws
             ];
             higher_order_reflexivity ];
    finish honing
  | ].


Tactic Notation "drop" "constraints" "from" "insert" constr(methname) :=
  drop_constraints_from_insert methname.
