Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation BuildADTRefinements
        QueryStructureSchema QueryStructure
        QueryQSSpecs InsertQSSpecs EmptyQSSpecs
        GeneralInsertRefinements GeneralQueryRefinements.

Ltac subst_strings :=
  repeat match goal with
           | [ H : string |- _ ] => subst H
         end.

Ltac pose_string_ids :=
  subst_strings;
  repeat match goal with
           | |- context [String ?R ?R'] =>
             let str := fresh "StringId" in
             set (String R R') as str in *
         end.

Lemma Constructor_DropQSConstraints {MySchema} {Dom}
: forall oldConstructor (d : Dom),
    refine
      (or' <- oldConstructor d;
       {nr' |
          DropQSConstraints_AbsR (qsSchema := MySchema) or' nr'})
        (or' <- oldConstructor d;
         ret (DropQSConstraints or')).
Proof.
  unfold refine; intros; inversion_by computes_to_inv.
  repeat econstructor; eauto.
Qed.

(* Queries over an empty relation return empty lists. *)
Lemma refine_For_In_Empty  :
  forall ResultT MySchema R bod,
    refine (Query_For (@UnConstrQuery_In ResultT MySchema
                                   (DropQSConstraints (QSEmptySpec MySchema))
                                   R bod))
           (ret []).
Proof.
  intros; rewrite refine_For.
  simplify with monad laws.
  unfold In, DropQSConstraints, GetUnConstrRelation in *.
  rewrite <- ith_Bounded_imap.
  unfold QSEmptySpec; simpl rels.
  rewrite Build_EmptyRelation_IsEmpty; simpl.
  rewrite refine_pick_val with
  (A := list (IndexedTuple)) (a := [])
    by (repeat econstructor; eauto).
  simplify with monad laws.
  rewrite refine_pick_val with
  (A := list ResultT) (a := []); reflexivity.
Qed.

Tactic Notation "start" "honing" "QueryStructure" :=
  pose_string_ids;
  match goal with
      |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _] =>
      hone representation using (@DropQSConstraints_AbsR Rep);
        match goal with
            |- context [Build_consDef (@Build_consSig ?Id _)
                                      (@absConstructor _ _ _ _ _)] =>
            hone constructor Id;
              [ etransitivity;
                [apply Constructor_DropQSConstraints |
                 simplify with monad laws; finish honing]
              | ]
        end; pose_string_ids;
        repeat (match goal with
                    |- context [Build_methDef (@Build_methSig ?Id _ _)
                                              (@absMethod _ _ _ _ _ _)] =>
                    first [ drop constraints from query Id
                          | drop constraints from insert Id ]
                end; pose_string_ids)
  end.
