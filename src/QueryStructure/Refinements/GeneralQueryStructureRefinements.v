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

Tactic Notation "start" "honing" "QueryStructure" :=
  pose_string_ids;
  match goal with
      |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _] =>
      hone representation using (@DropQSConstraints_AbsR Rep);
        repeat (pose_string_ids;
                match goal with
                    |- context [(meth ?R (_ : rep , _ : _ ) : _ :=
                                   {_ | forall or : QueryStructure _,
                                          DropQSConstraints_AbsR or _ -> _})%methDef] =>
                    first [ drop constraints from query R
                          | drop constraints from insert R ]
                end)
    end.
