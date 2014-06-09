Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation BuildADTRefinements
        QueryStructureSchema QueryStructure
        QueryQSSpecs InsertQSSpecs EmptyQSSpecs
        GeneralInsertRefinements GeneralQueryRefinements.

Tactic Notation "start" "honing" "QueryStructure" :=
  match goal with
      |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _] =>
      hone representation using (@DropQSConstraints_SiR Rep);
        repeat (match goal with
                    |- context [(meth ?R (_ : rep , _ : _ ) : _ :=
                                   {_ | forall or : QueryStructure _,
                                          DropQSConstraints_SiR or _ -> _})%methDef] =>
                    first [ drop constraints from query R
                          | drop constraints from insert R ]
                end)
    end.
