Require Import List String FunctionalExtensionality Ensembles
        ADTNotation.ilist ADTNotation.StringBound Program Schema
        Tuple.

(* A relation is a collection of tuples (described by a proposition)
   which satisfy the schema constraints. *)

Record Relation (RelationSchema : Schema) :=
  { rel : Ensemble (@IndexedTuple (schemaHeading RelationSchema));
    constr :
      forall tup tup',
        rel tup ->
        rel tup' ->
        schemaConstraints RelationSchema tup tup'
  }.

Definition UnConstrRelation (RelationSchema : Schema) :=
  Ensemble (@IndexedTuple (schemaHeading RelationSchema)).

Definition UnIndexedTupleIn {heading}
           (rel : Ensemble (@IndexedTuple heading))
           (tup : @Tuple heading):=
  exists n, rel {|tupleIndex := n;
                  indexedTuple := tup |}.
