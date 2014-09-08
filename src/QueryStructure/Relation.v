Require Import List String FunctionalExtensionality Ensembles
        Common.ilist ADTNotation.StringBound Program Schema
        Heading Tuple.

(* A relation is a collection of tuples (described by a proposition)
   which satisfy the schema constraints. *)

Record Relation (RelationSchema : Schema) :=
  { rel : Ensemble (@IndexedTuple (schemaHeading RelationSchema));
    constr :
      match (schemaConstraints RelationSchema) with
        | Some Constr =>
         forall tup tup',
           rel tup -> rel tup' -> Constr tup tup'
        | None => True
      end
  }.

Definition UnConstrRelation (RelationSchema : Heading) :=
  Ensemble (@IndexedTuple RelationSchema).

Definition UnIndexedTupleIn {heading}
           (rel : Ensemble (@IndexedTuple heading))
           (tup : @Tuple heading):=
  exists n, rel {|tupleIndex := n;
                  indexedTuple := tup |}.
