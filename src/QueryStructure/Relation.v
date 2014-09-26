Require Import List String FunctionalExtensionality Ensembles
        Common.ilist Common.StringBound Program IndexedEnsembles
        Schema Heading Tuple.

(* A relation is a collection of tuples (described by a proposition)
   which satisfy the schema constraints. *)

Record Relation (RelationSchema : Schema) :=
  { rel : @IndexedEnsemble (@Tuple (schemaHeading RelationSchema));
    constr :
      match (schemaConstraints RelationSchema) with
        | Some Constr =>
         forall tup tup',
           rel tup 
           -> rel tup' 
           -> Constr (indexedTuple tup) (indexedTuple tup')
        | None => True
      end
  }.

Definition UnConstrRelation (RelationSchema : Heading) :=
  Ensemble (@IndexedTuple RelationSchema).

Definition UnIndexedTupleIn {heading}
           (rel : @IndexedEnsemble (@Tuple heading))
           (tup : @Tuple heading):=
  exists n, rel {| elementIndex := n;
                   indexedElement := tup |}.
