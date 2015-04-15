Require Import Coq.Lists.List Coq.Strings.String Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Fiat.Common.ilist Fiat.Common.StringBound Coq.Program.Program Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.QueryStructure.Specification.Representation.Schema Fiat.QueryStructure.Specification.Representation.Heading Fiat.QueryStructure.Specification.Representation.Tuple.

(* A relation is a collection of tuples (described by a proposition)
   which satisfy the schema constraints. *)

Record Relation (RelationSchema : Schema) :=
  { rel : @IndexedEnsemble (@Tuple (schemaHeading RelationSchema));
    attrconstr :
      match (attrConstraints RelationSchema) with
        | Some Constr =>
          forall tup,
            rel tup -> Constr (indexedTuple tup)
        | None => True
      end;
    tupleconstr :
      match (tupleConstraints RelationSchema) with
        | Some Constr =>
          forall tup tup',
            elementIndex tup <> elementIndex tup'
            -> rel tup
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
