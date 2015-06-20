Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Logic.FunctionalExtensionality
        Coq.Sets.Ensembles
        Fiat.Common.StringBound
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.QueryStructure.Specification.Representation.Schema
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple.

(* A relation is a set of tuples (described by a proposition)
   which satisfy the schema constraints. *)

Record RawRelation (RelationSchema : RawSchema) :=
  { rawRel : @IndexedEnsemble (@RawTuple (rawSchemaHeading RelationSchema));
    rawAttrconstr :
      match (attrConstraints RelationSchema) with
        | Some Constr =>
          forall tup,
            rawRel tup -> Constr (indexedRawTuple tup)
        | None => True
      end;
    rawTupleconstr :
      match (tupleConstraints RelationSchema) with
        | Some Constr =>
          forall tup tup',
            elementIndex tup <> elementIndex tup'
            -> rawRel tup
            -> rawRel tup'
            -> Constr (indexedRawTuple tup) (indexedRawTuple tup')
        | None => True
      end
  }.

Definition RawUnConstrRelation (RelationSchema : RawHeading) :=
  Ensemble (@IndexedRawTuple RelationSchema).

Definition UnIndexedRawTupleIn {heading}
           (rel : @IndexedEnsemble (@RawTuple heading))
           (tup : @RawTuple heading):=
  exists n, rel {| elementIndex := n;
                   indexedElement := tup |}.

Definition Relation (RelationSchema : Schema) :=
  RawRelation RelationSchema.

Definition UnConstrRelation (RelationSchema : Heading) :=
  Ensemble (@IndexedTuple RelationSchema).

Definition UnIndexedTupleIn {heading}
           (rel : @IndexedEnsemble (@Tuple heading))
           (tup : @Tuple heading):=
  exists n, rel {| elementIndex := n;
                   indexedElement := tup |}.
