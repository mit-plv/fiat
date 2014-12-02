Require Import Coq.Lists.List Coq.Strings.String Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        ADTSynthesis.Common.ilist ADTSynthesis.Common.StringBound Coq.Program.Program ADTSynthesis.Common.Ensembles.IndexedEnsembles
        ADTSynthesis.QueryStructure.Schema ADTSynthesis.QueryStructure.Heading ADTSynthesis.QueryStructure.Tuple.

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
