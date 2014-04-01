Require Import List String FunctionalExtensionality Ensembles
        ADTNotation.ilist ADTNotation.StringBound Program Schema Tuple.

(* A relation is a collection (described by a proposition)
   of tuples which satisfy the schema constraints. *)

Record Relation {RelationSchema : Schema} :=
  { rel : Ensemble (Tuple (schemaHeading RelationSchema));
    constr :
      forall tup,
        rel tup -> schemaConstraints RelationSchema tup
  }.
