Require Import List String FunctionalExtensionality Ensembles
        ADTNotation.ilist ADTNotation.StringBound Program.
Require Export
        ADTExamples.QueryStructure.Notations
        Heading Tuple Schema Relation QueryStructureSchema.

(* A Query Structure is a collection of relations
   (described by a proposition) which satisfy the
   schema and the cross-relation constraints. *)

Record QueryStructure (QSSchema : QueryStructureSchema) :=
  { rels : forall idx : qschemaIndex QSSchema,
             Relation (qschemaSchema QSSchema idx);
    crossConstr :
      forall (idx idx' : qschemaIndex QSSchema)
             (tup : Tuple (schemaHeading (qschemaSchema QSSchema idx))),
        List.In tup (rel (rels idx)) ->
        qschemaConstraints QSSchema idx idx' tup (rels idx')
  }.

Notation "t ! R" := (rels t R%string): QueryStructure_scope.
