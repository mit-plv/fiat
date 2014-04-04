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
             Ensemble (Relation (qschemaSchema QSSchema idx));
    crossConstr :
      forall (idx idx' : qschemaIndex QSSchema)
             (tup : Tuple (schemaHeading (qschemaSchema QSSchema idx)))
             (rel1 : @Relation (qschemaSchema QSSchema idx))
             (rel2 : @Relation (qschemaSchema QSSchema idx')),
        rels idx rel1 ->
        rel rel1 tup ->
        qschemaConstraints QSSchema idx idx' tup rel2
  }.

Notation "t 's R" := (rels t {| bstring := R%string |})
                     : QueryStructure_scope.
