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
             Ensemble (@Relation (qschemaSchema QSSchema idx));
    constr :
      forall (idx idx' : qschemaIndex QSSchema)
             (rel : @Relation (qschemaSchema QSSchema idx))
             (rel' : @Relation (qschemaSchema QSSchema idx')),
        qschemaConstraints QSSchema idx idx' rel rel'
  }.
