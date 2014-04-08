Require Import List String Ensembles
        ADTNotation Program QueryStructureSchema QueryStructure.

(* Definitions for updating query structures. *)

Definition QSInsertSpec
           {QSSchema}
           (qs : QueryStructure QSSchema)
           (idx : qschemaIndex QSSchema)
           (tup : Tuple (schemaHeading (qschemaSchema _ idx)))
           (qs' : QueryStructure QSSchema)
: Prop :=
  (* All of the relations with a different index are untouched
     by insert. *)
  (forall idx',
     idx <> idx' ->
     rel (rels qs idx') = rel (rels qs' idx')) /\
  (* If [tup] is consistent with the schema constraints and the
     cross-relation constraints, it is included in the relation
     indexed by [idx] after insert; that relation is unspecified if
     [tup] does not satisfy either set of constraints. *)
  schemaConstraints (qschemaSchema QSSchema idx) tup
  -> (forall idx',
        qschemaConstraints QSSchema idx idx' tup (rels qs idx'))
  -> rel (rels qs' idx) = tup :: rel (rels qs idx).

Notation "'Insert' b 'into' idx " :=
  (QSInsertSpec qsHint idx%string b)
    (at level 80) : QuerySpec_scope.
