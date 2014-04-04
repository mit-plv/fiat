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
  (forall idx' (rel : Relation (qschemaSchema QSSchema idx')),
     idx <> idx' ->
     rels qs idx' rel <-> rels qs' idx' rel) /\
  (* If [tup] is consistent with the schema constraints and the
     cross-relation constraints, it is included in the relation
     indexed by [idx] after insert; that relation is unspecified if
     [tup] does not satisfy either set of constraints. *)
  schemaConstraints (qschemaSchema QSSchema idx) tup
  -> (forall idx' (rel' : Relation (qschemaSchema QSSchema idx')),
        rels qs idx' rel'
        -> qschemaConstraints QSSchema idx idx' tup rel')
  -> forall (tup' : Tuple (schemaHeading (qschemaSchema _ idx)))
            (rel' : Relation (qschemaSchema QSSchema idx)),
       rels qs' idx rel' ->
       (* A tuple [tup'] included in the modified relation [rel']
          iff it is equal to [tup] or it was included in the original
          relation [rel]. *)
       (rel rel' tup' ->
        tup = tup' \/
        exists rel'' : Relation (qschemaSchema QSSchema idx),
          rels qs idx rel'' /\ rel rel'' tup') /\
       (tup = tup' -> rel rel' tup') /\
       (forall rel'' : Relation (qschemaSchema QSSchema idx),
          rels qs idx rel'' -> rel rel'' tup' -> rel rel' tup').

Notation "'Insert' b 'into' idx 'of' r " :=
  (QSInsertSpec r {| bstring := idx%string |} b)
    (at level 80) : QuerySpec_scope.
