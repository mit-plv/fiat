Require Import List String Ensembles
        ADTNotation Program QueryStructureSchema QueryStructure.

(* Notations for queries. *)

(* This typeclass allows our 'in' notation to avoid
   mentioning the QueryStructure. *)

Class QueryStructureHint :=
  { qsSchemaHint : QueryStructureSchema;
     qsHint :> @QueryStructure qsSchemaHint
  }.

Notation "( x 'in' R ) bod" :=
  (fun bx =>
     exists r x, R%QueryStructure r /\
                 rel r x /\
                 (bod bx)%QuerySpec) : QuerySpec_scope.

Notation "'Return' t" :=
  (fun rx => rx = t%Tuple) : QuerySpec_scope.

Notation "'Where' p bod" :=
  (fun wx => p%Tuple /\ (bod wx)%QuerySpec) : QuerySpec_scope.

Notation "'For' bod 'returning' sch" :=
  (@Build_Relation
    sch bod%QuerySpec (fun _ _ => I))
  : QuerySpec_scope.

(* The spec for a count of the number of tuples in a relation.  *)
Definition Count {Schema} (R : Relation Schema) (n : nat) :=
  forall tup l,
    (List.In tup l <-> rel R tup) <->
    n = List.length l.
