Require Import List String FunctionalExtensionality Ensembles
        ADTNotation.ilist ADTNotation.StringBound Program Schema.

(* Definitions and notations for specifying structures
   that support querying and insertion operations. *)

(* Notations for queries. *)

Delimit Scope Relation_scope with Relation.

Notation "( x 'in' r ) bod" :=
  (fun a => ex (fun x => r x /\ (bod a)%Relation))
    (right associativity, at level 0) : Relation_scope.

Notation "'Return' t" :=
  (fun a : nat => a = t)
    (right associativity, at level 0) : Relation_scope.

Notation "'Where' p bod" :=
  (fun x => p /\ (bod x)%Relation)
    (right associativity, at level 0, x at level 0, p at level 0) : Relation_scope.

Notation "'For' bod" :=
  (fun a => bod%Relation a)
    (right associativity, at level 0) : Relation_scope.

Check (fun x => and True ((Return 5)%Relation x)).
Check (fun R R' : Ensemble nat =>
         For (x in R)
             (y in R')
         Where (x = y)
             (Return x))%Relation.

    For
    Where True
    (Return 5))%Relation.

Check ((Return 5)%Relation).

Check (Where True True True True True).

Check (For (Where I (Return 5)%Relation)%Relation)%Relation.

Notation "'for' x .. y 'where' " :=
  (x )
    (at level 70).

Section QuerySpec.

  Definition SetSpec A := Ensemble A.

  Notation
