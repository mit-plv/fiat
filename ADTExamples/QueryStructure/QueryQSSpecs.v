Require Import List String Ensembles Omega
        ADTNotation Program QueryStructureSchema QueryStructure.

(* Notations for queries. *)

Notation "( x 'in' R ) bod" :=
  (fold_right (@app _) nil
              (map (fun x : Tuple
                              (schemaHeading
                                 (GetNamedSchema qsSchemaHint R%string))
                    => bod)
                   (GetRelation qsHint R%string))) : QuerySpec_scope.

Notation "'Return' t" :=
  (cons t%Tuple nil) : QuerySpec_scope.

Notation "'Where' p bod" :=
  (if p%Tuple then bod else nil) : QuerySpec_scope.

Notation "'For' bod" := (bod)
  : QuerySpec_scope.

(* The spec for a count of the number of tuples in a relation. *)
Definition Count {Schema} (R : list Schema) := List.length R.
