Require Import List String Ensembles Omega
        ADTNotation Program QueryStructureSchema QueryStructure.

(* Notations for queries. *)

(* This typeclass allows our 'in' notation to avoid
   mentioning the QueryStructure. *)

Instance Astring_eq : Query_eq string := {| A_eq_dec := string_dec |}.
Instance Anat_eq : Query_eq nat := {| A_eq_dec := eq_nat_dec |}.

Class QueryStructureHint :=
  { qsSchemaHint : QueryStructureSchema;
    qsHint :> @QueryStructure qsSchemaHint
  }.

Notation "( x 'in' R ) bod" :=
  (fold_right (@app _) nil
              (map (fun x :Tuple (schemaHeading
                                    (qschemaSchema
                                       qsSchemaHint R%string))
                    => bod)
                   (rel (rels qsHint R%string)))) : QuerySpec_scope.

Notation "'Return' t" :=
  (cons t%Tuple nil) : QuerySpec_scope.

Notation "'Where' p bod" :=
  (if p%Tuple then bod else nil) : QuerySpec_scope.

Notation "'For' bod" :=
  (fun l => l = bod)
  : QuerySpec_scope.

(* The spec for a count of the number of tuples in a relation. *)
Definition Count {Schema} (R : Ensemble (list Schema)) (n : nat) :=
  exists l, R l /\ n = List.length l.
