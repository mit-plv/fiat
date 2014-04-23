Require Import List String Ensembles Omega
        ADTNotation Program QueryStructureSchema QueryStructure.

(* Notations for queries. *)

Definition Query_In (qs : QueryStructureHint) {A} (R : string)
           (bod : Tuple (schemaHeading
                           (QSGetNRelSchema qsSchemaHint R%string)) -> list A) :=
  fold_right (@app _) (@nil _)
              (map bod (GetUnConstrRelation qsHint R%string)).

Notation "( x 'in' R ) bod" :=
  (Query_In _ (R%string) (fun x => bod)) : QuerySpec_scope.

Definition Query_Return {A : Type} (a : A) := (cons a nil).

Notation "'Return' t" :=
  (Query_Return t%Tuple) : QuerySpec_scope.

Definition Query_Where
           {A : Type} {B B' : Prop} (p : {B} + {B'}) (bod : list A) :=
  if p%Tuple then bod else nil.

Notation "'Where' p bod" :=
  (Query_Where p%Tuple bod) : QuerySpec_scope.

Definition Query_For {A} (bod : list A) := bod.

Notation "'For' bod" := (Query_For bod) : QuerySpec_scope.

(* The spec for a count of the number of tuples in a relation. *)
Definition Count {Schema} (R : list Schema) := List.length R.
