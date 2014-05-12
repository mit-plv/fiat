Require Import List String Ensembles Omega
        ADTNotation Program QueryStructureSchema QueryStructure.

(* Notations for queries. *)

Definition Query_In (qs : QueryStructureHint) {A} (R : _)
           (bod : @Tuple (schemaHeading
                           (QSGetNRelSchema qsSchemaHint R%string)) -> Ensemble A)
           (a : A) :=
  exists tup, (GetRelation qsHint R) tup /\
              bod tup a.

Notation "( x 'in' R ) bod" :=
  (Query_In _ (R%string) (fun x => bod)) : QuerySpec_scope.

Definition Query_Return {A : Type} (a a' : A) := (a = a').

Notation "'Return' t" :=
  (Query_Return t%Tuple) : QuerySpec_scope.

Definition Query_Where
           {A : Type} (P : Prop) (bod : Ensemble A) (a : A) :=
  P /\ bod a.

Notation "'Where' p bod" :=
  (Query_Where p%Tuple bod) : QuerySpec_scope.

Definition Query_For {A} (bod : Ensemble A) : Comp (list A) :=
  Pick (fun l : list A => forall a, (List.In a l) <-> In _ bod a).

Notation "'For' bod" := (Query_For bod) : QuerySpec_scope.

(* The spec for a count of the number of tuples in a relation. *)
Definition Count {A} (rows : Comp (list A)) : Comp nat :=
  Bind rows (fun l => ret (List.length l)).
