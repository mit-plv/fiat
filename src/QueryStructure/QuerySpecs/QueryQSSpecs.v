Require Import List String Ensembles Sorting.Permutation
        Computation.Core
        ADT.ADTSig ADT.Core
        ADTNotation.StringBound ADTNotation.BuildADT ADTNotation.BuildADTSig
        QueryStructure.QueryStructureSchema  QueryStructure.QueryStructure
        EnsembleListEquivalence.

(* Notations and definitions for queries.
   The basic idea is to represent queries as ensembles of lists of returned values.
 *)

Open Scope comp.

Definition Query_For {ResultT}
           (bod : Comp (list ResultT)) : Comp (list ResultT) :=
  result <- bod;
  {l | Permutation result l}.

Notation "'For' bod" := (Query_For bod) : QuerySpec_scope.

Definition flatten_CompList {A} (c : list (Comp (list A))) :=
  fold_right (fun (b : Comp (list A)) (a : Comp (list A)) =>
                l <- b;
              l' <- a;
              ret (l ++ l')) (ret []) c.

Definition QueryResultComp
           {QueryT ResultT}
           (queriedEnsemble : Ensemble QueryT)
           (resultEnsemble : QueryT -> Comp (list ResultT))
  :=
    (* First construct a list that contains each element in the query list
       (expressed as an ensemble) paired with its result list.
       Then flatten the result and compare with [resultList].*)
    queriedList <- {queriedList | EnsembleListEquivalence queriedEnsemble queriedList };
    flatten_CompList (map resultEnsemble queriedList).

Definition Query_In (qs : QueryStructureHint) {ResultT} (R : _)
           (bod : @Tuple (schemaHeading
                            (QSGetNRelSchema qsSchemaHint' R))
                  -> Comp (list ResultT)) :=
  QueryResultComp (GetUnConstrRelation (DropQSConstraints qsHint) R) bod.

Notation "( x 'in' R ) bod" :=
  (Query_In _ {| bindex := R%string |} (fun x => bod)) : QuerySpec_scope.

(* [Query_Return] returns the singleton list. *)
Definition Query_Return {ResultT : Type} (a : ResultT) := ret [a].

Notation "'Return' t" :=
  (Query_Return t%Tuple) : QuerySpec_scope.

Definition Query_Where
           {ResultT : Type} (P : Prop) (bod : Comp (list ResultT)) :=
  {l | P -> bod ↝ l /\ ~ P -> l = []}.

Notation "'Where' p bod" :=
  (Query_Where p%Tuple bod) : QuerySpec_scope.

(* The spec for a count of the number of tuples in a relation. *)
Definition Count {A} (rows : Comp (list A)) : Comp nat :=
  l <- rows;
  ret (List.length l).
