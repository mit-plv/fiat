Require Import List String Ensembles
        Computation.Core
        ADT.ADTSig ADT.Core
        ADTNotation.StringBound ADTNotation.BuildADT ADTNotation.BuildADTSig
        QueryStructure.QueryStructureSchema  QueryStructure.QueryStructure
        EnsembleListEquivalence.

(* Notations and definitions for queries.
   The basic idea is to represent queries as ensembles of lists of returned values.
 *)

Open Scope comp.

Definition QueryResultEquiv
           {QueryT ResultT}
           (queriedEnsemble : Ensemble QueryT)
           (resultEnsemble : QueryT -> Ensemble (list ResultT))
           (resultList : list ResultT)
  :=
    (* First construct a list that contains each element in the query list
       (expressed as an ensemble) paired with its result list.
       Then flatten the result and compare with [resultList].*)
    exists queriedList : list (QueryT * (list ResultT)),
       (forall el : QueryT * (list ResultT),
          List.In el queriedList <->
          (In _ queriedEnsemble (fst el) /\ In _ (resultEnsemble (fst el)) (snd el)))
       /\ resultList = flatten (map snd queriedList).

Definition Query_In (qs : QueryStructureHint) {ResultT} (R : _)
           (bod : @Tuple (schemaHeading
                            (QSGetNRelSchema qsSchemaHint' R))
                  -> Ensemble (list ResultT))
           (results : list ResultT) :=
  QueryResultEquiv (GetUnConstrRelation (DropQSConstraints qsHint) R) bod results.

Notation "( x 'in' R ) bod" :=
  (Query_In _ {| bindex := R%string |} (fun x => bod)) : QuerySpec_scope.

(* [Query_Return] terminates the trace with a unit value. *)
Definition Query_Return {A : Type} (a : A) (el : list A) := (el = [a]).

Notation "'Return' t" :=
  (Query_Return t%Tuple) : QuerySpec_scope.

Definition Query_Where
           {A : Type} (P : Prop) (bod : Ensemble (list A)) (a : list A) :=
  P /\ bod a.

Notation "'Where' p bod" :=
  (Query_Where p%Tuple bod) : QuerySpec_scope.

Definition Query_For {ResultT}
           (bod : Ensemble (list ResultT)) : Comp (list ResultT) :=
  {l | bod l}.

Notation "'For' bod" := (Query_For bod) : QuerySpec_scope.

(* The spec for a count of the number of tuples in a relation. *)
Definition Count {A} (rows : Comp (list A)) : Comp nat :=
  l <- rows;
  ret (List.length l).
