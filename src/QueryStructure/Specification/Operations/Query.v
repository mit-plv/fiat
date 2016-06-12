Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Sets.Ensembles
        Coq.Sorting.Permutation
        Fiat.Computation.Core
        Fiat.ADT.ADTSig Fiat.ADT.Core
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Common.StringBound
        Fiat.ADTNotation.BuildADT
        Fiat.ADTNotation.BuildADTSig
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.QueryStructure.Specification.Operations.FlattenCompList.

Import Lists.List.ListNotations.

(* Notations and definitions for queries.
   The basic idea is to represent queries as ensembles of lists of returned values.
 *)

Open Scope comp_scope.

Definition Query_For {ResultT}
           (bod : Comp (list ResultT)) : Comp (list ResultT) :=
  result <- bod;
  {l | Permutation result l}.

(* [Query_For] is opaque so that the [simplify with monad laws]
   tactic doesn't agressively simplify them away. Computations
   with [Query_For] should be refined using refinement lemmas.
   To prove these lemmas, we'll make [Query_For] locally transparent
   in the file defining them.  *)

Global Opaque Query_For.

Notation "'For' bod" := (Query_For bod) : QuerySpec_scope.

Definition QueryResultComp
           {heading ResultT}
           (queriedEnsemble : Ensemble (@IndexedRawTuple heading))
           (resultEnsemble : @RawTuple heading -> Comp (list ResultT))
  :=
    (* First construct a list that contains each element in the query list
       (expressed as an ensemble) paired with its result list.
       Then flatten the result and compare with [resultList].*)
    queriedList <- {queriedList | UnIndexedEnsembleListEquivalence queriedEnsemble
                                                          queriedList };
    flatten_CompList (map resultEnsemble queriedList).

Definition Query_In {ResultT}
           {qs_schema}
           (qs : QueryStructure qs_schema)
           (R : Fin.t _)
           (bod : @RawTuple (GetNRelSchemaHeading (qschemaSchemas qs_schema) R)
                             -> Comp (list ResultT))
  := QueryResultComp (GetRelation qs R) bod.

Notation "( x 'in' r '!' Ridx ) bod" :=
  (let qs_schema := _ in
   let r' : QueryStructure qs_schema := r in
   let Ridx' := ibound (indexb (@Build_BoundedIndex _ _ (QSschemaNames qs_schema) Ridx%string _)) in
   @Query_In _ qs_schema r' Ridx'
            (fun x : @RawTuple (GetNRelSchemaHeading (qschemaSchemas qs_schema) Ridx') => bod)) : QuerySpec_scope.

(* UnConstrained Query Structure query notations *)

Definition UnConstrQuery_In {ResultT}
           {qsSchema}
           (qs : UnConstrQueryStructure qsSchema)
           (R : Fin.t _)
           (bod : RawTuple -> Comp (list ResultT))
  := QueryResultComp (GetUnConstrRelation qs R) bod.

Notation "( x 'in' r '!' Ridx ) bod" :=
  (let qs_schema : QueryStructureSchema := _ in
   let r' : UnConstrQueryStructure qs_schema := r in
   let Ridx' := ibound (indexb (@Build_BoundedIndex _ _ (QSschemaNames qs_schema) Ridx%string _)) in
   @UnConstrQuery_In _ qs_schema r' Ridx'
            (fun x : @RawTuple (GetNRelSchemaHeading (qschemaSchemas qs_schema) Ridx') => bod)) : QueryImpl_scope.

(* [Query_Return] returns the singleton list. *)
Definition Query_Return {ResultT : Type} (a : ResultT) := ret [a].

Notation "'Return' t" :=
  (Query_Return t%Tuple) : QuerySpec_scope.

Definition Query_Where
           {ResultT : Type} (P : Prop) (bod : Comp (list ResultT)) :=
  {l | (P -> bod ↝ l) /\ (~ P -> l = [])}.

Notation "'Where' p bod" :=
  (Query_Where p%Tuple bod) : QuerySpec_scope.

(*Notation "x <= y " :=
  (InRange x (None, Some y)) : QuerySpec_scope. *)


(* The spec for a count of the number of tuples in a relation. *)
Definition Count {A} (rows : Comp (list A)) : Comp nat :=
  l <- rows;
  ret (List.length l).

Definition foldOption {A: Type} (f : A -> A -> A) seq :=
  match seq with
    | []     => None
    | h :: t => Some (List.fold_left f t h)
  end.

(* Specs for the min and the max of lists of values. *)

Require Import Coq.NArith.NArith Coq.ZArith.ZArith.

Definition FoldAggregateOption {A} (updater: A -> A -> A) (rows: Comp (list A)) :=
  l <- rows;
  ret (foldOption updater l).

Definition FoldAggregate {A B} (updater: A -> B -> A) (default: A) (rows: Comp (list B)) :=
  l <- rows;
  ret (List.fold_left updater l default).

Definition Max (rows : Comp (list nat)) : Comp (option nat) :=
  FoldAggregateOption max rows.

Definition MaxN (rows : Comp (list N)) : Comp (option N) :=
  FoldAggregateOption N.max rows.

Definition MaxZ (rows : Comp (list Z)) : Comp (option Z) :=
  FoldAggregateOption Z.max rows.

Definition Sum  (rows : Comp (list nat)) : Comp nat :=
  FoldAggregate plus 0 rows.

Definition SumN (rows : Comp (list N)) : Comp N :=
  FoldAggregate N.add 0%N rows.

Definition SumZ (rows : Comp (list Z)) : Comp Z :=
  FoldAggregate Z.add 0%Z rows.

(*
Definition MinN (rows : Comp (list N)) : Comp (option N) :=
  FoldAggregateOption N.min rows.

Definition MinZ (rows : Comp (list Z)) : Comp (option Z) :=
  FoldAggregateOption Z.min rows.
*)

(* Much like [Query_For], [Count] is opaque so that the
   [simplify with monad laws] tactic doesn't agressively
   simplify it away.  *)

Global Opaque Count Max MaxN MaxZ Sum SumN SumZ.
