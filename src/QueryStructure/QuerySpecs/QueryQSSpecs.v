Require Import List String Ensembles
        Computation.Core
        ADT.ADTSig ADT.Core
        ADTNotation.StringBound ADTNotation.BuildADT ADTNotation.BuildADTSig
        QueryStructure.QueryStructureSchema  QueryStructure.QueryStructure
        EnsembleListEquivalence.

(* Notations and definitions for queries.
   The basic idea is to represent queries as ensembles of
   returned values paired with a trace of the tuples that produced it.
   [Query_For] projects out the returned values from a list equivalent to
   this ensemble. Traces are unique since the tuples are pulled from ensembles,
   guaranteeing the standard SQL semantics.

   If new query syntax is introduced that violates the uniqueness of traces,
   things might not behave as expected.
 *)

Open Scope comp.

Definition Query_In (qs : QueryStructureHint) {ReturnT TraceT} (R : _)
           (bod : @Tuple (schemaHeading
                           (QSGetNRelSchema qsSchemaHint' R))
                  -> Ensemble (ReturnT * TraceT))
           (el : ReturnT * (Tuple * TraceT)) :=
  GetUnConstrRelation (DropQSConstraints qsHint) R (fst (snd el))
  /\ bod (fst (snd el)) (fst el, snd (snd el)).

Notation "( x 'in' R ) bod" :=
  (Query_In _ {| bindex := R%string |} (fun x => bod)) : QuerySpec_scope.

(* [Query_Return] terminates the trace with a unit value. *)
Definition Query_Return {A : Type} (a : A) (el : A * unit) := (fst el = a).

Notation "'Return' t" :=
  (Query_Return t%Tuple) : QuerySpec_scope.

Definition Query_Where
           {A : Type} (P : Prop) (bod : Ensemble A) (a : A) :=
  P /\ bod a.

Notation "'Where' p bod" :=
  (Query_Where p%Tuple bod) : QuerySpec_scope.

Definition Query_For {ReturnT TraceT}
           (bod : Ensemble (ReturnT * TraceT)) : Comp (list ReturnT) :=
  {l | exists l', l = map fst l' /\ EnsembleListEquivalence bod l'}.

Notation "'For' bod" := (Query_For bod) : QuerySpec_scope.

(* The spec for a count of the number of tuples in a relation. *)
Definition Count {A} (rows : Comp (list A)) : Comp nat :=
  l <- rows;
  ret (List.length l).
