(* Definition of the finite set spec *)
Require Import Coq.Sets.Ensembles
    Fiat.ADT.Core
    Fiat.Common.Ensembles
    Fiat.ADT.ComputationalADT
    Fiat.ADTNotation.
Require Export Fiat.FiniteSetADTs.BedrockWord.

Set Implicit Arguments.

Local Open Scope string_scope.

(** TODO: Test: Do we get a speedup if we replace these definitions
    with [{| bindex := "$STRING-HERE" |}]? *)
Definition sEmpty := "Empty".
Definition sAdd := "Add".
Definition sRemove := "Remove".
Definition sIn := "In".
Definition sSize := "Size".

Definition cardinal (S : Ensemble W) : Comp W
  := (n <- { n : nat | cardinal _ S n };
      ret (from_nat n)).

(** We define the interface for finite sets *)
(** QUESTION: Does Facade give us any other methods?  Do we want to
    provide any other methods? *)
Definition FiniteSetSig : ADTSig :=
  ADTsignature {
      Constructor sEmpty : unit -> rep,
      Method sAdd : rep x W -> rep x unit,
      Method sRemove : rep x W -> rep x unit,
      Method sIn : rep x W -> rep x bool,
      Method sSize : rep x unit -> rep x W
    }.

(** And now the spec *)
Definition FiniteSetSpec : ADT FiniteSetSig :=
  ADTRep (Ensemble W) {
    Def Constructor sEmpty (_ : unit) : rep := ret (Empty_set _),

    Def Method sAdd (xs : rep , x : W) : unit :=
      ret (Add _ xs x, tt),

    Def Method sRemove (xs : rep , x : W) : unit :=
      ret (Subtract _ xs x, tt),

    Def Method sIn (xs : rep , x : W) : bool :=
        (b <- { b : bool | b = true <-> Ensembles.In _ xs x };
         ret (xs, b)),

    Def Method sSize (xs : rep , _ : unit) : W :=
          (n <- cardinal xs;
           ret (xs, n))
  }.
