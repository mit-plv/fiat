Require Export Common Computation.
Require Import Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

(** * Basic ADT definitions *)
(** Type of a mutator method *)
Definition mutatorMethodType (Ty : Type) :=
  Ty    (* Initial model *)
  -> nat (* Actual argument*)
  -> Comp Ty (* Final Model *).

(** Type of an obeserver method *)
Definition observerMethodType (Ty : Type) :=
  Ty    (* Initial model *)
  -> nat (* Actual argument*)
  -> Comp nat. (* Return value *)

(** Interface of an ADT *)
Record ADT :=
  {
    Rep : Type;
    (** The way we model state mathematically *)

    MutatorIndex : Type;
    (** The index set of mutators *)

    ObserverIndex : Type;
    (** The index set of observers *)

    MutatorMethods : MutatorIndex -> mutatorMethodType Rep;
    (** Mutator method implementations *)

    ObserverMethods : ObserverIndex -> observerMethodType Rep
    (** Observer method implementations *)

  }.
