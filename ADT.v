Require Export Common Computation.

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

    RepInv : Rep -> Prop;
    (** Invariants on the Representation **)

    MutatorIndex : Type;
    (** The index set of mutators *)

    ObserverIndex : Type;
    (** The index set of observers *)

    MutatorMethods : MutatorIndex -> mutatorMethodType Rep;
    (** Mutator method implementations *)

    ObserverMethods : ObserverIndex -> observerMethodType Rep;
    (** Observer method implementations *)

    MutatorMethodsInv : forall idx r n, RepInv r -> computational_inv RepInv (MutatorMethods idx r n)
    (** Mutator methods maintain Representation Invariants **)

    (** We probably want some sort of observer method specs as well.
     That can wait until the next iteration of the ADT with arbitrary signatures. **)

  }.
