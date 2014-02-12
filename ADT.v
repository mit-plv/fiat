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

(** Correctness property for mutators: Mutators should maintain
   representation invariants. **)
Definition mutatorInv rep (repInv : Ensemble rep) mutIdx mutators :=
  forall (idx : mutIdx) (r : rep) (n : nat),
    repInv r -> computational_inv repInv (mutators idx r n).

Arguments mutatorInv rep repInv mutIdx mutators /.

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

    MutatorMethodsInv : mutatorInv RepInv MutatorMethods
    (** Mutator methods maintain Representation Invariants **)

    (** We probably want some sort of observer method specs as well.
     That can wait until the next iteration of the ADT with arbitrary signatures. **)

  }.
