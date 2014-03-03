Require Export Common Computation.
Require Import Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

Local Open Scope type_scope.

(** * Basic ADT definitions *)
(** Type of a context *)
Definition Build_ADTContext (rep mutIdx obsIdx : Type) : Context :=
  {| names := mutIdx + obsIdx;
     dom idx := rep * nat;
     cod idx := match idx with
                  | inl mIdx => rep
                  | inr oIdx => nat
                end |}.

(** Type of a mutator method *)
Definition mutatorMethodTypeUnbundled (Ty mutIdx obsIdx : Type)
           (* we give a [Context] here so typeclass resolution can pick it up *)
           (ctx := Build_ADTContext Ty mutIdx obsIdx)
  := Ty    (* Initial model *)
     -> nat (* Actual argument*)
     -> Comp Ty (* Final Model *).

(** Type of an obeserver method *)
Definition observerMethodTypeUnbundled (Ty mutIdx obsIdx : Type)
           (* we give a [Context] here so typeclass resolution can pick it up *)
           (ctx := Build_ADTContext Ty mutIdx obsIdx)
  := Ty    (* Initial model *)
     -> nat (* Actual argument*)
     -> Comp nat. (* Return value *)

(** Type of a mutator method bundled with its context *)
Definition mutatorMethodType (Ty : Type)
  := Ty    (* Initial model *)
     -> nat (* Actual argument*)
     -> BundledComp Ty (* Final Model *).

(** Type of an obeserver method *)
Definition observerMethodType (Ty : Type)
  := Ty    (* Initial model *)
     -> nat (* Actual argument*)
     -> BundledComp nat. (* Return value *)

(** Interface of an ADT *)
Record ADT :=
  {
    Rep : Type;
    (** The way we model state mathematically *)

    MutatorIndex : Type;
    (** The index set of mutators *)

    ObserverIndex : Type;
    (** The index set of observers *)

    UnbundledMutatorMethods : MutatorIndex -> mutatorMethodTypeUnbundled Rep MutatorIndex ObserverIndex;
    (** Mutator method implementations *)

    UnbundledObserverMethods : ObserverIndex -> observerMethodTypeUnbundled Rep MutatorIndex ObserverIndex
    (** Observer method implementations *)

  }.

Definition ADTLookupContext (A : ADT) : LookupContext
  := {| LContext := Build_ADTContext (Rep A) (MutatorIndex A) (ObserverIndex A);
        lookup idx := match idx with
                        | inl mIdx => fun state_value =>
                                        UnbundledMutatorMethods A mIdx (fst state_value) (snd state_value)
                        | inr oIdx => fun state_value =>
                                        UnbundledObserverMethods A oIdx (fst state_value) (snd state_value)
                      end |}.

Definition MutatorMethods (A : ADT) (i : MutatorIndex A) : mutatorMethodType (Rep A)
  := fun m x => ``[ UnbundledMutatorMethods A i m x with ADTLookupContext A ]``.
Definition ObserverMethods (A : ADT) (i : ObserverIndex A) : observerMethodType (Rep A)
  := fun m x => ``[ UnbundledObserverMethods A i m x with ADTLookupContext A ]``.
