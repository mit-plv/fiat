Require Export Common Computation.
Require Import Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

Local Open Scope type_scope.

(** * Basic ADT definitions *)
(** Type of a context *)
Definition Build_ADTContext
           (rep mutIdx obsIdx : Type)
           (mutDom : mutIdx -> Type)
           (obsDom obsCod : obsIdx -> Type): Context :=
  {| names := mutIdx + obsIdx;
     dom idx := rep *
                match idx with
                  | inl mIdx => mutDom mIdx
                  | inr oIdx => obsDom oIdx
                end;
     cod idx := match idx with
                  | inl mIdx => rep
                  | inr oIdx => obsCod oIdx
                end |}.

(** Type of a mutator method *)
Definition mutatorMethodTypeUnbundled (Ty mutIdx obsIdx dom : Type)
           (mutDom : mutIdx -> Type)
           (obsDom obsCod : obsIdx -> Type)
           (* we give a [Context] here so typeclass resolution can pick it up *)
           (ctx := Build_ADTContext Ty mutDom obsDom obsCod)
  := Ty    (* Initial model *)
     -> dom (* Actual argument*)
     -> Comp Ty (* Final Model *).

(** Type of an obeserver method *)
Definition observerMethodTypeUnbundled (Ty mutIdx obsIdx dom cod : Type)
           (mutDom : mutIdx -> Type)
           (obsDom obsCod : obsIdx -> Type)
           (* we give a [Context] here so typeclass resolution can pick it up *)
           (ctx := Build_ADTContext Ty mutDom obsDom obsCod)
  := Ty    (* Initial model *)
     -> dom (* Actual argument*)
     -> Comp cod. (* Return value *)

(** Type of a mutator method bundled with its context *)
Definition mutatorMethodType (Ty dom : Type)
  := Ty    (* Initial model *)
     -> dom (* Actual argument*)
     -> BundledComp Ty (* Final Model *).

(** Type of an obeserver method *)
Definition observerMethodType (Ty dom cod : Type)
  := Ty    (* Initial model *)
     -> dom (* Actual argument*)
     -> BundledComp cod. (* Return value *)

(** Interface of an ADT *)
Record ADT :=
  {
    Rep : Type;
    (** The representation type of the ADT **)

    MutatorIndex : Type;
    (** The index set of mutators *)

    ObserverIndex : Type;
    (** The index set of observers *)

    MutatorDom : MutatorIndex -> Type;

    ObserverDom : ObserverIndex -> Type;

    ObserverCod : ObserverIndex -> Type;

    UnbundledMutatorMethods :
      forall idx : MutatorIndex,
        mutatorMethodTypeUnbundled Rep (MutatorDom idx)
                                   MutatorDom ObserverDom ObserverCod;
    (** Mutator method implementations *)

    UnbundledObserverMethods :
      forall idx : ObserverIndex,
        observerMethodTypeUnbundled Rep (ObserverDom idx) (ObserverCod idx)
                                    MutatorDom ObserverDom ObserverCod
    (** Observer method implementations *)

  }.

Definition ADTLookupContext (A : ADT) : LookupContext
  := {| LContext := Build_ADTContext (Rep A) (MutatorDom A) (ObserverDom A) (ObserverCod A);
        lookup idx := match idx with
                        | inl mIdx => fun state_value =>
                                        UnbundledMutatorMethods A mIdx (fst state_value) (snd state_value)
                        | inr oIdx => fun state_value =>
                                        UnbundledObserverMethods A oIdx (fst state_value) (snd state_value)
                      end |}.

Definition MutatorMethods (A : ADT) (i : MutatorIndex A)
: mutatorMethodType (Rep A) (MutatorDom A i)
  := fun m x => ``[ UnbundledMutatorMethods A i m x with ADTLookupContext A ]`` .

Definition ObserverMethods (A : ADT) (i : ObserverIndex A)
: observerMethodType (Rep A) (ObserverDom A i) (ObserverCod A i)
  := fun m x => ``[ UnbundledObserverMethods A i m x with ADTLookupContext A ]``.
