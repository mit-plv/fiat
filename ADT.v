Require Export Common Computation.
Require Import Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

Local Open Scope type_scope.

(** * Basic ADT definitions *)
(** Type of a context *)

(** Type of a mutator method. *)
Definition mutatorMethodType (Ty dom : Type)
  := Ty    (* Initial model *)
     -> dom (* Actual argument*)
     -> Comp Ty (* Final Model *).

(** Type of an obeserver method. *)
Definition observerMethodType (Ty dom cod : Type)
  := Ty    (* Initial model *)
     -> dom (* Actual argument*)
     -> Comp cod. (* Return value *)

Record ADTSig :=
  { MutatorIndex : Type;
     (** The index set of mutators *)

     ObserverIndex : Type;
     (** The index set of observers *)

     MutatorDom : MutatorIndex -> Type;
     (** The representation-independent piece of the
         domain of mutator methods. **)

    ObserverDom : ObserverIndex -> Type;
     (** The representation-independent piece of the
         domain of observer methods. **)

    ObserverCod : ObserverIndex -> Type
     (** The codomain of observer methods. **)

  }.

(** Interface of an ADT *)
Record ADT (Sig : ADTSig) :=
  {
    Rep : Type;
    (** The representation type of the ADT **)

    MutatorMethods :
      forall idx : MutatorIndex Sig,
        mutatorMethodType Rep (MutatorDom Sig idx);
    (** Mutator method implementations *)

    ObserverMethods :
      forall idx : ObserverIndex Sig,
        observerMethodType Rep (ObserverDom Sig idx) (ObserverCod Sig idx)
    (** Observer method implementations *)

  }.
