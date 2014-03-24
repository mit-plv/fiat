Require Export Common Computation ADTNotation.ilist.

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

    ObserverDomCod : ObserverIndex -> (Type * Type)
     (** The representation-independent piece of the
         domain and codomain of observer methods. **)

  }.
