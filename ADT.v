Require Export Common Computation.

Generalizable All Variables.
Set Implicit Arguments.

(** * Basic ADT definitions *)
(** Hoare logic-style total correctness specification of a mutator method *)
Definition mutatorMethodSpec (Ty : Type) :=
  Ty    (* Initial model *)
  -> nat (* Actual argument*)
  -> Ty (* Final model *)
  (*  -> nat (* Return value *) *)
  -> Prop.

(** Hoare logic-style total correctness specification of an obeserver method *)
Definition observerMethodSpec (Ty : Type) :=
  Ty    (* Initial model *)
  -> nat (* Actual argument*)
  (*  -> Ty (* Final model *) *)
  -> nat (* Return value *)
  -> Prop.

(** Interface of an ADT *)
Record ADT :=
  {
    Model : Type;
    (** The way we model state mathematically *)

    MutatorIndex : Type;
    (** The index set of mutators *)

    ObserverIndex : Type;
    (** The index set of observers *)

    MutatorMethodSpecs : MutatorIndex -> mutatorMethodSpec Model;
    (** A specification for each mutator method *)

    ObserverMethodSpecs : ObserverIndex -> observerMethodSpec Model
  (** A specification for each observer method *)
  }.

(** Implementation type of a method *)
Definition methodTypeD funcs (State : Type) :=
  State -> nat -> Comp funcs (State * nat).

(** Usual Hoare logic notion of implementating a mutator method spec *)

Definition mutatorMethodCorrect
           funcs denote_funcs
           (Model State : Type)
           (ms : mutatorMethodSpec Model)
           (RepInv : Model -> State -> Prop)
           (mb : methodTypeD funcs State)
  := forall m s,
       RepInv m s
       -> forall x,
            let s'y := mb s x in
            forall s'y_value,
              @computes_to funcs denote_funcs _ s'y s'y_value
              -> exists m', RepInv m' (fst s'y_value)
                            /\ ms m x m'
                            /\ (snd s'y_value) = 0.

Definition observerMethodCorrect
           funcs denote_funcs
           (Model State : Type)
           (ms : observerMethodSpec Model)
           (RepInv : Model -> State -> Prop)
           (mb : methodTypeD funcs State)
  := forall m s,
       RepInv m s
       -> forall x,
            let s'y := mb s x in
            forall s'y_value,
              @computes_to funcs denote_funcs _ s'y s'y_value
              -> RepInv m (fst s'y_value)
                 /\ ms m x (snd s'y_value).
