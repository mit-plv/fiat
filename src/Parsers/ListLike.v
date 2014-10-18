(** * A Module Type for things like [list] *)
Require Import Coq.Init.Wf Coq.Setoids.Setoid Coq.Structures.Equalities.

Set Implicit Arguments.

Coercion is_true (b : bool) : Prop := b = true.

Module Type ListLike (E : Typ).
  Parameter t : Type.
  Bind Scope list_like_scope with t.
  Delimit Scope list_like_scope with list_like.
  Local Open Scope list_like_scope.

  Parameter empty : t.
  (** The empty list. *)
  Notation "[ ]" := empty : list_like_scope.

  Parameter is_empty : t -> bool.
  (** Test whether a list is empty or not. *)

  Parameter mem : E.t -> t -> bool.
  (** [mem x s] tests whether [x] belongs to the list [s]. *)
  Infix "∈" := mem (at level 20, no associativity) : list_like_scope.
  Notation "y ∉ s" := (negb (y ∈ s)) (at level 20, no associativity) : list_like_scope.

  Parameter add : E.t -> t -> t.
  (** [add x s] returns a list containing all elements of [s], plus
      [x]. If [x] was already in [s], [s] is returned unchanged. *)

  Parameter remove : E.t -> t -> t.
  (** [remove x s] returns a list containing all elements of [s],
      except [x]. If [x] was not in [s], [s] is returned unchanged. *)

  Parameter append : t -> t -> t.
  (** Concatenate two lists. *)

  Infix "++" := append : list_like_scope.

  Parameter lt : t -> t -> Prop.
  (** Is one list smaller than another? *)

  Infix "<" := lt : list_like_scope.

  Axiom lt_wf : well_founded lt.

  Section Spec.
    Variable s s' s'': t.
    Variable x y : E.t.

    (** Specification of [empty] *)
    Parameter empty_1 : forall x, x ∉ empty.

    (** Specification of is_empty *)
    Parameter is_empty_1 : (forall x, x ∉ s) -> is_empty s.
    Parameter is_empty_2 : is_empty s -> (forall x, x ∉ s).

    (** Specification of [add] *)
    Parameter add_1 : x ∈ add x s.
    Parameter add_2 : y ∈ s -> y ∈ add x s.
    Parameter add_3 : y ∉ s -> y ∈ add x s -> y = x.

    (** Specification of [remove] *)
    Parameter remove_1 : x ∉ remove x s.
    Parameter remove_2 : y ∉ remove x s -> y ∈ s -> y = x.
    Parameter remove_3 : y ∈ remove x s -> y ∈ s.

    (** Specification of [append] *)
    Parameter append_1 : x ∈ (s ++ s') = ((x ∈ s) || (x ∈ s'))%bool.

    (** Specification of [lt] *)
    Parameter lt_1 : x ∈ s -> remove x s < s.
    Parameter lt_trans : Transitive lt.
    Global Existing Instance lt_trans.
    Parameter lt_asym : Asymmetric lt.
    Global Existing Instance lt_asym.
  End Spec.

  Hint Resolve empty_1
       is_empty_1 add_1 add_2 remove_1
       remove_2
  : list_like.
  Hint Immediate is_empty_2 add_3
       remove_3
  : list_like.
End ListLike.
