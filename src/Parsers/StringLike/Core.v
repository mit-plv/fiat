(** * Definition of the string-like type *)
Require Import Coq.Arith.Lt Coq.Arith.Compare_dec.

Set Implicit Arguments.
Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.

(** Something is string-like (for a given type of characters) if it
    has an associative concatenation operation and decidable
    equality. *)

Reserved Notation "[ x ]".

Record string_like (CharType : Type) :=
  {
    String :> Type;
    Singleton : CharType -> String where "[ x ]" := (Singleton x);
    Empty : String;
    Concat : String -> String -> String where "x ++ y" := (Concat x y);
    bool_eq : String -> String -> bool;
    bool_eq_correct : forall x y : String, bool_eq x y = true <-> x = y;
    Length : String -> nat;
    Fold : forall (P : String -> Type) (Pnil : P Empty) (Pcons : forall x y, P y -> P (Singleton x ++ y)) (s : String),
             P s;
    Associativity : forall x y z, (x ++ y) ++ z = x ++ (y ++ z);
    LeftId : forall x, Empty ++ x = x;
    RightId : forall x, x ++ Empty = x;
    Singleton_Length : forall x, Length (Singleton x) = 1;
    Length_correct : forall s1 s2, Length s1 + Length s2 = Length (s1 ++ s2);
    Length_Empty : Length Empty = 0;
    Empty_Length : forall s1, Length s1 = 0 -> s1 = Empty;
    Not_Singleton_Empty : forall x, Singleton x <> Empty;
    Fold_compute_empty : forall P Pnil Pcons, Fold P Pnil Pcons Empty = Pnil;
    Fold_compute_cons : forall P Pnil Pcons x s, Fold P Pnil Pcons (Singleton x ++ s) = Pcons x s (Fold P Pnil Pcons s);
    SplitAt : nat -> String -> String * String;
    SplitAt_correct : forall n s, fst (SplitAt n s) ++ snd (SplitAt n s) = s;
    SplitAt_concat_correct : forall s1 s2, SplitAt (Length s1) (s1 ++ s2) = (s1, s2);
    SplitAtLength_correct : forall n s, Length (fst (SplitAt n s)) = min (Length s) n
  }.

Delimit Scope string_like_scope with string_like.
Bind Scope string_like_scope with String.
Arguments Concat {_%type_scope _} (_ _)%string_like.
Arguments bool_eq {_%type_scope _} (_ _)%string_like.
Arguments Length {_%type_scope _} _%string_like.
Arguments SplitAt {_%type_scope _} _%nat_scope _%string_like.
Notation "[[ x ]]" := (@Singleton _ _ x) : string_like_scope.
Infix "++" := (@Concat _ _) : string_like_scope.
Infix "=s" := (@bool_eq _ _) (at level 70, right associativity) : string_like_scope.

Definition str_le {CharType} {String : string_like CharType} (s1 s2 : String)
  := Length s1 < Length s2 \/ s1 = s2.
Infix "≤s" := str_le (at level 70, right associativity).

Definition CharAt {CharType} {String : string_like CharType}
: forall (n : nat) (s : String), n < Length s -> CharType.
Proof.
  intros n s; revert s n.
  refine (Fold _ _ _ _).
  { intros n H; exfalso.
    abstract (
        rewrite Length_Empty in H;
        eapply lt_n_0; eassumption
      ). }
  { intros ch s H n.
    refine (match n with
              | 0 => fun _ => ch
              | S n' => fun H' => H n' _
            end).
    clear -H'.
    abstract (
        rewrite <- Length_correct, Singleton_Length in H';
        apply lt_S_n, H'
      ). }
Defined.

Definition CharAt_option {CharType} {String : string_like CharType} (n : nat) (s : String) : option CharType
  := match lt_dec n (Length s) with
       | left pf => Some (CharAt s pf)
       | right _ => None
     end.

Definition CharAt_default {CharType} {String : string_like CharType} (n : nat) (default : CharType) (s : String)
: CharType
  := match CharAt_option n s with
       | Some ch => ch
       | None => default
     end.

Record StringWithSplitState {CharType} (String : string_like CharType) (split_stateT : String -> Type) :=
  { string_val :> String;
    state_val : split_stateT string_val }.

Definition lift_StringWithSplitState {CharType String A B}
           (s0 : @StringWithSplitState CharType String A)
           (lift : A (string_val s0) -> B (string_val s0))
: @StringWithSplitState CharType String B
  := {| string_val := string_val s0;
        state_val := lift (state_val s0) |}.
