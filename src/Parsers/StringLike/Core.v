(** * Definition of the string-like type *)
Require Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions (* for [relation] *).
Require Import Coq.Classes.Morphisms (* for [==>] / [respectful] *).

Local Coercion is_true : bool >-> Sortclass.

Global Set Keyed Unification. (* Makes [rewrite] faster in 8.5 / 8.6; we put it hear to not have to deal with compatibility issues in other files *)
Global Set Asymmetric Patterns.

Set Implicit Arguments.
Generalizable All Variables.

(** Something is string-like if it has a type of characters, and can
    be split. *)

Reserved Notation "[ x ]".

Module Export StringLike.
  Class StringLikeMin {Char : Type} :=
    {
      String :> Type;
      char_at_matches : nat -> String -> (Char -> bool) -> bool;
      unsafe_get : nat -> String -> Char;
      length : String -> nat
    }.

  Class StringLike {Char : Type} {HSLM : @StringLikeMin Char} :=
    {
      is_char : String -> Char -> bool;
      take : nat -> String -> String;
      drop : nat -> String -> String;
      get : nat -> String -> option Char;
      bool_eq : String -> String -> bool;
      beq : relation String := fun x y => bool_eq x y
    }.

  Class StringIso {Char} {HSLM : @StringLikeMin Char} :=
    {
      of_string : list Char -> String
    }.

  Arguments StringLikeMin : clear implicits.
  Arguments StringLike Char {HSLM}.
  Arguments StringIso Char {HSLM}.
  Bind Scope string_like_scope with String.
  Delimit Scope string_like_scope with string_like.
  Infix "=s" := (@beq _ _ _) (at level 70, no associativity) : type_scope.
  Infix "=s" := (@bool_eq _ _ _) (at level 70, no associativity) : string_like_scope.
  Notation "s ~= [ ch ]" := (is_char s ch) (at level 70, no associativity) : string_like_scope.
  Local Open Scope string_like_scope.
  Local Open Scope type_scope.

  Definition fold' {Char} {HSLM} {HSL : @StringLike Char HSLM} {A}
             (f : Char -> A -> A)
             (init : A)
             (str : String) (len : nat)
  : A
    := nat_rect
         (fun _ => A)
         init
         (fun len' acc
          => match get (length str - S len') str with
               | Some ch => f ch acc
               | None => init
             end)
         len.

  Definition fold {Char} {HSLM} {HSL : @StringLike Char HSLM} {A}
             (f : Char -> A -> A)
             (init : A)
             (str : String)
  : A
    := fold' f init str (length str).

  Definition fold_lookahead' {Char} {HSLM} {HSL : @StringLike Char HSLM} {A}
             (f : Char -> option Char -> A -> A)
             (init : A)
             (str : String) (len : nat)
  : A
    := nat_rect
         (fun _ => A)
         init
         (fun len' acc
          => match get (length str - S len') str with
               | Some ch => f ch (get (length str - len') str) acc
               | None => init
             end)
         len.

  Definition fold_lookahead {Char} {HSLM} {HSL : @StringLike Char HSLM} {A}
             (f : Char -> option Char -> A -> A)
             (init : A)
             (str : String)
  : A
    := fold_lookahead' f init str (length str).

  Notation to_string str := (fold (@List.cons _) (@List.nil _) str).

  Definition str_le `{@StringLike Char HSLM} (s1 s2 : String)
    := length s1 < length s2 \/ s1 =s s2.
  Infix "≤s" := str_le (at level 70, right associativity).

  Notation substring n m str := (take m (drop n str)).

  Class StringLikeProperties (Char : Type) `{StringLike Char} :=
    {
      singleton_unique : forall s ch ch', s ~= [ ch ] -> s ~= [ ch' ] -> ch = ch';
      singleton_exists : forall s, length s = 1 -> exists ch, s ~= [ ch ];
      char_at_matches_correct : forall s n P ch, get n s = Some ch -> (char_at_matches n s P = P ch);
      get_0 : forall s ch, take 1 s ~= [ ch ] <-> get 0 s = Some ch;
      get_S : forall n s, get (S n) s = get n (drop 1 s);
      unsafe_get_correct : forall n s ch, get n s = Some ch -> unsafe_get n s = ch;
      length_singleton : forall s ch, s ~= [ ch ] -> length s = 1;
      bool_eq_char : forall s s' ch, s ~= [ ch ] -> s' ~= [ ch ] -> s =s s';
      is_char_Proper :> Proper (beq ==> eq ==> eq) is_char;
      length_Proper :> Proper (beq ==> eq) length;
      take_Proper :> Proper (eq ==> beq ==> beq) take;
      drop_Proper :> Proper (eq ==> beq ==> beq) drop;
      bool_eq_Equivalence :> Equivalence beq;
      bool_eq_empty : forall str str', length str = 0 -> length str' = 0 -> str =s str';
      take_short_length : forall str n, n <= length str -> length (take n str) = n;
      take_long : forall str n, length str <= n -> take n str =s str;
      take_take : forall str n m, take n (take m str) =s take (min n m) str;
      drop_length : forall str n, length (drop n str) = length str - n;
      drop_0 : forall str, drop 0 str =s str;
      drop_drop : forall str n m, drop n (drop m str) =s drop (n + m) str;
      drop_take : forall str n m, drop n (take m str) =s take (m - n) (drop n str);
      take_drop : forall str n m, take n (drop m str) =s drop m (take (n + m) str);
      bool_eq_from_get : forall str str', (forall n, get n str = get n str') -> str =s str';
      strings_nontrivial : forall n, exists str, length str = n
    }.

  Class StringIsoProperties {Char} {HSLM} {HSL : @StringLike Char HSLM} {HSI : @StringIso Char HSLM} :=
    {
      get_of_string : forall n str, get n (of_string str) = List.nth_error str n
    }.

  Class StringEqProperties {Char} {HSLM} {HSL : @StringLike Char HSLM} :=
    {
      bool_eq_bl : forall s s', s =s s' -> s = s';
      bool_eq_lb : forall s s', s = s' -> s =s s'
    }.

  Global Existing Instance Equivalence_Reflexive.
  Global Existing Instance Equivalence_Symmetric.
  Global Existing Instance Equivalence_Transitive.

  Arguments StringLikeProperties Char {_ _}.
  Arguments StringIsoProperties Char {_ _ _}.
  Arguments StringEqProperties Char {_ _}.
End StringLike.

(* Speed up some setoid lemmas *)
Global Instance: forall T H,
    @Params (forall Char
                    (HSLM : StringLikeMin Char) (HSL : StringLike Char),
                String -> T Char)
            H
            3.
