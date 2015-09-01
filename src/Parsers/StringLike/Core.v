(** * Definition of the string-like type *)
Require Import Coq.Relations.Relation_Definitions (* for [relation] *).
Require Import Coq.Classes.Morphisms (* for [==>] / [respectful] *).

Local Coercion is_true : bool >-> Sortclass.

Set Implicit Arguments.
Generalizable All Variables.

(** Something is string-like if it has a type of characters, and can
    be split. *)

Reserved Notation "[ x ]".

Module Export StringLike.
  Class StringLike {Char : Type} :=
    {
      String :> Type;
      is_char : String -> Char -> bool;
      length : String -> nat;
      take : nat -> String -> String;
      drop : nat -> String -> String;
      get : nat -> String -> option Char;
      bool_eq : String -> String -> bool;
      beq : relation String := fun x y => bool_eq x y
    }.

  Arguments StringLike : clear implicits.
  Bind Scope string_like_scope with String.
  Delimit Scope string_like_scope with string_like.
  Infix "=s" := (@beq _ _) (at level 70, no associativity) : type_scope.
  Infix "=s" := (@bool_eq _ _) (at level 70, no associativity) : string_like_scope.
  Notation "s ~= [ ch ]" := (is_char s ch) (at level 70, no associativity) : string_like_scope.
  Local Open Scope string_like_scope.
  Local Open Scope type_scope.

  Hint Extern 0 (@StringLike (@String ?string ?H)) => exact H : typeclass_instances.

  Definition fold' {Char} {HSL : StringLike Char} {A}
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

  Definition fold {Char} {HSL : StringLike Char} {A}
             (f : Char -> A -> A)
             (init : A)
             (str : String)
  : A
    := fold' f init str (length str).

  Definition str_le `{StringLike Char} (s1 s2 : String)
    := length s1 < length s2 \/ s1 =s s2.
  Infix "≤s" := str_le (at level 70, right associativity).

  Class StringLikeProperties (Char : Type) `{StringLike Char} :=
    {
      singleton_unique : forall s ch ch', s ~= [ ch ] -> s ~= [ ch' ] -> ch = ch';
      singleton_exists : forall s, length s = 1 -> exists ch, s ~= [ ch ];
      get_0 : forall s ch, take 1 s ~= [ ch ] <-> get 0 s = Some ch;
      get_S : forall n s, get (S n) s = get n (drop 1 s);
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
      take_drop : forall str n m, take n (drop m str) =s drop m (take (n + m) str)
    }.

  Global Existing Instance Equivalence_Reflexive.
  Global Existing Instance Equivalence_Symmetric.
  Global Existing Instance Equivalence_Transitive.

  Arguments StringLikeProperties Char {_}.
End StringLike.
