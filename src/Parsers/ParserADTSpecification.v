(** Reference implementation of a splitter and parser based on that splitter *)
Require Import Fiat.ADTNotation.BuildADT Fiat.ADTNotation.BuildADTSig.
Require Import Fiat.ADT.ComputationalADT.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Common.Equality.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.
Local Open Scope string_scope.

Section ReferenceImpl.
  Section GenericSig.
    Context (Char : Type) (String : Type).

    (** Representation of a [String] that can be split *)
    Definition string_rep :=
      ADTsignature {
        Constructor "new" : String -> rep,
        (** Initialize, with a given [string] to be parsed or split. *)

        Method "to_string" : rep -> rep * String,
        (** Return the underlying string; hack to get around not having [eq : rep x rep -> bool] *)

        Method "is_char" : rep * Char -> rep * bool,
        (* Return [true] if this string represents a singleton character equal to the given one; otherwise return [false]. *)

        Method "get" : rep * nat -> rep * Char,
        (* Returns [ch] if the [n]th character of this string is some [ch], and returns an arbitrary character otherwise. *)

        Method "length" : rep -> rep * nat,
        (** Return the length of this string. *)

        Method "take" : rep * (nat : Type) -> rep,
        (** Return the first [n] characters, for the given [n : nat]. *)

        Method "drop" : rep * (nat : Type) -> rep,
        (** Return everything but the first [n] characters, for the given [n : nat]. *)

        Method "splits" : rep * (item Char) * (production Char) -> rep * (list nat)
        (** Return a list of locations to split this string at for this production rule. *)
      }.
  End GenericSig.

  Context (G : grammar Ascii.ascii) (HSL : StringLike Ascii.ascii).
  Local Open Scope ADTParsing_scope.
  (** Reference implementation of a [String] that can be split *)
  Definition string_spec : ADT (string_rep Ascii.ascii String) := ADTRep String {
    Def Constructor1 "new"(s : String) : rep :=
      ret s,

    Def Method0 "to_string" (s : rep) : rep * String :=
      ret (s, s),

    Def Method1 "is_char"(s : rep) (x : Ascii.ascii) : rep * bool  :=
      ret (s, is_char s x),

    Def Method1 "get"(s : rep) (n : nat) : rep * Ascii.ascii  :=
      ch <- { ch : Ascii.ascii | forall ch', get n s = Some ch' -> ch = ch' };
      ret (s, ch),

    Def Method0 "length"(s : rep) : rep * nat :=
      ret (s, length s),

    Def Method1 "take"(s : rep) (n : nat) : rep :=
      ret (take n s),

    Def Method1 "drop"(s : rep) (n : nat) : rep :=
      ret (drop n s),

    Def Method2 "splits"(s : rep) (i : item Ascii.ascii) (p : production Ascii.ascii) : rep * list nat :=
      ls <- { ls : list nat | split_list_is_complete G s i p ls };
      ret (s, ls)
  }.
End ReferenceImpl.
