(** Reference implementation of a splitter and parser based on that splitter *)
Require Import Coq.Strings.String.
Require Import ADTNotation.BuildADT ADTNotation.BuildADTSig.
Require Import ADT.ComputationalADT.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Common.Equality.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.
Local Open Scope string_scope.

Section ReferenceImpl.
  Section GenericSig.
    Context (Char : Type).

    (** Representation of a [String] that can be split *)
    Definition string_rep : ADTSig :=
      ADTsignature {
        Constructor "new" : String.string -> rep,
        (** Initialize, with a given [string] to be parsed or split. *)

        Method "to_string" : rep x unit -> rep x String.string,
        (** Return the underlying string; hack to get around not having [eq : rep x rep -> bool] *)

        Method "is_char" : rep x Char -> rep x bool,
        (* Return [true] if this string represents a singleton character equal to the given one; otherwise return [false]. *)

        Method "length" : rep x unit -> rep x nat,
        (** Return the length of this string. *)

        Method "take" : rep x nat -> rep x unit,
        (** Return the first [n] characters, for the given [n : nat]. *)

        Method "drop" : rep x nat -> rep x unit,
        (** Return everything but the first [n] characters, for the given [n : nat]. *)

        Method "splits" : rep x item Char * production Char -> rep x list nat
        (** Return a list of locations to split this string at for this production rule. *)
      }.
  End GenericSig.

  Context (G : grammar Ascii.ascii).

  (** Reference implementation of a [String] that can be split *)
  Definition string_spec : ADT (string_rep Ascii.ascii) := ADTRep String.string {
    Def Constructor "new"(s : String) : rep :=
      ret s,

    Def Method "to_string"(s : rep, x : unit) : String.string :=
      ret (s, s),

    Def Method "is_char"(s : rep, x : Ascii.ascii) : bool  :=
      ret (s, string_beq s (String.String x "")),

    Def Method "length"(s : rep, x : unit) : nat :=
      ret (s, String.length s),

    Def Method "take"(s : rep, n : nat) : unit :=
      ret (take n s, tt),

    Def Method "drop"(s : rep, n : nat) : unit :=
      ret (drop n s, tt),

    Def Method "splits"(s : rep, p : item Ascii.ascii * production Ascii.ascii) : list nat :=
      ls <- { ls : list nat | split_list_is_complete G s (fst p) (snd p) ls };
      ret (s, ls)
  }.
End ReferenceImpl.
