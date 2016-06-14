(** Reference implementation of a splitter and parser based on that splitter *)
Require Import Fiat.ADTNotation.BuildADT Fiat.ADTNotation.BuildADTSig.
Require Import Fiat.ADT.ComputationalADT.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.
Local Open Scope string_scope.

Section ReferenceImpl.
  Section GenericSig.
    Context (Char : Type) (String : Type) (production_carrierT : Type).

    (** Representation of a [String] that can be split *)
    Definition string_rep :=
      ADTsignature {
        Constructor "new" : String -> rep,
        (** Initialize, with a given [string] to be parsed or split. *)

        Method "to_string" : rep -> rep * String,
        (** Return the underlying string; hack to get around not having [eq : rep x rep -> bool] *)

        Method "char_at_matches" : rep * (nat : Type) * (Char -> bool) -> rep * bool,
        (* Return [char_at_matches str n P] is equal to [P ch] if [str] has a character at position [n] which is equal to [ch]; return value is arbitrary otherwise. *)

        Method "get" : rep * nat -> rep * Char,
        (* Returns [ch] if the [n]th character of this string is some [ch], and returns an arbitrary character otherwise. *)

        Method "length" : rep -> rep * nat,
        (** Return the length of this string. *)

        Method "take" : rep * (nat : Type) -> rep,
        (** Return the first [n] characters, for the given [n : nat]. *)

        Method "drop" : rep * (nat : Type) -> rep,
        (** Return everything but the first [n] characters, for the given [n : nat]. *)

        Method "splits" : rep * production_carrierT * (nat : Type) * (nat : Type) -> rep * (list nat)
        (** Return a list of locations to split this string at for this production rule. *)
      }.
  End GenericSig.

  Context (G : pregrammar' Ascii.ascii) (HSLM : StringLikeMin Ascii.ascii) (HSL : StringLike Ascii.ascii).
  Local Open Scope ADTParsing_scope.

  (** Reference implementation of a [String] that can be split *)
  Definition string_spec' : ADT (string_rep Ascii.ascii String default_production_carrierT) := Def ADT  {
    rep := String,

    Def Constructor1 "new"(s : String) : rep :=
      ret s,,

    Def Method0 "to_string" (s : rep) : rep * String :=
      ret (s, s),

    Def Method2 "char_at_matches"(s : rep) (n : nat) (P : Ascii.ascii -> bool) : rep * bool  :=
      b <- { b : bool | forall ch', get n s = Some ch' -> P ch' = b };
      ret (s, b),

    Def Method1 "get"(s : rep) (n : nat) : rep * Ascii.ascii  :=
      ch <- { ch : Ascii.ascii | forall ch', get n s = Some ch' -> ch = ch' };
      ret (s, ch),

    Def Method0 "length"(s : rep) : rep * nat :=
      ret (s, length s),

    Def Method1 "take"(s : rep) (n : nat) : rep :=
      ret (take n s),

    Def Method1 "drop"(s : rep) (n : nat) : rep :=
      ret (drop n s),

    Def Method3 "splits"(s : rep) (idx : default_production_carrierT) (offset : nat) (len : nat) : rep * list nat :=
      ls <- { ls : list nat | split_list_is_complete_idx G s offset len idx ls };
      ret (s, ls)
  }.
End ReferenceImpl.

Class ceq {A} (x y : A) := ceq' : x = y.
Global Instance ceq_refl {A} (x : A) : ceq x x := eq_refl.

Definition string_spec
           (G : grammar Ascii.ascii)
           {G' : pregrammar' Ascii.ascii}
           {HGeq : ceq G G'}
           (HSLM : StringLikeMin Ascii.ascii)
           (HSL : StringLike Ascii.ascii)
  := string_spec' G' HSL.

Arguments string_spec G {G' HGeq} [HSLM] HSL.
