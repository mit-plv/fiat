(** * Reference implementation of a splitter and parser based on that splitter *)
Require Import ADTNotation.BuildADT ADTNotation.BuildADTSig.
Require Import ADT.ComputationalADT.
Require Import ADTSynthesis.Common.List.Operations.
Require Import ADTRefinement.GeneralRefinements.
Require Import Parsers.ParserInterface.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.

Section ReferenceImpl.
  Context {CharType} {String : string_like CharType} (G : grammar CharType).

  (** Representation of a [String] that can be split *)
  Definition string_rep : ADTSig :=
    ADTsignature {
      Constructor "new" : String -> rep,
      (** Initialize, with a given [String] to be parsed or split. *)

      Method "take" : rep x nat -> rep x unit,
      (** Return the first [n] characters, for the given [n : nat]. *)

      Method "drop" : rep x nat -> rep x unit,
      (** Return everything but the first [n] characters, for the given [n : nat]. *)

      Method "splits" : rep x item CharType * production CharType -> rep x list nat
    }.

  (** Reference implementation of a [String] that can be split *)
  Definition string_spec : ADT string_rep := ADTRep String {
    Def Constructor "new"(s : String) : rep :=
      ret s,

    Def Method "take"(s : rep, n : nat) : unit :=
      ret (fst (SplitAt n s), tt),

    Def Method "drop"(s : rep, n : nat) : unit :=
      ret (snd (SplitAt n s), tt),

    Def Method "splits"(s : rep, p : item CharType * production CharType) : list nat :=
      ls <- { ls : list nat | split_list_is_complete String G s (fst p) (snd p) ls };
      ret (s, ls)
  }.

  Section parser.
    Context (splitter : Sharpened string_spec).

    Local Obligation Tactic := admit.

    Program Definition adt_based_splitter : Splitter String G
      := {| split_rep := _ (* rep of splitter *);
            split_take n st := _ (* call "take"(st, n) on splitter *);
            split_drop n st := _ (* call "drop"(st, n) on splitter *);
            splits_for st it its := _ (* call "splits"(st, (it, its)) on splitter *);
            split_invariant str st := _ (* rep inv between String and split_rep *);
            take_respectful str st n H := _ (* proof that "take" preserves the rep inv w.r.t. its spec *);
            drop_respectful str st n H := _ (* proof that "drop" preserves the rep inv w.r.t. its spec *);
            splits_for_complete str st it its H := _ (* proof that "splits" obeys its spec, given that the rep inv holds on the input, by H *) |}.
    (* Next Obligation.
    Proof.
    ...
    Qed. *)
End parser.
