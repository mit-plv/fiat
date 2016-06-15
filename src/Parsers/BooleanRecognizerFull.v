(** * Brute-force boolean recognizer *)

Require Import Fiat.Parsers.BooleanRecognizer.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.Splitters.RDPList Fiat.Parsers.Splitters.BruteForce.

Set Implicit Arguments.

Class ceq {A} (x y : A) := ceq' : x = y.
Global Instance ceq_refl {A} (x : A) : ceq x x := eq_refl.

Section example_parse_string_grammar.
  Context (G : grammar Ascii.ascii)
          {G' : pregrammar' Ascii.ascii}
          {HGeq : ceq G G'}
          {HSLM : StringLikeMin Ascii.ascii}.

  Definition brute_force_parse_nonterminal
  : @String Ascii.ascii _
    -> String.string
    -> bool
    := let dummy := HGeq in let data := @brute_force_data Ascii.ascii _ G' in parse_nonterminal.

  Definition brute_force_parse_production
             (str : @String Ascii.ascii _)
  : BaseTypes.production_carrierT
    -> bool
    := let dummy := HGeq in let data := @brute_force_data Ascii.ascii _ G' in parse_production str.

  Definition brute_force_parse_productions
             (str : @String Ascii.ascii _)
  : list BaseTypes.production_carrierT
    -> bool
    := let dummy := HGeq in let data := @brute_force_data Ascii.ascii _ G' in parse_productions str.

  Definition brute_force_parse_item
             (str : @String Ascii.ascii _)
  : item Ascii.ascii
    -> bool
    := let dummy := HGeq in let data := @brute_force_data Ascii.ascii _ G' in parse_item str.

  Definition brute_force_parse
  : String -> bool
    := fun str => brute_force_parse_nonterminal str G.
End example_parse_string_grammar.

Arguments brute_force_parse G {G' HGeq _} _.
Arguments brute_force_parse_item G {G' HGeq _} _ _.
Arguments brute_force_parse_production G {G' HGeq _} _ _.
Arguments brute_force_parse_productions G {G' HGeq _} _ _.
Arguments brute_force_parse_nonterminal G {G' HGeq _} _ _.
