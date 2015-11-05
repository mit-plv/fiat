(** * Brute-force boolean recognizer *)
Require Import Coq.Classes.RelationClasses.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.BooleanRecognizer.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.Splitters.RDPList Fiat.Parsers.Splitters.BruteForce.

Set Implicit Arguments.

Section example_parse_string_grammar.
  Context (G : grammar Ascii.ascii)
          {HSL : StringLike Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}.

  Definition brute_force_parse_nonterminal
  : @String Ascii.ascii _
    -> String.string
    -> bool
    := let data := @brute_force_data Ascii.ascii _ G in parse_nonterminal (G := G).

  Definition brute_force_parse_production
             (str : @String Ascii.ascii _)
  : production Ascii.ascii
    -> bool
    := let data := @brute_force_data Ascii.ascii _ G in parse_production (G := G) str.

  Definition brute_force_parse_productions
             (str : @String Ascii.ascii _)
  : productions Ascii.ascii
    -> bool
    := let data := @brute_force_data Ascii.ascii _ G in parse_productions (G := G) str.

  Definition brute_force_parse_item
             (str : @String Ascii.ascii _)
  : item Ascii.ascii
    -> bool
    := let data := @brute_force_data Ascii.ascii _ G in parse_item (G := G) str.

  Definition brute_force_parse
  : String -> bool
    := fun str => brute_force_parse_nonterminal str G.
End example_parse_string_grammar.
