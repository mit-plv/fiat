(** * Brute-force boolean recognizer *)
Require Import Coq.Classes.RelationClasses.
Require Import ADTSynthesis.Parsers.StringLike.String.
Require Import ADTSynthesis.Parsers.BooleanRecognizer.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.Splitters.RDPList ADTSynthesis.Parsers.Splitters.BruteForce.

Set Implicit Arguments.

Section example_parse_string_grammar.
  Context (G : grammar Ascii.ascii).

  Definition brute_force_parse_nonterminal
  : @String Ascii.ascii _
    -> String.string
    -> bool
    := let data := @brute_force_data Ascii.ascii _ G in parse_nonterminal (G := G).

  Definition brute_force_parse_production
             (str : @String Ascii.ascii _)
  : production Ascii.ascii
    -> bool
    := let data := @brute_force_data Ascii.ascii _ G in parse_production (fun str' _ nt => brute_force_parse_nonterminal str' nt) (reflexivity str).

  Definition brute_force_parse_productions
             (str : @String Ascii.ascii _)
  : productions Ascii.ascii
    -> bool
    := let data := @brute_force_data Ascii.ascii _ G in parse_productions (fun str' _ nt => brute_force_parse_nonterminal str' nt) (reflexivity str).

  Definition brute_force_parse_item
             (str : @String Ascii.ascii _)
  : item Ascii.ascii
    -> bool
    := let data := @brute_force_data Ascii.ascii _ G in parse_item (fun nt => brute_force_parse_nonterminal str nt) str.

  Definition brute_force_parse
  : String.string -> bool
    := fun str => brute_force_parse_nonterminal str G.
End example_parse_string_grammar.
