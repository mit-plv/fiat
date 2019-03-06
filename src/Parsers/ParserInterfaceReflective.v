(** * Simply-typed reflective interface of the parser *)
Require Import Fiat.Parsers.BooleanRecognizerOptimizedReflective.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.Reflective.Syntax.
Require Import Fiat.Parsers.Reflective.ParserSyntax.
Require Import Fiat.Parsers.Reflective.ParserPartialUnfold.

Record ParserReflective (G : pregrammar Ascii.ascii) :=
  {
    rhas_parse : polyhas_parse_term cbool;

    rhas_parse_correct : rhas_parse = polypnormalize (parse_nonterminal_reified G (Start_symbol G))
  }.

Definition default_ParserReflective G : ParserReflective G
  := {| rhas_parse_correct := eq_refl |}.

Ltac make_ParserReflective G :=
  let p := constr:(default_ParserReflective G) in
  eval vm_compute in p.
