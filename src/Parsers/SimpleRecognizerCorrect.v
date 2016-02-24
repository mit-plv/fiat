(** * Proof that SimpleRecognizer outputs correct parse trees *)
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.SimpleRecognizer Fiat.Parsers.SimpleRecognizerExt.
Require Import Fiat.Parsers.ContextFreeGrammar.SimpleCorrectness.

Section correctness.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}
          (*{cdata : @boolean_parser_completeness_dataT' Char _ _ G _}*)
          {rdata : @parser_removal_dataT' _ G _}
          (*(gvalid : grammar_valid G)*).
  (** XXX TODO: remove the above commented out variables if they end up not being necessary. *)

  (** To prove the following, look in SimpleRecognizer, SimpleBooleanRecognizerEquality, SimpleRecognizerExt, BooleanRecognizerCorrect, in that order *)
  Lemma simple_recognizer_correct (str : String) (nt : String.string) t
    : parse_nonterminal str nt = Some t
      -> simple_parse_of_correct G str (Lookup G nt) t.
  Proof.
  Abort.
End correctness.
