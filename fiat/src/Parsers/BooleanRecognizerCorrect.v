Require Import Coq.Classes.Morphisms.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.GenericBaseTypes Fiat.Parsers.GenericCorrectnessBaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid.
Require Import Fiat.Parsers.GenericRecognizerCorrect.
Require Import Fiat.Parsers.BooleanRecognizer.

Local Coercion is_true : bool >-> Sortclass.

Section convenience.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}
          {cdata : @boolean_parser_completeness_dataT' Char _ _ G _}
          {rdata : @parser_removal_dataT' _ G _}
          (gvalid : grammar_valid G).

  Local Instance gencdata_default_proper {A}
    : Proper (beq ==> eq ==> eq ==> eq ==> Basics.impl) (fun _ (_ : A) (x y : bool) => y = x).
  Proof.
    repeat intro; repeat subst; reflexivity.
  Qed.

  Local Existing Instance boolean_gendata.
  Global Program Instance boolean_gencdata : generic_parser_correctness_dataT
    := { parse_nt_is_correct str nt exp act := act = exp;
         parse_item_is_correct str it exp act := act = exp;
         parse_production_is_correct str p exp act := act = exp;
         parse_productions_is_correct str p exp act := act = exp }.

  Definition parse_item_sound
    : forall str it, parse_item str it -> parse_of_item G str it
    := parse_item_sound.

  Definition parse_item_complete
    : forall str it, parse_of_item G str it -> parse_item str it
    := parse_item_complete.

  Definition parse_nonterminal_sound
    : forall str nt, parse_nonterminal str nt -> parse_of_item G str (NonTerminal nt)
    := parse_nonterminal_sound.

  Definition parse_nonterminal_complete
    : forall str nt, parse_of_item G str (NonTerminal nt) -> parse_nonterminal str nt
    := parse_nonterminal_complete.

  Definition parse_of_nonterminal_complete
    : forall str nt,
      List.In nt (Valid_nonterminals G)
      -> parse_of G str (Lookup G nt)
      -> parse_nonterminal str nt
    := parse_of_nonterminal_complete.
End convenience.
