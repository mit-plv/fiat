Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BooleanRecognizerMin Fiat.Parsers.BooleanRecognizer Fiat.Parsers.BooleanRecognizerExt.
Require Import Fiat.Parsers.MinimalParse.
Require Import Fiat.Parsers.BaseTypes Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.Splitters.RDPList Fiat.Parsers.Splitters.BruteForce.
Require Import Fiat.Parsers.MinimalParseOfParse.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties Fiat.Parsers.WellFoundedParse.
Require Import Fiat.Common Fiat.Common.Wf.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid Fiat.Parsers.ContextFreeGrammar.ValidProperties.
Local Open Scope string_like_scope.

Section convenience.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}
          {cdata : @boolean_parser_completeness_dataT' Char _ G _}
          {rdata : @parser_removal_dataT' _ G _}
          (gvalid : grammar_valid G).

  Local Ltac invert_bool_of_sum :=
    progress
      repeat match goal with
               | [ H : is_true false |- _ ] => solve [ inversion H ]
               | [ |- is_true true ] => reflexivity
               | [ H : context[bool_of_sum _] |- _ ] => revert H
               | [ |- context[bool_of_sum ?e] ] => case e; simpl
               | _ => progress intros
               | [ |- is_true false ] => exfalso
               | [ H : _ -> False |- False ] => apply H; clear H
             end.

  Definition parse_item_sound
             (str : String) (it : item Char)
  : parse_item (G := G) str it
    -> parse_of_item G str it.
  Proof.
    intro pit.
    erewrite <- parse_item_eq in pit by assumption; invert_bool_of_sum.
    apply parse_of_item__of__minimal_parse_of_item in m.
    apply m.
  Defined.

  Definition parse_item_complete
             (str : String) (it : item Char)
             (p : parse_of_item G str it)
  : parse_item (G := G) str it.
  Proof.
    erewrite <- parse_item_eq by assumption; invert_bool_of_sum.
    apply minimal_parse_of_item__of__parse_of_item; assumption.
  Qed.

  Definition parse_nonterminal_sound
             (str : String) (nt : String.string)
  : parse_nonterminal (G := G) str nt
    -> parse_of_item G str (NonTerminal nt).
  Proof.
    intro pit.
    erewrite <- parse_nonterminal_eq in pit by assumption; invert_bool_of_sum.
    apply parse_of_item_nonterminal__of__minimal_parse_of_nonterminal in m.
    apply m.
  Defined.

  Definition parse_nonterminal_complete
             (str : String) (nt : String.string)
             (p : parse_of_item G str (NonTerminal nt))
  : parse_nonterminal (G := G) str nt.
  Proof.
    erewrite <- parse_nonterminal_eq by assumption; invert_bool_of_sum.
    apply minimal_parse_of_nonterminal__of__parse_of_item_nonterminal.
    assumption.
  Qed.

  Definition parse_of_nonterminal_complete
             (str : String) (nt : String.string)
             (H : List.In nt (Valid_nonterminals G))
             (p : parse_of G str (Lookup G nt))
  : parse_nonterminal (G := G) str nt.
  Proof.
    apply (parse_nonterminal_complete (ParseNonTerminal _ H p)).
  Qed.
End convenience.
