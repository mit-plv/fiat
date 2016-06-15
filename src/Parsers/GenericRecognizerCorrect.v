Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.GenericRecognizerMin.
Require Import Fiat.Parsers.BaseTypes Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.GenericBaseTypes Fiat.Parsers.GenericCorrectnessBaseTypes.
Require Import Fiat.Parsers.MinimalParseOfParse.
Require Import Fiat.Common.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid.
Require Import Fiat.Parsers.GenericRecognizer.
Local Open Scope string_like_scope.

Section convenience.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}
          {cdata : @boolean_parser_completeness_dataT' Char _ _ G _}
          {rdata : @parser_removal_dataT' _ G _}
          {gendata : generic_parser_dataT Char}
          {gencdata : generic_parser_correctness_dataT}
          (gvalid : grammar_valid G).

  Local Ltac t :=
    match goal with
    | [ H : ?R true ?v, H' : ?R (bool_of_sum ?x) ?v |- _ ]
      => destruct x; simpl in *
    | [ H : ?R (bool_of_sum ?x) ?v |- ?R true ?v ]
      => destruct x; simpl in *
    end;
    try solve [ assumption
              | exfalso;
                solve [ eapply parse_nt_is_correct_disjoint; eassumption
                      | eapply parse_item_is_correct_disjoint; eassumption
                      | eapply parse_production_is_correct_disjoint; eassumption
                      | eapply parse_productions_is_correct_disjoint; eassumption
                      | auto with nocore ] ].

  Definition parse_item_sound
             (str : String) (it : item Char)
  : parse_item_is_correct str it true (parse_item str it)
    -> parse_of_item G str it.
  Proof.
    intro pit.
    pose proof (parse_item_correct str it).
    t.
    eapply parse_of_item__of__minimal_parse_of_item; eassumption.
  Defined.

  Definition parse_item_complete
             (str : String) (it : item Char)
             (p : parse_of_item G str it)
  : parse_item_is_correct str it true (parse_item str it).
  Proof.
    apply minimal_parse_of_item__of__parse_of_item in p.
    pose proof (parse_item_correct str it).
    t.
  Qed.

  Definition parse_nonterminal_sound
             (str : String) (nt : String.string)
  : parse_nt_is_correct str (of_nonterminal nt) true (parse_nonterminal str nt)
    -> parse_of_item G str (NonTerminal nt).
  Proof.
    intro pit.
    pose proof (parse_nonterminal_correct str nt).
    t.
    eapply parse_of_item_nonterminal__of__minimal_parse_of_nonterminal; eassumption.
  Defined.

  Definition parse_nonterminal_complete
             (str : String) (nt : String.string)
             (p : parse_of_item G str (NonTerminal nt))
  : parse_nt_is_correct str (of_nonterminal nt) true (parse_nonterminal str nt).
  Proof.
    apply minimal_parse_of_nonterminal__of__parse_of_item_nonterminal in p.
    pose proof (parse_nonterminal_correct str nt).
    t.
  Qed.

  Definition parse_of_nonterminal_complete
             (str : String) (nt : String.string)
             (H : List.In nt (Valid_nonterminals G))
             (p : parse_of G str (Lookup G nt))
  : parse_nt_is_correct str (of_nonterminal nt) true (parse_nonterminal str nt).
  Proof.
    apply (parse_nonterminal_complete (ParseNonTerminal _ H p)).
  Qed.
End convenience.
