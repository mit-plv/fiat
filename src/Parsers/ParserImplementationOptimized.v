(** * Implementation of simply-typed interface of the parser *)
Require Export Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.BaseTypes Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.BooleanRecognizerPreOptimized.
Require Import Fiat.Parsers.BooleanRecognizerOptimized.
Require Import Fiat.Parsers.BooleanRecognizerEquality.
Require Import Fiat.Parsers.ParserImplementation.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Transfer.
Require Import Fiat.Parsers.ContextFreeGrammar.TransferProperties.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.

Set Implicit Arguments.

Local Open Scope list_scope.

Definition transfer_parser_keep_string {Char G} {HSLM HSL}
           (old : @Parser Char G HSLM HSL)
           (new_has_parse : @String Char HSLM -> _)
           (new_parse : @String Char HSLM -> _)
           (H_has_parse : forall s, new_has_parse s = has_parse old s)
           (H_parse : forall s, new_parse s = parse old s)
: @Parser Char G HSLM HSL.
Proof.
  refine {| has_parse := new_has_parse;
            parse := new_parse |};
  abstract (
      intros;
      rewrite ?H_has_parse, ?H_parse in *;
        first [ apply (has_parse_sound old); assumption
              | eapply (has_parse_complete old); eassumption
              | eapply (parse_correct old); eassumption ]
    ).
Defined.

Arguments transfer_parser_keep_string {_ _ _ _} _ _ _ _ _.

Definition transfer_parser {Char G} {HSLM1 HSLM2 HSL1 HSL2}
           (old : @Parser Char G HSLM1 HSL1)
           (make_string : @String Char HSLM2 -> @String Char HSLM1)
           (new_has_parse : @String Char HSLM2 -> _)
           (new_parse : @String Char HSLM2 -> _)
           (H_has_parse : forall s, new_has_parse s = has_parse old (make_string s))
           (H_parse : forall s, new_parse s = parse old (make_string s))
           (R : @String Char HSLM1 -> @String Char HSLM2 -> Prop)
           (R_make : forall str, R (make_string str) str)
           (R_respectful : transfer_respectful R)
           (R_flip_respectful : transfer_respectful (Basics.flip R))
: @Parser Char G HSLM2 HSL2.
Proof.
  refine {| has_parse := new_has_parse;
            parse := new_parse |}.
  { abstract (
        intros str H';
        rewrite H_has_parse in H';
        refine (@transfer_parse_of_item Char _ _ _ _ G R R_respectful (make_string str) str (NonTerminal G) (R_make str) _);
        apply (has_parse_sound old); assumption
      ). }
  { abstract (
        intros str p;
        rewrite H_has_parse;
        pose (@transfer_parse_of_item Char _ _ _ _ G (Basics.flip R) R_flip_respectful str (make_string str) (NonTerminal G) (R_make str) p) as p';
        apply (has_parse_complete old p'); subst p';
        exact (transfer_forall_parse_of_item _ H')
      ). }
  { abstract (
        intros str;
        rewrite H_has_parse, H_parse, parse_correct; reflexivity
      ). }
Defined.

Arguments transfer_parser {_ _ _ _ _ _} _ _ _ _ _ _ _ _ _ _.

Section implementation.
  Context {G : pregrammar Ascii.ascii}.
  Context (Hvalid : is_true (grammar_rvalid G)).
  Context (splitter : Splitter G).
  Context {string_like_min_lite : StringLikeMin Ascii.ascii}
          {string_like_lite : @StringLike Ascii.ascii string_like_min_lite}
          split_string_for_production_lite
          (HSLPr : @StringLikeProj Ascii.ascii splitter string_like_min_lite (parser_data splitter) (parser_split_data splitter) (@optsplitdata _ _ _ split_string_for_production_lite)).
  Context (stringlike_stringlikemin : StringLikeMin Ascii.ascii)
          (stringlike_stringlike : @StringLike Ascii.ascii stringlike_stringlikemin)
          (make_string : @String _ stringlike_stringlikemin -> @String _ splitter)
          (R : @String _ splitter -> @String _ stringlike_stringlikemin -> Prop)
          (R_make : forall str, R (make_string str) str)
          (R_respectful : transfer_respectful R)
          (R_flip_respectful : transfer_respectful (Basics.flip R)).

  Local Instance pdata : @boolean_parser_dataT Ascii.ascii string_like_min_lite
    := { split_data := split_string_for_production_lite }.

  Local Instance pdataopt : @boolean_parser_dataT Ascii.ascii string_like_min_lite
    := { split_data := @optsplitdata _ _ _ split_string_for_production_lite }.

 Local Instance pdata' : @boolean_parser_dataT Ascii.ascii splitter
    := parser_data splitter.

  Local Instance splitdata_correct' : @boolean_parser_completeness_dataT' _ _ _ G pdata'
    := parser_completeness_data splitter.

  Local Arguments Compare_dec.leb !_ !_.

  Definition parser : Parser G stringlike_stringlike.
  Proof.
    pose proof Hvalid as Hrvalid.
    apply grammar_rvalid_correct in Hvalid.
    let impl0 := constr:(fun str => parse_nonterminal_opt (G := G) (splitdata := pdata) Hrvalid (@proj _ _ _ _ _ _ HSLPr (make_string str)) (Start_symbol G)) in
    let impl := (eval simpl in (fun str => proj1_sig (impl0 str))) in
    let implH := constr:(fun str => proj2_sig (impl0 str)) in
    let impl' := (eval cbv beta iota zeta delta [RDPList.rdp_list_remove_nonterminal RDPList.rdp_list_initial_nonterminals_data RDPList.rdp_list_nonterminals_listT RDPList.rdp_list_is_valid_nonterminal RDPList.rdp_list_ntl_wf RDPList.rdp_list_nonterminals_listT_R RDPList.rdp_list_of_nonterminal RDPList.rdp_list_to_nonterminal Carriers.default_nonterminal_carrierT Carriers.some_invalid_nonterminal Carriers.default_to_production Carriers.default_to_nonterminal] in impl) in
    let impl := (eval simpl in impl') in
    let s_impl0 := constr:(fun str => option_map (SimpleParseNonTerminal (Start_symbol G))
                                                 (SimpleRecognizer.parse_nonterminal (make_string str) (Start_symbol G))) in
    let s_impl := (eval simpl in s_impl0) in
    let s_impl := (eval cbv [SimpleRecognizer.parse_nonterminal SimpleRecognizer.parse_nonterminal' nonterminals_length initial_nonterminals_data predata pdata RDPList.rdp_list_predata RDPList.rdp_list_initial_nonterminals_data of_nonterminal RDPList.rdp_list_of_nonterminal SimpleRecognizer.parse_nonterminal_or_abort nonterminals_listT RDPList.rdp_list_nonterminals_listT default_nonterminal_carrierT nonterminal_carrierT SimpleRecognizer.parse_nonterminal_step SimpleRecognizer.parse_productions' nonterminal_to_production is_valid_nonterminal RDPList.rdp_list_is_valid_nonterminal remove_nonterminal RDPList.rdp_list_remove_nonterminal RDPList.rdp_list_nonterminal_to_production RDPList.rdp_list_to_nonterminal default_to_nonterminal SimpleRecognizer.option_simple_parse_of_orb SimpleRecognizer.parse_production' SimpleRecognizer.parse_production'_for SimpleRecognizer.option_orb SimpleRecognizer.option_SimpleParseProductionCons SimpleRecognizer.parse_item'] in s_impl) in
    refine (transfer_parser
              (HSL1 := splitter) (HSL2 := stringlike_stringlike)
              (parser splitter) make_string
              impl
              s_impl
              (fun str => eq_trans
                            (implH str)
                            (@parse_nonterminal_proj _ splitter string_like_min_lite G pdata' _ _ _ HSLPr _ _))
              (fun str => eq_refl : s_impl0 str = _ (SimpleRecognizer.parse_nonterminal (make_string str) G))
              R R_make _ _).
  Defined.

End implementation.
