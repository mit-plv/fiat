(** * Definition of the common part of the interface of the CFG parser *)
Require Import Coq.Lists.List Coq.Arith.Wf_nat Coq.Init.Wf Coq.Strings.String.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.

Set Implicit Arguments.

Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.

Section recursive_descent_parser.
  Context {Char} {HSL : StringLike Char} {G : grammar Char}.

  Class parser_computational_predataT :=
    { nonterminals_listT : Type;
      initial_nonterminals_data : nonterminals_listT;
      nonterminals_length : nonterminals_listT -> nat;
      is_valid_nonterminal : nonterminals_listT -> String.string -> bool;
      remove_nonterminal : nonterminals_listT -> String.string -> nonterminals_listT }.

  Class parser_removal_dataT' `{predata : parser_computational_predataT} :=
    { nonterminals_listT_R : nonterminals_listT -> nonterminals_listT -> Prop
      := ltof _ nonterminals_length;
      remove_nonterminal_dec : forall ls nonterminal,
                                 is_valid_nonterminal ls nonterminal
                                 -> nonterminals_listT_R (remove_nonterminal ls nonterminal) ls;
      remove_nonterminal_noninc : forall ls nonterminal,
                                    ~nonterminals_listT_R ls (remove_nonterminal ls nonterminal);
      ntl_wf : well_founded nonterminals_listT_R
      := well_founded_ltof _ _;
      remove_nonterminal_1
      : forall ls ps ps',
          is_valid_nonterminal (remove_nonterminal ls ps) ps'
          -> is_valid_nonterminal ls ps';
      remove_nonterminal_2
      : forall ls ps ps',
          is_valid_nonterminal (remove_nonterminal ls ps) ps' = false
          <-> is_valid_nonterminal ls ps' = false \/ ps = ps' }.

  Class boolean_parser_dataT :=
    { predata :> parser_computational_predataT;
      split_string_for_production
      : item Char -> production Char -> String -> list nat }.

  Global Coercion predata : boolean_parser_dataT >-> parser_computational_predataT.
End recursive_descent_parser.
