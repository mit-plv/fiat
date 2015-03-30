(** * Definition of the common part of the interface of the CFG parser *)
Require Import Coq.Lists.List Coq.Init.Wf Coq.Strings.String.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.

Set Implicit Arguments.

Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.

Inductive any_grammar string `{StringLike string} :=
| include_item (_ : item string)
| include_production (_ : production string)
| include_productions (_ : productions string)
| include_nonterminal (_ : String.string).
Global Arguments any_grammar _ {_}.
Global Coercion include_item : item >-> any_grammar.
Global Coercion include_production : production >-> any_grammar.
Global Coercion include_productions : productions >-> any_grammar.

Section recursive_descent_parser.
  Context {string} {HSL : StringLike string} {G : grammar string}.

  Class parser_computational_predataT :=
    { nonterminals_listT : Type;
      initial_nonterminals_data : nonterminals_listT;
      is_valid_nonterminal : nonterminals_listT -> String.string -> bool;
      remove_nonterminal : nonterminals_listT -> String.string -> nonterminals_listT;
      nonterminals_listT_R : nonterminals_listT -> nonterminals_listT -> Prop;
      remove_nonterminal_dec : forall ls nonterminal,
                                 is_valid_nonterminal ls nonterminal
                                 -> nonterminals_listT_R (remove_nonterminal ls nonterminal) ls;
      ntl_wf : well_founded nonterminals_listT_R }.

  Class parser_removal_dataT' `{predata : parser_computational_predataT} :=
    { remove_nonterminal_1
      : forall ls ps ps',
          is_valid_nonterminal (remove_nonterminal ls ps) ps'
          -> is_valid_nonterminal ls ps';
      remove_nonterminal_2
      : forall ls ps ps',
          is_valid_nonterminal (remove_nonterminal ls ps) ps' = false
          <-> is_valid_nonterminal ls ps' = false \/ ps = ps' }.
End recursive_descent_parser.
