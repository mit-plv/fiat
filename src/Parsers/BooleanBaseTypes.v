(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Classes.RelationClasses Coq.Strings.String.
Require Import ADTSynthesis.Parsers.BaseTypes ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.MinimalParse.
Require Import ADTSynthesis.Common.

Local Open Scope string_like_scope.

Section general.
  Context {Char} {HSL : StringLike Char} {G : grammar Char}.

  Class boolean_parser_dataT :=
    { predata :> parser_computational_predataT;
      split_string_for_production
      : item Char -> production Char -> String -> list nat }.

  Global Coercion predata : boolean_parser_dataT >-> parser_computational_predataT.

  Definition split_list_completeT `{data : @parser_computational_predataT}
             {str0 valid}
             (it : item Char) (its : production Char)
             (str : String)
             (pf : str ≤s str0)
             (split_list : list nat)

    := ({ n : nat
              & (minimal_parse_of_item (G := G) (predata := data) str0 valid (take n str) it)
                * (minimal_parse_of_production (G := G) str0 valid (drop n str) its) }%type)
       -> ({ n : nat
                 & (In n split_list)
                   * (minimal_parse_of_item (G := G) str0 valid (take n str) it)
                   * (minimal_parse_of_production (G := G) str0 valid (drop n str) its) }%type).

  Class boolean_parser_completeness_dataT' `{data : boolean_parser_dataT} :=
    { split_string_for_production_complete
      : forall str0 valid str (pf : str ≤s str0) nt,
          is_valid_nonterminal initial_nonterminals_data nt
          -> ForallT
               (Forall_tails
                  (fun prod
                   => match prod return Type with
                        | nil => True
                        | it::its
                          => @split_list_completeT data str0 valid it its str pf (split_string_for_production it its str)
                      end))
               (Lookup G nt) }.

  Class boolean_parser_correctness_dataT :=
    { data :> boolean_parser_dataT;
      rdata' :> parser_removal_dataT';
      cdata' :> boolean_parser_completeness_dataT' }.
End general.
