(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Fiat.Parsers.BaseTypes Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.MinimalParse.
Require Import Fiat.Common.

Local Open Scope string_like_scope.

Section general.
  Context {Char} {HSL : StringLike Char} {G : grammar Char}.

  Definition split_list_completeT_for {data : @parser_computational_predataT}
             {len0 valid}
             (it : item Char) (its : production Char)
             (str : String)
             (pf : length str <= len0)
             (split_list : list nat)

    := ({ n : nat
              & (minimal_parse_of_item (G := G) (predata := data) len0 valid (take n str) it)
                * (minimal_parse_of_production (G := G) len0 valid (drop n str) its) }%type)
       -> ({ n : nat
                 & (In (min (length str) n) (map (min (length str)) split_list))
                   * (minimal_parse_of_item (G := G) len0 valid (take n str) it)
                   * (minimal_parse_of_production (G := G) len0 valid (drop n str) its) }%type).

  Definition split_list_completeT {data : @parser_computational_predataT}
             (splits : item Char -> production Char -> String -> list nat)
    := forall len0 valid str (pf : length str <= len0) nt,
         is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt)
         -> ForallT
              (Forall_tails
                 (fun prod
                  => match prod return Type with
                       | nil => True
                       | it::its
                         => @split_list_completeT_for data len0 valid it its str pf (splits it its str)
                     end))
              (Lookup G nt).

  Class boolean_parser_completeness_dataT' {data : boolean_parser_dataT} :=
    { split_string_for_production_complete
      : split_list_completeT split_string_for_production }.

  Class boolean_parser_correctness_dataT :=
    { data :> boolean_parser_dataT;
      rdata' :> @parser_removal_dataT' _ G _;
      cdata' :> boolean_parser_completeness_dataT' }.
End general.
