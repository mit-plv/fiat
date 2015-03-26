(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Classes.RelationClasses Coq.Strings.String.
Require Import ADTSynthesis.Parsers.BaseTypes ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.MinimalParse.
Require Import ADTSynthesis.Common.

Local Coercion is_true : bool >-> Sortclass.

Local Open Scope string_like_scope.

Section general.
  Context {CharType} {String : string_like CharType} {G : grammar CharType}.

  Class boolean_parser_dataT :=
    { predata :> parser_computational_predataT;
      split_stateT : String -> Type;
      data' :> _ := {| BaseTypes.predata := predata ; BaseTypes.split_stateT := fun _ _ _ => split_stateT |};
      split_string_for_production
      : forall it its,
          StringWithSplitState String split_stateT
          -> list (StringWithSplitState String split_stateT * StringWithSplitState String split_stateT);
      split_string_for_production_correct
      : forall it its (str : StringWithSplitState String split_stateT),
          let P f := List.Forall f (split_string_for_production it its str) in
          P (fun s1s2 =>
               (fst s1s2 ++ snd s1s2 =s str) = true);
      premethods :> parser_computational_dataT'
      := @Build_parser_computational_dataT'
           _ String data'
           (fun _ _ => split_string_for_production)
           (fun _ _ => split_string_for_production_correct) }.

  Definition split_list_completeT `{data : @parser_computational_types_dataT _ String}
             {str0 valid}
             (it : item CharType) (its : production CharType)
             (str : StringWithSplitState String (@BaseTypes.split_stateT _ _ data str0 valid (it::its : production CharType)))
             (pf : str ≤s str0)
             (split_list : list (StringWithSplitState String (@BaseTypes.split_stateT _ _ data str0 valid it)
                                 * StringWithSplitState String (@BaseTypes.split_stateT _ _ data str0 valid its)))

    := ({ s1s2 : String * String
                 & (fst s1s2 ++ snd s1s2 =s str)
                   * (minimal_parse_of_item (G := G) (predata := @BaseTypes.predata _ _ data) str0 valid (fst s1s2) it)
                   * (minimal_parse_of_production (G := G) str0 valid (snd s1s2) its) }%type)
       -> ({ s1s2 : _
                    & (In s1s2 split_list)
                      * (minimal_parse_of_item (G := G) str0 valid (fst s1s2) it)
                      * (minimal_parse_of_production (G := G) str0 valid (snd s1s2) its) }%type).

  Coercion parser_computational_types_dataT__of__boolean_parser_dataT {data : boolean_parser_dataT}
  : @parser_computational_types_dataT _ String
    := {| BaseTypes.predata := predata ; BaseTypes.split_stateT := fun _ _ _ => split_stateT |}.

  Class boolean_parser_completeness_dataT' `{data : boolean_parser_dataT} :=
    { split_string_for_production_complete
      : forall str0 valid (str : StringWithSplitState String split_stateT) (pf : str ≤s str0) nt,
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
