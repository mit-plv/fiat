(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.BaseTypes Parsers.ContextFreeGrammar.
Require Import Parsers.MinimalParse.
Require Import Common.

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

  Definition split_list_completeT `{data : boolean_parser_dataT}
             {str0 valid}
             (str : StringWithSplitState String split_stateT) (pf : str ≤s str0)
             (split_list : list (StringWithSplitState String split_stateT * StringWithSplitState String split_stateT))
             (it : item CharType) (its : production CharType)
    := ({ s1s2 : String * String
                 & (fst s1s2 ++ snd s1s2 =s str)
                   * (minimal_parse_of_item _ G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid (fst s1s2) it)
                   * (minimal_parse_of_production _ G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid (snd s1s2) its) }%type)
       -> ({ s1s2 : StringWithSplitState String split_stateT * StringWithSplitState String split_stateT
                    & (In s1s2 split_list)
                      * (minimal_parse_of_item _ G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid (fst s1s2) it)
                      * (minimal_parse_of_production _ G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid (snd s1s2) its) }%type).

  Class boolean_parser_completeness_dataT' `{data : boolean_parser_dataT} :=
    { remove_nonterminal_1
      : forall ls ps ps',
          is_valid_nonterminal (remove_nonterminal ls ps) ps' = true
          -> is_valid_nonterminal ls ps' = true;
      remove_nonterminal_2
      : forall ls ps ps',
          is_valid_nonterminal (remove_nonterminal ls ps) ps' = false
          <-> is_valid_nonterminal ls ps' = false \/ ps = ps';
      split_string_for_production_complete
      : forall str0 valid str pf nt,
          is_valid_nonterminal initial_nonterminals_data nt
          -> ForallT
               (Forall_tails
                  (fun prod
                   => match prod return Type with
                        | nil => True
                        | it::its
                          => @split_list_completeT _ str0 valid str pf (split_string_for_production it its str) it its
                      end))
               (Lookup G nt) }.

  Class boolean_parser_correctness_dataT :=
    { data :> boolean_parser_dataT;
      cdata' :> boolean_parser_completeness_dataT' }.
End general.
