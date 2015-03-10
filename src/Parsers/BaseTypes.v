(** * Definition of the common part of the interface of the CFG parser *)
Require Import Coq.Lists.List Coq.Init.Wf Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar.

Set Implicit Arguments.

Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.

Inductive any_grammar CharType :=
| include_item (_ : item CharType)
| include_production (_ : production CharType)
| include_productions (_ : productions CharType)
| include_nonterminal (_ : string).
Global Coercion include_item : item >-> any_grammar.
Global Coercion include_production : production >-> any_grammar.
Global Coercion include_productions : productions >-> any_grammar.

Section recursive_descent_parser.
  Context {CharType : Type}
          {String : string_like CharType}
          {G : grammar CharType}.

  Class parser_computational_predataT :=
    { nonterminals_listT : Type;
      initial_nonterminals_data : nonterminals_listT;
      is_valid_nonterminal : nonterminals_listT -> string -> bool;
      remove_nonterminal : nonterminals_listT -> string -> nonterminals_listT;
      nonterminals_listT_R : nonterminals_listT -> nonterminals_listT -> Prop;
      remove_nonterminal_dec : forall ls nonterminal,
                             is_valid_nonterminal ls nonterminal = true
                             -> nonterminals_listT_R (remove_nonterminal ls nonterminal) ls;
      ntl_wf : well_founded nonterminals_listT_R }.

  Class parser_computational_types_dataT :=
    { predata :> parser_computational_predataT;
      split_stateT : String -> nonterminals_listT -> any_grammar CharType -> String -> Type }.

  Class parser_computational_dataT' `{parser_computational_types_dataT} :=
    { split_string_for_production
      : forall (str0 : String) (valid : nonterminals_listT) (it : item CharType) (its : production CharType) (str : StringWithSplitState String (split_stateT str0 valid (it::its : production CharType))),
          list (StringWithSplitState String (split_stateT str0 valid it)
                * StringWithSplitState String (split_stateT str0 valid its));
      split_string_for_production_correct
      : forall str0 valid it its str,
          let P f := List.Forall f (@split_string_for_production str0 valid it its str) in
          P (fun s1s2 => (fst s1s2 ++ snd s1s2 =s str) = true) }.

  Class parser_computational_dataT :=
    { premethods :> parser_computational_types_dataT;
      methods' :> parser_computational_dataT' }.

  Class MonadT := Build_MonadT : Type -> Type.
  Global Instance idM : MonadT | 10000 := fun x => x.
  Global Strategy -1000 [idM].

  Class parser_computational_prestrdataT `{parser_computational_dataT} `{M : MonadT} :=
    { prelower_nonterminal_state
      : forall {str0 valid nonterminal s},
          split_stateT str0 valid (NonTerminal _ nonterminal) s -> M (split_stateT str0 valid (include_nonterminal _ nonterminal) s);

      prelower_string_head
      : forall {str0 valid}
               {prod : production CharType}
               {prods : productions CharType}
               {s},
          split_stateT str0 valid (prod::prods : productions CharType) s -> M (split_stateT str0 valid prod s);
      prelower_string_tail
      : forall {str0 valid}
               {prod : production CharType}
               {prods : productions CharType}
               {s},
          split_stateT str0 valid (prod::prods : productions CharType) s -> M (split_stateT str0 valid prods s);

      prelift_lookup_nonterminal_state_lt
      : forall {str0 valid nonterminal s} (pf : Length s < Length str0),
          split_stateT str0 valid (include_nonterminal _ nonterminal) s -> M (split_stateT s initial_nonterminals_data (Lookup G nonterminal) s);

      prelift_lookup_nonterminal_state_eq
      : forall {str0 valid nonterminal s}
               (pf : s = str0 :> String),
          split_stateT str0 valid (include_nonterminal _ nonterminal) s -> M (split_stateT str0 (remove_nonterminal valid nonterminal) (Lookup G nonterminal) s) }.

  Definition parser_computational_strdataT `{parser_computational_dataT} : Type
    := parser_computational_prestrdataT.
  Existing Class parser_computational_strdataT.

  Definition lower_nonterminal_state `{methods : parser_computational_dataT, strdata : @parser_computational_strdataT methods}
  : forall {str0 valid nonterminal s},
      split_stateT _ _ _ _ -> split_stateT _ _ _ _
    := @prelower_nonterminal_state methods (fun x => x) strdata.
  Definition lower_string_head `{methods : parser_computational_dataT, strdata : @parser_computational_strdataT methods}
  : forall {str0 valid prod prods s},
      split_stateT _ _ _ _ -> split_stateT _ _ _ _
    := @prelower_string_head methods (fun x => x) strdata.
  Definition lower_string_tail `{methods : parser_computational_dataT, strdata : @parser_computational_strdataT methods}
  : forall {str0 valid prod prods s},
      split_stateT _ _ _ _ -> split_stateT _ _ _ _
    := @prelower_string_tail methods (fun x => x) strdata.
  Definition lift_lookup_nonterminal_state_lt `{methods : parser_computational_dataT, strdata : @parser_computational_strdataT methods}
  : forall {str0 valid nonterminal s} pf,
      split_stateT _ _ _ _ -> split_stateT _ _ _ _
    := @prelift_lookup_nonterminal_state_lt methods (fun x => x) strdata.
  Definition lift_lookup_nonterminal_state_eq `{methods : parser_computational_dataT, strdata : @parser_computational_strdataT methods}
  : forall {str0 valid nonterminal s} pf,
      split_stateT _ _ _ _ -> split_stateT _ _ _ _
    := @prelift_lookup_nonterminal_state_eq methods (fun x => x) strdata.
End recursive_descent_parser.

Existing Class parser_computational_strdataT.
