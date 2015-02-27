(** * Definition of a [comp]-based non-computational CFG parser *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.Specification Parsers.DependentlyTyped Parsers.MinimalParse.
Require Parsers.BooleanRecognizer Parsers.BooleanRecognizerCorrect.
Require Import Parsers.DependentlyTypedMinimalOfParseFactored.
Require Import Parsers.WellFoundedParse Parsers.ContextFreeGrammarProperties.
Require Import Common Common.Wf Common.Le.

Set Implicit Arguments.

Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.

Section recursive_descent_parser.
  Context (G : grammar Ascii.ascii).

  Local Instance predata : parser_computational_predataT
    := { nonterminal_names_listT := BooleanRecognizer.rdp_list_names_listT;
         initial_nonterminal_names_data := Valid_nonterminal_symbols G;
         is_valid_nonterminal_name := BooleanRecognizer.rdp_list_is_valid_name;
         remove_nonterminal_name := BooleanRecognizer.rdp_list_remove_name;
         nonterminal_names_listT_R := BooleanRecognizer.rdp_list_names_listT_R;
         remove_nonterminal_name_dec := BooleanRecognizer.rdp_list_remove_name_dec;
         ntl_wf := BooleanRecognizer.rdp_list_ntl_wf }.

  Local Instance types_data : @parser_computational_types_dataT _ string_stringlike
    := {| predata := predata;
          split_stateT str0 valid g str := True |}.

  Local Instance methods' : @parser_computational_dataT' _ string_stringlike types_data
    := { split_string_for_production str0 valid it its := BooleanRecognizer.make_all_single_splits;
         split_string_for_production_correct str0 valid it its str
         := Forall_impl _ _ (BooleanRecognizer.make_all_single_splits_correct_eq str)
}.
  Proof.
    intros; apply bool_eq_correct; assumption.
  Defined.

  Local Instance strdata : @parser_computational_prestrdataT _ string_stringlike G {| DependentlyTyped.methods' := methods' |} idM.
  Proof.
    constructor; simpl; intros; assumption.
  Defined.

  Local Instance orig_methods : @parser_computational_dataT _ string_stringlike
    := { methods' := methods' }.

  Lemma rdp_list_complete'
        (str0 : string_stringlike) (valid : nonterminal_names_listT)
        (it : item Ascii.ascii) (its : production Ascii.ascii)
        (str : StringWithSplitState string_stringlike (split_stateT str0 valid (it :: its : production _)))
        (pf : str ≤s str0)
  : DependentlyTypedMinimal.split_list_completeT G valid it its str pf
                                                 (split_string_for_production str0 valid it its str).
  Proof.
    simpl.
    repeat intro.
    apply (@BooleanRecognizerCorrect.make_all_single_splits_complete
             G BooleanRecognizer.rdp_list_names_listT
             (Valid_nonterminal_symbols G)
             BooleanRecognizer.rdp_list_is_valid_name
             BooleanRecognizer.rdp_list_remove_name
             {| string_val := str0 : string_stringlike ; state_val := I |}
             valid valid
             str
             pf (it::its : production _)).
    assumption.
  Defined.

  Global Instance minimal_of_parse_parser_dependent_types_extra_data
  : @parser_dependent_types_extra_dataT _ string_stringlike G
    := @minimal_of_parse_parser_dependent_types_extra_data'
         _ string_stringlike G
         predata methods' strdata
         BooleanRecognizer.rdp_list_remove_name_1 BooleanRecognizer.rdp_list_remove_name_2
         rdp_list_complete'.

  Definition minimal_parse_nonterminal_name__of__parse
             (nonterminal_name : string)
             (s : string)
             (p : parse_of_item string_stringlike G s (NonTerminal _ nonterminal_name))
             (H : Forall_parse_of_item
                    (fun _ n => is_valid_nonterminal_name initial_nonterminal_names_data n = true)
                    p)
  : minimal_parse_of_name string_stringlike G initial_nonterminal_names_data is_valid_nonterminal_name remove_nonterminal_name s initial_nonterminal_names_data s nonterminal_name.
  Proof.
    eapply @minimal_parse_nonterminal_name__of__parse'.
    exact strdata.
    exact BooleanRecognizer.rdp_list_remove_name_1.
    exact BooleanRecognizer.rdp_list_remove_name_2.
    exact rdp_list_complete'.
    exact H.
  Defined.
End recursive_descent_parser.
