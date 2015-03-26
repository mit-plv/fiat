(** * Fully instantiated specialization of the dependently typed parser to minimal parse trees, taking in parse trees, using the factored abstraction barrier *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar ADTSynthesis.Parsers.DependentlyTyped ADTSynthesis.Parsers.MinimalParse ADTSynthesis.Parsers.BaseTypes.
Require Import ADTSynthesis.Parsers.Splitters.BruteForce ADTSynthesis.Parsers.Splitters.RDPList.
Require Import ADTSynthesis.Parsers.DependentlyTypedMinimalOfParseFactored.
Require Import ADTSynthesis.Parsers.WellFoundedParse ADTSynthesis.Parsers.ContextFreeGrammarProperties.
Require Import ADTSynthesis.Common ADTSynthesis.Common.Wf ADTSynthesis.Common.Le.

Set Implicit Arguments.

Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.

Section recursive_descent_parser.
  Context (G : grammar Ascii.ascii).

  Local Instance predata : parser_computational_predataT
    := { nonterminals_listT := rdp_list_nonterminals_listT;
         initial_nonterminals_data := Valid_nonterminals G;
         is_valid_nonterminal := rdp_list_is_valid_nonterminal;
         remove_nonterminal := rdp_list_remove_nonterminal;
         nonterminals_listT_R := rdp_list_nonterminals_listT_R;
         remove_nonterminal_dec := rdp_list_remove_nonterminal_dec;
         ntl_wf := rdp_list_ntl_wf }.

  Local Instance types_data : @parser_computational_types_dataT _ string_stringlike
    := {| predata := predata;
          split_stateT str0 valid g str := True |}.

  Local Instance methods' : @parser_computational_dataT' _ string_stringlike types_data
    := { split_string_for_production str0 valid it its := make_all_single_splits;
         split_string_for_production_correct str0 valid it its str
         := Forall_impl _ _ (make_all_single_splits_correct_eq str)
}.
  Proof.
    intros; apply bool_eq_correct; assumption.
  Defined.

  Local Instance strdata : @parser_computational_prestrdataT _ string_stringlike G {| BaseTypes.methods' := methods' |} idM.
  Proof.
    constructor; simpl; intros; assumption.
  Defined.

  Local Instance orig_methods : @parser_computational_dataT _ string_stringlike
    := { methods' := methods' }.

  Lemma rdp_list_complete'
        (str0 : string_stringlike) (valid : nonterminals_listT)
        (it : item Ascii.ascii) (its : production Ascii.ascii)
        (str : StringWithSplitState string_stringlike (split_stateT str0 valid (it :: its : production _)))
        (pf : str ≤s str0)
  : BooleanBaseTypes.split_list_completeT (G := G) (valid := valid) it its str pf
                                          (split_string_for_production str0 valid it its str).
  Proof.
    simpl.
    repeat intro.
    apply (@make_all_single_splits_complete
             _ G str0 valid
             it its
             str
             pf).
    assumption.
  Defined.

  Global Instance minimal_of_parse_parser_dependent_types_extra_data
  : @parser_dependent_types_extra_dataT _ string_stringlike G
    := @minimal_of_parse_parser_dependent_types_extra_data'
         _ string_stringlike G
         predata methods' strdata
         rdp_list_rdata'
         rdp_list_complete'.

  Definition minimal_parse_nonterminal__of__parse
             (nonterminal : string)
             (s : string)
             (p : parse_of_item string_stringlike G s (NonTerminal _ nonterminal))
             (H : Forall_parse_of_item
                    (fun _ n => is_valid_nonterminal initial_nonterminals_data n = true)
                    p)
  : minimal_parse_of_nonterminal (G := G) s initial_nonterminals_data s nonterminal.
  Proof.
    eapply @minimal_parse_nonterminal__of__parse'.
    exact strdata.
    exact rdp_list_rdata'.
    exact rdp_list_complete'.
    exact H.
  Defined.
End recursive_descent_parser.
