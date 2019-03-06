Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.SimpleRecognizer.
Require Import Fiat.Parsers.SimpleRecognizerCorrect.
Require Import Fiat.Parsers.RecognizerPreOptimized.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.GenericRecognizerOptimized.
Require Import Fiat.Parsers.GenericRecognizerOptimizedTactics.
Require Import Fiat.Common.

Section recursive_descent_parser.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char}
          {G : pregrammar Char}.
  Context (Hvalid : is_true (grammar_rvalid G)).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Context {splitdata : @split_dataT Char _ _}.

  Let data : boolean_parser_dataT :=
    {| split_data := splitdata |}.
  Let optdata : boolean_parser_dataT :=
    {| split_data := optsplitdata |}.
  Local Existing Instance data.

  Let rdata' : @parser_removal_dataT' _ G predata := rdp_list_rdata'.
  Local Existing Instance rdata'.

  Local Arguments minus !_ !_.
  Local Arguments min !_ !_.

  Definition parse_nonterminal_opt'0
             (str : String)
             (nt : String.string)
  : { b : _ | b = parse_nonterminal (data := optdata) str nt }.
  Proof.
    exact (@parse_nonterminal_opt _ _ G Hvalid _ simple_gendata str nt).
  Defined.

  Definition parse_nonterminal_opt'1
             (str : String)
             (nt : String.string)
  : { b : _ | b = parse_nonterminal (data := optdata) str nt }.
  Proof.
    let c := constr:(parse_nonterminal_opt'0 str nt) in
    let h := head c in
    let p := (eval cbv [proj1_sig h] in (proj1_sig c)) in
    sigL_transitivity p; [ | abstract exact (proj2_sig c) ].

    let T := match goal with |- @sig ?A _ => A end in
    evar (b' : T).
    sigL_transitivity b'; subst b'.
    Focus 2.
    { let gendata := match goal with |- context[@parse_nonterminal_opt _ _ _ _ _ ?gendata] => head gendata end in
      cbv [parse_nonterminal_opt gendata].
      cbv [GenericBaseTypes.parse_nt_T GenericBaseTypes.parse_item_T GenericBaseTypes.parse_production_T GenericBaseTypes.parse_productions_T GenericBaseTypes.ret_Terminal_false GenericBaseTypes.ret_Terminal_true GenericBaseTypes.ret_NonTerminal_false GenericBaseTypes.ret_NonTerminal_true GenericBaseTypes.ret_production_cons GenericBaseTypes.ret_orb_production GenericBaseTypes.ret_orb_production_base GenericBaseTypes.ret_production_nil_true GenericBaseTypes.ret_production_nil_false GenericBaseTypes.ret_orb_productions GenericBaseTypes.ret_orb_productions_base GenericBaseTypes.ret_nt GenericBaseTypes.ret_nt_invalid].
      reflexivity. }
    Unfocus.

    eexists; reflexivity.
  Defined.

  Definition parse_nonterminal_opt
             (str : String)
             (nt : String.string)
  : { b : _ | b = parse_nonterminal (data := optdata) str nt }.
  Proof.
    let c := constr:(parse_nonterminal_opt'1 str nt) in
    let h := head c in
    let impl := (eval cbv [h proj1_sig] in (proj1_sig c)) in
    (exists impl);
      abstract (exact (proj2_sig c)).
  Defined.

  Lemma parse_nonterminal_opt_eq
        {HSLP : StringLikeProperties Char}
        {splitdata_correct : @boolean_parser_completeness_dataT' _ _ _ G data}
        (str : String)
        (nt : String.string)
    : @GenericCorrectnessBaseTypes.parse_nt_is_correct _ _ _ _ _ simple_gencdata2 str (of_nonterminal nt) (GenericRecognizerMin.parse_nonterminal str nt) (proj1_sig (parse_nonterminal_opt str nt)).
  Proof.
    let p := match goal with |- context[proj1_sig ?p] => p end in
    rewrite (proj2_sig p).
    refine (proj2 (@parse_nonterminal_optdata_eq _ _ _ G splitdata simple_gendata simple_gencdata2 _ _ str nt _ ) _).
    unfold parse_nonterminal.
    exact (GenericRecognizerMin.parse_nonterminal_correct (gcdata := simple_gencdata2) str nt).
  Qed.
End recursive_descent_parser.
