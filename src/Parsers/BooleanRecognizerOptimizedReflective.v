Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BooleanRecognizerOptimized.
Require Import Fiat.Parsers.Reflective.Syntax Fiat.Parsers.Reflective.ParserSyntax.
Require Import Fiat.Parsers.Reflective.Semantics Fiat.Parsers.Reflective.ParserSemantics.
Require Import Fiat.Parsers.Reflective.SemanticsOptimized Fiat.Parsers.Reflective.ParserSemanticsOptimized.
Require Import Fiat.Parsers.Reflective.Morphisms.
Require Import Fiat.Parsers.Reflective.ParserReify.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Common.

Section recursive_descent_parser.
  Context {HSLM : StringLikeMin Ascii.ascii} {HSL : StringLike Ascii.ascii}
          {G : pregrammar Ascii.ascii}.
  Context (Hvalid : is_true (grammar_rvalid G)).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Context {splitdata : @split_dataT Ascii.ascii _ _}.

  Definition parse_nonterminal_prereified0 (str : String) (nt : String.string) : polyhas_parse_term cbool.
  Proof.
    let p := constr:(parse_nonterminal_preopt Hvalid str nt) in
    let h := head p in
    let p := (eval cbv [proj1_sig h] in (proj1_sig p)) in
    do_reify_has_parse p ltac:(fun r => exact r).
  Defined.
End recursive_descent_parser.

Definition parse_nonterminal_reified (G : pregrammar Ascii.ascii) (nt : String.string) : polyhas_parse_term cbool.
Proof.
  let p := constr:(fun HSLM => @parse_nonterminal_prereified0 HSLM G) in
  let p := (eval cbv [parse_nonterminal_prereified0] in p) in
  let p := match p with fun A B C => ?f => f end in
  let p := (eval cbv [rdp_list_of_nonterminal Carriers.default_of_nonterminal grammar_of_pregrammar pregrammar'_of_pregrammar pregrammar_nonterminals pregrammar_productions] in (p nt)) in
  exact p.
Defined.

Section correctness.
  Context {HSLM : StringLikeMin Ascii.ascii} {HSL : StringLike Ascii.ascii} {HSLP : StringLikeProperties Ascii.ascii}
          {G : pregrammar Ascii.ascii}.
  Context (Hvalid : is_true (grammar_rvalid G)).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Context {splitdata : @split_dataT Ascii.ascii _ _}.

  Let data : boolean_parser_dataT :=
    {| split_data := splitdata |}.

  Context {splitdata_correct : @CorrectnessBaseTypes.boolean_parser_completeness_dataT' _ _ _ G data}.

  Context (str : String) (nt : String.string).

  Definition rinterp_parse pnt
    := (opt.interp_has_parse_term
          (T := cbool)
          (@is_valid_nonterminal _ _)
          (length str)
          (fun n => @Reflective.char_at_matches_interp _ _ (pregrammar_idata G) n str)
          (fun n => split_string_for_production n str)
          pnt).

  Lemma parse_nonterminal_reified_opt_interp_precorrect
    : rinterp_parse (parse_nonterminal_reified G nt _)
      = proj1_sig (parse_nonterminal_preopt Hvalid str nt).
  Proof.
    clear splitdata_correct HSLP.
    cbv [rinterp_parse parse_nonterminal_reified].
    change @opt.interp_has_parse_term with @interp_has_parse_term.
    cbv [interp_has_parse_term].
    cbv [proj1_sig parse_nonterminal_preopt].
    match goal with
    | [ |- ?f ?x = ?g ?y ]
      => replace x with y
    end.
    Focus 2.
    { unfold rdp_list_of_nonterminal, Carriers.default_of_nonterminal.
      cbv [pregrammar_productions pregrammar'_of_pregrammar].
      rewrite !List.map_length, !List.map_map; simpl.
      reflexivity. }
    Unfocus.
    unfold interp_Term; simpl; fold @interp_Term;
      rewrite <- !interp_Term_syntactify_rproductions;
      reflexivity.
  Qed.

  Lemma parse_nonterminal_reified_opt_interp_correct
    : rinterp_parse (parse_nonterminal_reified G nt _)
      = BooleanRecognizer.parse_nonterminal (data := data) str nt.
  Proof.
    rewrite parse_nonterminal_reified_opt_interp_precorrect.
    apply parse_nonterminal_preopt_eq; assumption.
  Qed.
End correctness.
