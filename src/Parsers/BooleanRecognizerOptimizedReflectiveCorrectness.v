Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BooleanRecognizerOptimizedReflective.
Require Import Fiat.Parsers.Reflective.ParserSoundnessOptimized.
Require Import Fiat.Parsers.Reflective.ParserPartialUnfold.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.StringLike.Core.

Section correctness.
  Context {HSLM : StringLikeMin Ascii.ascii} {HSL : StringLike Ascii.ascii} {HSLP : StringLikeProperties Ascii.ascii}
          {G : pregrammar Ascii.ascii}.
  Context (Hvalid : is_true (grammar_rvalid G)).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Context {splitdata : @split_dataT Ascii.ascii _ _}.

  Let data : boolean_parser_dataT :=
    {| split_data := splitdata |}.

  Let optdata : boolean_parser_dataT :=
    {| split_data := RecognizerPreOptimized.optsplitdata |}.

  Context {splitdata_correct : @CorrectnessBaseTypes.boolean_parser_completeness_dataT' _ _ _ G data}.

  Context (str : String) (nt : String.string).

  Lemma parse_nonterminal_reified_opt_interp_polynormalize_precorrect
    : rinterp_parse str (polypnormalize (parse_nonterminal_reified G nt) _)
      = BooleanRecognizer.parse_nonterminal (data := optdata) str nt.
  Proof.
    cbv [rinterp_parse].
    rewrite opt.polypnormalize_correct.
    etransitivity; [ | apply (proj2_sig (BooleanRecognizerOptimized.parse_nonterminal_preopt Hvalid _ _)) ].
    etransitivity; [ | apply parse_nonterminal_reified_opt_interp_precorrect ].
    cbv [rinterp_parse].
    reflexivity.
  Qed.
End correctness.
