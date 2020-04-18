(** Sharpened ADT for (ab)* *)
Require Import Fiat.Parsers.Grammars.ABStar.
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Refinement.SharpenedABStar.

Definition parser : ParserInterface.Parser ab_star_grammar String.string_stringlike.
Proof.
  let b := make_Parser (@ComputationalSplitter _ String.string_stringlike _ _) in
  exact b.
Defined.

Definition ab_star_parser_informative_opaque (str : Coq.Strings.String.string)
  : option (parse_of_item ab_star_grammar str (NonTerminal (Start_symbol ab_star_grammar))).
Proof.
  Time make_parser_informative_opaque (@ComputationalSplitter _ String.string_stringlike _ _). (* 0.82 s *)
Defined.

Goal forall b, ab_star_parser_informative_opaque "" = b.
Proof.
  intro.
  let LHS := match goal with |- ?LHS = _ => LHS end in
  let LHS := (eval hnf in LHS) in
  change (LHS = b).
Abort.

Definition ab_star_parser_informative (str : Coq.Strings.String.string)
  : option (@simple_parse_of_item Ascii.ascii).
Proof.
  Time make_parser_informative (@ComputationalSplitter _ String.string_stringlike _ _). (* 0.124 s *)
Defined.

Goal exists s, ab_star_parser_informative "" = Some s.
Proof.
  eexists.
  compute.
  reflexivity.
Qed.
