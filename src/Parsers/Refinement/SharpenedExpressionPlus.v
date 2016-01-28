(** Sharpened ADT for an expression grammar with + *)
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Grammars.ExpressionNumPlus.
Require Import Fiat.Parsers.Refinement.DisjointRules.
Require Import Fiat.Parsers.ExtrOcamlParsers. (* for simpl rules for [find_first_char_such_that] *)

Set Implicit Arguments.

Section IndexedImpl.

  Lemma ComputationalSplitter'
  : FullySharpened (string_spec plus_expr_grammar string_stringlike).
  Proof.
    start sharpening ADT.
    start honing parser using indexed representation.

    hone method "splits".
    {
      Time simplify parser splitter.
      (*Start Profiling.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      Show Profile. *)
(*
total time:     23.641s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─simplify_parser_splitter' -------------   0.0% 100.0%      38    5.016s
─solve_prod_beq ------------------------   2.9%  64.1%      15    4.797s
─rewrite !if_aggregate2 by solve_prod_be   2.2%  51.2%       6    4.828s
─destruct H ----------------------------  18.1%  18.1%     650    0.016s
─rewrite !if_aggregate3 by solve_prod_be   0.1%  15.2%       2    3.594s
─simplify with monad laws --------------   0.0%  13.4%      37    0.313s
─simplify_with_applied_monad_laws ------   0.3%  13.4%      37    0.313s
─apply (proj1 (EqNat.beq_nat_true_iff _   11.2%  11.2%     549    0.016s
─apply (proj1 (Bool.andb_true_iff _ _))    7.1%   7.1%     350    0.016s
─subst ---------------------------------   5.2%   5.2%     879    0.016s
─discriminate --------------------------   4.9%   4.9%     249    0.016s
─unguard -------------------------------   0.0%   4.2%      38    0.172s
─rewrite ?(unguard [0]) ----------------   4.0%   4.2%      38    0.172s
─destruct x ----------------------------   3.6%   3.6%      75    0.016s
─apply Bool.orb_true_iff in H ----------   3.2%   3.2%      81    0.016s
─rewrite <- !Bool.andb_orb_distrib_r ---   3.2%   3.2%      36    0.203s
─rewrite <- !Bool.andb_orb_distrib_l ---   2.9%   2.9%      31    0.156s
─apply Bool.andb_false_iff in H --------   2.5%   2.5%      60    0.016s
─eapply refine_under_bind_helper -------   2.5%   2.5%     266    0.031s
─eapply refine_under_bind_helper_2 -----   2.4%   2.4%     266    0.016s
─eapply refine_under_bind_helper_1 -----   2.4%   2.4%     266    0.016s
─rewrite <- !Bool.orb_assoc ------------   2.3%   2.3%      23    0.141s
─apply Bool.orb_false_iff in H ---------   2.2%   2.2%      66    0.016s
─apply refine_bind_unit_helper ---------   2.1%   2.1%     270    0.016s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─simplify_parser_splitter' -------------   0.0% 100.0%      38    5.016s
 ├─rewrite !if_aggregate2 by solve_prod_   2.2%  51.2%       6    4.828s
 │└solve_prod_beq ----------------------   2.5%  49.0%      14    4.797s
 │ ├─destruct H ------------------------  14.8%  14.8%     510    0.016s
 │ ├─apply (proj1 (EqNat.beq_nat_true_if   8.7%   8.7%     399    0.016s
 │ ├─apply (proj1 (Bool.andb_true_iff _    5.2%   5.2%     255    0.016s
 │ ├─discriminate ----------------------   3.8%   3.8%     204    0.016s
 │ ├─subst -----------------------------   2.8%   2.8%     622    0.016s
 │ ├─apply Bool.orb_true_iff in H ------   2.5%   2.5%      64    0.016s
 │ ├─apply Bool.andb_false_iff in H ----   2.4%   2.4%      57    0.016s
 │ ├─apply Bool.orb_false_iff in H -----   2.2%   2.2%      65    0.016s
 │ └─destruct x ------------------------   2.0%   2.0%      40    0.016s
 ├─rewrite !if_aggregate3 by solve_prod_   0.1%  15.2%       2    3.594s
 │└solve_prod_beq ----------------------   0.4%  15.1%       1    3.578s
 │ ├─destruct H ------------------------   3.3%   3.3%     140    0.016s
 │ ├─apply (proj1 (EqNat.beq_nat_true_if   2.5%   2.5%     150    0.016s
 │ └─subst -----------------------------   2.4%   2.4%     257    0.016s
 ├─simplify with monad laws ------------   0.0%  13.4%      37    0.313s
 │└simplify_with_applied_monad_laws ----   0.3%  13.4%      37    0.313s
 │ ├─eapply refine_under_bind_helper ---   2.5%   2.5%     266    0.031s
 │ ├─eapply refine_under_bind_helper_2 -   2.4%   2.4%     266    0.016s
 │ ├─eapply refine_under_bind_helper_1 -   2.4%   2.4%     266    0.016s
 │ └─apply refine_bind_unit_helper -----   2.1%   2.1%     270    0.016s
 ├─unguard -----------------------------   0.0%   4.2%      38    0.172s
 │└rewrite ?(unguard [0]) --------------   4.0%   4.2%      38    0.172s
 ├─rewrite <- !Bool.andb_orb_distrib_r -   3.2%   3.2%      36    0.203s
 ├─rewrite <- !Bool.andb_orb_distrib_l -   2.9%   2.9%      31    0.156s
 └─rewrite <- !Bool.orb_assoc ----------   2.3%   2.3%      23    0.141s *)
      let lem := constr:(@refine_disjoint_search_for_idx _ _ _ _ _) in
      setoid_rewrite lem; [ | reflexivity.. ].
      simpl.
      finish honing parser method.
    }
    finish_Sharpening_SplitterADT.
  Defined.

  Lemma ComputationalSplitter
    : FullySharpened (string_spec plus_expr_grammar string_stringlike).
  Proof.
    make_simplified_splitter ComputationalSplitter'.
  Defined.

End IndexedImpl.

Require Import Fiat.Parsers.ParserFromParserADT.
Require Import Fiat.Parsers.ExtrOcamlParsers.
Import Fiat.Parsers.ExtrOcamlParsers.HideProofs.

Definition paren_expr_parser (str : String.string) : bool.
Proof.
  Time make_parser ComputationalSplitter. (* 15 s *)
Defined.

Print paren_expr_parser.

Recursive Extraction paren_expr_parser.
