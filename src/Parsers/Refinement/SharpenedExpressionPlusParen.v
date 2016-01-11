(** Sharpened ADT for an expression grammar with + and () *)
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Grammars.ExpressionNumPlusParen.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.MakeBinOpTable.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.BinOpRules.
Require Import Fiat.Parsers.ExtrOcamlParsers. (* for simpl rules for [find_first_char_such_that] *)

Set Implicit Arguments.

Section IndexedImpl.

  Lemma ComputationalSplitter'
  : FullySharpened (string_spec plus_expr_grammar string_stringlike).
  Proof.
    start sharpening ADT.
    Time start honing parser using indexed representation.

    Time hone method "splits".
    {
      (*Start Profiling.*)
      Time simplify parser splitter.
      (*Show Profile.*)
      (*

total time:      3.578s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─simplify parser splitter --------------   0.0% 100.0%       1    3.578s
─simplify_parser_splitter' -------------   0.4% 100.0%      13    0.406s
─simplify ------------------------------   0.0% 100.0%       1    3.578s
─simplify with monad laws --------------   0.0%  37.1%      12    0.281s
─simplify_with_applied_monad_laws ------   1.7%  37.1%      12    0.281s
─unguard -------------------------------   0.0%  10.9%      13    0.188s
─rewrite ?(unguard [0]) ----------------  10.5%  10.9%      13    0.188s
─rewrite !if_aggregate3 by solve_prod_be   3.9%   7.9%       4    0.172s
─eapply refine_under_bind_helper -------   7.9%   7.9%      91    0.016s
─rewrite !if_aggregate2 by solve_prod_be   4.8%   7.0%       6    0.109s
─eapply refine_under_bind_helper_1 -----   6.6%   6.6%      91    0.031s
─rewrite <- !Bool.andb_orb_distrib_r ---   6.6%   6.6%      11    0.078s
─eapply refine_under_bind_helper_2 -----   6.6%   6.6%      91    0.031s
─solve_prod_beq ------------------------   0.9%   6.1%       8    0.063s
─rewrite !if_aggregate -----------------   5.2%   5.2%       8    0.109s
─rewrite <- !Bool.andb_orb_distrib_l ---   5.2%   5.2%       9    0.063s
─apply refine_bind_bind_helper ---------   4.8%   4.8%      93    0.016s
─apply refine_unit_bind_helper ---------   4.8%   4.8%      93    0.016s
─apply refine_bind_unit_helper ---------   3.9%   3.9%      95    0.016s
─rewrite !beq_0_1_leb ------------------   3.5%   3.5%       7    0.031s
─rewrite <- !BoolFacts.andb_orb_distrib_   3.5%   3.5%       8    0.031s
─rewrite <- !Bool.andb_assoc -----------   3.1%   3.1%       8    0.031s
─rewrite <- !Bool.orb_andb_distrib_l ---   2.6%   2.6%       8    0.016s
─rewrite <- !Bool.orb_assoc ------------   2.6%   2.6%       8    0.031s
─rewrite <- !Bool.orb_andb_distrib_r ---   2.6%   2.6%       8    0.016s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─simplify parser splitter --------------   0.0% 100.0%       1    3.578s
└simplify ------------------------------   0.0% 100.0%       1    3.578s
└simplify_parser_splitter' -------------   0.4% 100.0%      13    0.406s
 ├─simplify with monad laws ------------   0.0%  37.1%      12    0.281s
 │└simplify_with_applied_monad_laws ----   1.7%  37.1%      12    0.281s
 │ ├─eapply refine_under_bind_helper ---   7.9%   7.9%      91    0.016s
 │ ├─eapply refine_under_bind_helper_1 -   6.6%   6.6%      91    0.031s
 │ ├─eapply refine_under_bind_helper_2 -   6.6%   6.6%      91    0.031s
 │ ├─apply refine_unit_bind_helper -----   4.8%   4.8%      93    0.016s
 │ ├─apply refine_bind_bind_helper -----   4.8%   4.8%      93    0.016s
 │ └─apply refine_bind_unit_helper -----   3.9%   3.9%      95    0.016s
 ├─unguard -----------------------------   0.0%  10.9%      13    0.188s
 │└rewrite ?(unguard [0]) --------------  10.5%  10.9%      13    0.188s
 ├─rewrite !if_aggregate3 by solve_prod_   3.9%   7.9%       4    0.172s
 │└solve_prod_beq ----------------------   0.0%   3.9%       4    0.063s
 ├─rewrite !if_aggregate2 by solve_prod_   4.8%   7.0%       6    0.109s
 │└solve_prod_beq ----------------------   0.9%   2.2%       4    0.047s
 ├─rewrite <- !Bool.andb_orb_distrib_r -   6.6%   6.6%      11    0.078s
 ├─rewrite !if_aggregate ---------------   5.2%   5.2%       8    0.109s
 ├─rewrite <- !Bool.andb_orb_distrib_l -   5.2%   5.2%       9    0.063s
 ├─rewrite !beq_0_1_leb ----------------   3.5%   3.5%       7    0.031s
 ├─rewrite <- !BoolFacts.andb_orb_distri   3.5%   3.5%       8    0.031s
 ├─rewrite <- !Bool.andb_assoc ---------   3.1%   3.1%       8    0.031s
 ├─rewrite <- !Bool.orb_andb_distrib_l -   2.6%   2.6%       8    0.016s
 ├─rewrite <- !Bool.orb_andb_distrib_r -   2.6%   2.6%       8    0.016s
 └─rewrite <- !Bool.orb_assoc ----------   2.6%   2.6%       8    0.031s
 *)
      (*Start Profiling.*)
      Time refine_binop_table.
      (*Show Profile.*)
      (*
total time:      6.094s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─setoid_rewrite_refine_binop_table_idx -   1.0% 100.0%       1    6.094s
─refine_binop_table --------------------   0.0% 100.0%       1    6.094s
─lazy beta iota zeta delta in c0 -------  92.1%  92.1%       1    5.609s
─setoid_rewrite H ----------------------   4.1%   5.4%       1    0.328s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─refine_binop_table --------------------   0.0% 100.0%       1    6.094s
└setoid_rewrite_refine_binop_table_idx -   1.0% 100.0%       1    6.094s
 ├─lazy beta iota zeta delta in c0 -----  92.1%  92.1%       1    5.609s
 └─setoid_rewrite H --------------------   4.1%   5.4%       1    0.328s
 *)
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
  Time make_parser ComputationalSplitter. (* 20 s *)
(*  Show Proof.

  pose (has_parse (parser ComputationalSplitter) str) as p.
  Timeout 5 cbv beta iota zeta delta [has_parse parser ParserImplementationOptimized.parser transfer_parser projT1 projT2] in p.
  Timeout 5 simpl map in p.
  Timeout 5 simpl hd in p.
  Timeout 5 simpl Datatypes.length in p.
  Timeout 5 simpl @fst in p.
  Timeout 5 simpl @snd in p.
  Timeout 5 unfold fold_right, fold_left, map in p.
  Timeout 5 simpl @fst in p.
  Timeout 5 simpl @snd in p.
  Timeout 5 unfold map in p.
  Timeout 5 unfold BooleanRecognizer.parse_production' in p.
  About split_string_for_production.
Definition Let_In {A P} (x : A) (f : forall x : A, P x) := let a := x in f a.
Strategy expand [Let_In].
  Timeout 50 let pbody := (eval unfold p in p) in
  lazymatch pbody with
  | appcontext [@split_string_for_production ?Char ?HSL ?pdata ?it (Terminal "+"%char::?ps) (?str, _)]
    => idtac;
      let c1 := constr:(@split_string_for_production Char HSL pdata it (Terminal "+"%char::ps)) in
      let T := type of str in
      let c2 := constr:(fun sz : T * _ => c1 (str, snd sz)) in
      set (splitsv := c2);
      lazymatch eval pattern c1 in pbody with
        | ?pbody' _ => idtac; change pbody with (Let_In splitsv pbody') in p
  end
end.
  Timeout 5 cbv beta in p.
  Timeout 5 simpl in splitsv.
  About list_of_next_bin_ops_opt.
  Timeout 30 let splitsv' := (eval unfold splitsv in splitsv) in
            let c1 := match splitsv' with appcontext[@list_of_next_bin_ops_opt ?a ?b] => constr:(@list_of_next_bin_ops_opt a b) end in
            lazymatch eval pattern c1 in splitsv' with
              | ?splitsv'' _ => idtac;
                               change splitsv with (Let_In c1 splitsv'') in p
  end.
  Timeout 20 cbv beta in p.
  let pbody := (eval unfold p in p) in exact pbody.*)
Defined.
(*Opaque Let_In.
Definition paren_expr_parser' (str : String.string) : bool
  := Eval hnf in paren_expr_parser str.
Transparent Let_In.*)

Print paren_expr_parser.

Recursive Extraction paren_expr_parser.
