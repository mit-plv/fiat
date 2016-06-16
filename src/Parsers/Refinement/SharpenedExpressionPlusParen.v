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

total time:      0.125s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─simplify parser splitter --------------   0.0% 100.0%       1    0.125s
─simplify_parser_splitter' -------------   0.0% 100.0%       3    0.078s
─simplify ------------------------------   0.0% 100.0%       1    0.125s
─simplify with monad laws --------------   0.0%  50.0%       2    0.063s
─simplify_with_applied_monad_laws ------   0.0%  50.0%       2    0.063s
─eapply refine_under_bind_helper -------  25.0%  25.0%       5    0.016s
─eapply refine_under_bind_helper_2 -----  25.0%  25.0%       5    0.016s
─eapply lem ----------------------------  12.5%  12.5%       1    0.016s
─simpl opt.nat_of_ascii ----------------  12.5%  12.5%       2    0.016s
─apply (simplify_monad_laws_first_step (  12.5%  12.5%       1    0.016s
─clear lem -----------------------------  12.5%  12.5%       2    0.016s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─simplify parser splitter --------------   0.0% 100.0%       1    0.125s
└simplify ------------------------------   0.0% 100.0%       1    0.125s
└simplify_parser_splitter' -------------   0.0% 100.0%       3    0.078s
 ├─simplify with monad laws ------------   0.0%  50.0%       2    0.063s
 │└simplify_with_applied_monad_laws ----   0.0%  50.0%       2    0.063s
 │ ├─eapply refine_under_bind_helper ---  25.0%  25.0%       5    0.016s
 │ └─eapply refine_under_bind_helper_2 -  25.0%  25.0%       5    0.016s
 ├─eapply lem --------------------------  12.5%  12.5%       1    0.016s
 ├─clear lem ---------------------------  12.5%  12.5%       2    0.016s
 ├─simpl opt.nat_of_ascii --------------  12.5%  12.5%       2    0.016s
 └─apply (simplify_monad_laws_first_step  12.5%  12.5%       1    0.016s
 *)
      { (*Start Profiling.*)
        Time refine_binop_table.
        (*Show Profile.*)
      (*
total time:      0.548s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─refine_binop_table --------------------   0.7% 100.0%       1    0.548s
─setoid_rewrite_refine_binop_table_idx -  62.8%  99.3%       1    0.544s
─replace_with_at_by --------------------   0.0%  18.2%       1    0.100s
─replace_with_vm_compute_in ------------   0.0%  18.2%       1    0.100s
─replace c with c' in H by (clear; vm_ca   0.0%  18.2%       1    0.100s
─set_tac -------------------------------   0.0%   9.5%       1    0.052s
─set (x' := x) in H --------------------   9.5%   9.5%       1    0.052s
─induction H ---------------------------   6.6%   6.6%       1    0.036s
─setoid_rewrite H ----------------------   4.4%   5.1%       1    0.028s
─pose proof lem as H -------------------   4.4%   4.4%       1    0.024s
─assert T0 as H0 by (clear; lazy beta io   0.7%   3.6%       1    0.020s
─clear ---------------------------------   2.9%   2.9%       2    0.016s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─refine_binop_table --------------------   0.7% 100.0%       1    0.548s
└setoid_rewrite_refine_binop_table_idx -  62.8%  99.3%       1    0.544s
 ├─replace_with_vm_compute_in ----------   0.0%  18.2%       1    0.100s
 │└replace c with c' in H by (clear; vm_   0.0%  18.2%       1    0.100s
 │└replace_with_at_by ------------------   0.0%  18.2%       1    0.100s
 │ ├─set_tac ---------------------------   0.0%   9.5%       1    0.052s
 │ │└set (x' := x) in H ----------------   9.5%   9.5%       1    0.052s
 │ └─induction H -----------------------   6.6%   6.6%       1    0.036s
 ├─setoid_rewrite H --------------------   4.4%   5.1%       1    0.028s
 ├─pose proof lem as H -----------------   4.4%   4.4%       1    0.024s
 └─assert T0 as H0 by (clear; lazy beta    0.7%   3.6%       1    0.020s
  └clear -------------------------------   2.9%   2.9%       1    0.016s
 *)
        reflexivity. }
      finish honing parser method.
    }

    finish_Sharpening_SplitterADT.
  Time Defined.

  Lemma ComputationalSplitter
  : FullySharpened (string_spec plus_expr_grammar string_stringlike).
  Proof.
    Time make_simplified_splitter ComputationalSplitter'.
  Time Defined.

End IndexedImpl.

Require Import Fiat.Parsers.ParserFromParserADT.
Require Import Fiat.Parsers.ExtrOcamlParsers.
Import Fiat.Parsers.ExtrOcamlParsers.HideProofs.

Definition paren_expr_parser (str : String.string) : bool.
Proof.
  Time make_parser ComputationalSplitter. (* 0.18 s *)
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
