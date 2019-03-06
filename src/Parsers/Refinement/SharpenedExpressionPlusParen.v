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
    (*Start Profiling.*)
    Time splitter_start.
    (*Show Profile.*)
    (*
total time:      0.109s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─splitter_start ------------------------  14.3% 100.0%       1    0.109s
─replace_with_at_by --------------------   0.0%  42.9%       1    0.047s
─eapply lem ----------------------------  14.3%  14.3%       2    0.016s
─induction H ---------------------------  14.3%  14.3%       1    0.016s
─pose proof  (refine_opt2_fold_right_no_  14.3%  14.3%       1    0.016s
─tac -----------------------------------  14.3%  14.3%       1    0.016s
─assert (y = x') as H by (subst x'; tac)   0.0%  14.3%       1    0.016s
─set_tac -------------------------------   0.0%  14.3%       1    0.016s
─cbv beta ------------------------------  14.3%  14.3%       3    0.016s
─apply_splitter_tower_lemma ------------   0.0%  14.3%       1    0.016s
─change x with x' ----------------------  14.3%  14.3%       1    0.016s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─splitter_start ------------------------  14.3% 100.0%       1    0.109s
 ├─replace_with_at_by ------------------   0.0%  42.9%       1    0.047s
 │ ├─induction H -----------------------  14.3%  14.3%       1    0.016s
 │ ├─set_tac ---------------------------   0.0%  14.3%       1    0.016s
 │ │└change x with x' ------------------  14.3%  14.3%       1    0.016s
 │ └─assert (y = x') as H by (subst x';    0.0%  14.3%       1    0.016s
 │  └tac -------------------------------  14.3%  14.3%       1    0.016s
 ├─eapply lem --------------------------  14.3%  14.3%       1    0.016s
 ├─cbv beta ----------------------------  14.3%  14.3%       3    0.016s
 └─apply_splitter_tower_lemma ----------   0.0%  14.3%       1    0.016s
  └pose proof  (refine_opt2_fold_right_n  14.3%  14.3%       1    0.016s *)

    {
      (*Start Profiling.*)
      Time refine_binop_table.
      (*Show Profile.*)
      (*
total time:      0.531s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─setoid_rewrite_refine_binop_table_idx -  88.2% 100.0%       1    0.531s
─refine_binop_table --------------------   0.0% 100.0%       1    0.531s
─setoid_rewrite H ----------------------   5.9%   5.9%       1    0.031s
─replace_with_at_by --------------------   0.0%   2.9%       1    0.016s
─induction H ---------------------------   2.9%   2.9%       1    0.016s
─replace_with_vm_compute_in ------------   0.0%   2.9%       1    0.016s
─pose proof lem as H -------------------   2.9%   2.9%       1    0.016s
─replace c with c' in H by (clear; vm_ca   0.0%   2.9%       1    0.016s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─refine_binop_table --------------------   0.0% 100.0%       1    0.531s
└setoid_rewrite_refine_binop_table_idx -  88.2% 100.0%       1    0.531s
 ├─setoid_rewrite H --------------------   5.9%   5.9%       1    0.031s
 ├─replace_with_vm_compute_in ----------   0.0%   2.9%       1    0.016s
 │└replace c with c' in H by (clear; vm_   0.0%   2.9%       1    0.016s
 │└replace_with_at_by ------------------   0.0%   2.9%       1    0.016s
 │└induction H -------------------------   2.9%   2.9%       1    0.016s
 └─pose proof lem as H -----------------   2.9%   2.9%       1    0.016s
 *)
    }
    { finish honing parser method. }

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
  | context [@split_string_for_production ?Char ?HSL ?pdata ?it (Terminal "+"%char::?ps) (?str, _)]
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
            let c1 := match splitsv' with context[@list_of_next_bin_ops_opt ?a ?b] => constr:(@list_of_next_bin_ops_opt a b) end in
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
