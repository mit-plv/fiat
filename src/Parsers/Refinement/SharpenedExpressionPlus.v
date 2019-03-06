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
      { (*Set Ltac Profiling.*)
        Time refine_disjoint_search_for.
        (*Show Ltac Profile.*)
        (*Show Profile.*)
        (*
total time:      0.496s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─rewrite_disjoint_search_for -----------   0.0%  99.2%       1    0.492s
─rewrite_disjoint_search_for_no_clear --   0.0%  97.6%       1    0.484s
─rewrite_once_disjoint_search_for ------   0.0%  92.7%       2    0.460s
─rewrite_once_disjoint_search_for_specia   4.0%  86.3%       2    0.428s
─replace_with_at_by --------------------   0.0%  58.9%       1    0.292s
─replace_with_vm_compute_in ------------   0.0%  58.9%       1    0.292s
─replace c with c' in H by (clear; vm_ca   0.0%  58.9%       1    0.292s
─set_tac -------------------------------   0.0%  43.5%       1    0.216s
─set (x' := x) in H --------------------  43.5%  43.5%       1    0.216s
─induction H ---------------------------   9.7%   9.7%       1    0.048s
─assert T as H' by solve_disjoint_side_c   0.8%   5.6%       2    0.016s
─clear H' ------------------------------   5.6%   5.6%       3    0.012s
─setoid_rewrite lem' -------------------   4.8%   5.6%       1    0.028s
─solve_disjoint_side_conditions --------   0.8%   4.8%       2    0.016s
─assert (y = x') as H by (subst x'; tac)   0.0%   4.8%       1    0.024s
─subst x -------------------------------   4.8%   4.8%       2    0.012s
─pose_disjoint_search_for --------------   0.8%   4.8%       1    0.024s
─specialize (lem' H') ------------------   4.0%   4.0%       2    0.012s
─specialize (lem' x) -------------------   3.2%   3.2%       2    0.008s
─reflexivity ---------------------------   3.2%   3.2%       4    0.012s
─subst x' ------------------------------   2.4%   2.4%       1    0.012s
─vm_compute ----------------------------   2.4%   2.4%       2    0.008s
─tac -----------------------------------   0.0%   2.4%       1    0.012s
─clear ---------------------------------   2.4%   2.4%       1    0.012s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─rewrite_disjoint_search_for -----------   0.0%  99.2%       1    0.492s
└rewrite_disjoint_search_for_no_clear --   0.0%  97.6%       1    0.484s
 ├─rewrite_once_disjoint_search_for ----   0.0%  92.7%       2    0.460s
 │ ├─rewrite_once_disjoint_search_for_sp   4.0%  86.3%       2    0.428s
 │ │ ├─replace_with_vm_compute_in ------   0.0%  58.9%       1    0.292s
 │ │ │└replace c with c' in H by (clear;   0.0%  58.9%       1    0.292s
 │ │ │└replace_with_at_by --------------   0.0%  58.9%       1    0.292s
 │ │ │ ├─set_tac -----------------------   0.0%  43.5%       1    0.216s
 │ │ │ │└set (x' := x) in H ------------  43.5%  43.5%       1    0.216s
 │ │ │ ├─induction H -------------------   9.7%   9.7%       1    0.048s
 │ │ │ └─assert (y = x') as H by (subst    0.0%   4.8%       1    0.024s
 │ │ │   ├─subst x' --------------------   2.4%   2.4%       1    0.012s
 │ │ │   └─tac -------------------------   0.0%   2.4%       1    0.012s
 │ │ │    └clear -----------------------   2.4%   2.4%       1    0.012s
 │ │ ├─assert T as H' by solve_disjoint_   0.8%   5.6%       2    0.016s
 │ │ │└solve_disjoint_side_conditions --   0.8%   4.8%       2    0.016s
 │ │ │└reflexivity ---------------------   2.4%   2.4%       2    0.012s
 │ │ ├─subst x -------------------------   4.8%   4.8%       2    0.012s
 │ │ ├─clear H' ------------------------   4.0%   4.0%       2    0.012s
 │ │ ├─specialize (lem' H') ------------   4.0%   4.0%       2    0.012s
 │ │ └─specialize (lem' x) -------------   3.2%   3.2%       2    0.008s
 │ └─setoid_rewrite lem' ---------------   4.8%   5.6%       1    0.028s
 └─pose_disjoint_search_for ------------   0.8%   4.8%       1    0.024s
         *) }
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
  Time make_parser ComputationalSplitter. (* 0.088 s *)
Defined.

Print paren_expr_parser.

Recursive Extraction paren_expr_parser.
