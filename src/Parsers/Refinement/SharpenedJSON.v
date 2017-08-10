(** Sharpened ADT for JSON *)
Require Import Fiat.Parsers.Grammars.JSONImpoverished.
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Refinement.DisjointRules.
Require Import Fiat.Parsers.Refinement.DisjointRulesRev.
Require Import Fiat.Parsers.ExtrOcamlParsers. (* for simpl rules for [find_first_char_such_that] *)
Require Import Fiat.Parsers.Refinement.BinOpBrackets.BinOpRules.
Require Import Fiat.Parsers.StringLike.String.

Section IndexedImpl.
  (*Context {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSI : StringIso Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          {HSEP : StringEqProperties Ascii.ascii}
          {HSIP : StringIsoProperties Ascii.ascii}.*)

  Lemma ComputationalSplitter'
  : FullySharpened (string_spec json'_grammar string_stringlike).
  Proof.
    (*Start Profiling.*)
    Time splitter_start.
    (*Show Profile.*)
    (*
total time:      1.250s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─splitter_start ------------------------  10.0% 100.0%       1    1.250s
─replace_with_at_by --------------------   1.3%  60.0%       1    0.750s
─set_tac -------------------------------   0.0%  46.3%       1    0.578s
─change x with x' ----------------------  46.3%  46.3%       1    0.578s
─apply_splitter_tower_lemma ------------   0.0%  28.7%       1    0.359s
─eapply lem ----------------------------  18.8%  18.8%       2    0.234s
─induction H ---------------------------   7.5%   7.5%       1    0.094s
─pose proof  (refine_opt2_fold_right_no_   5.0%   5.0%       1    0.063s
─assert (y = x') as H by (subst x'; tac)   0.0%   3.8%       1    0.047s
─cbv beta iota zeta delta [make_tower_no   3.8%   3.8%       1    0.047s
─tac -----------------------------------   0.0%   2.5%       1    0.031s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─splitter_start ------------------------  10.0% 100.0%       1    1.250s
 ├─replace_with_at_by ------------------   1.3%  60.0%       1    0.750s
 │ ├─set_tac ---------------------------   0.0%  46.3%       1    0.578s
 │ │└change x with x' ------------------  46.3%  46.3%       1    0.578s
 │ ├─induction H -----------------------   7.5%   7.5%       1    0.094s
 │ └─assert (y = x') as H by (subst x';    0.0%   3.8%       1    0.047s
 │  └tac -------------------------------   0.0%   2.5%       1    0.031s
 └─apply_splitter_tower_lemma ----------   0.0%  28.7%       1    0.359s
   ├─eapply lem ------------------------  18.8%  18.8%       1    0.234s
   ├─pose proof  (refine_opt2_fold_right   5.0%   5.0%       1    0.063s
   └─cbv beta iota zeta delta [make_towe   3.8%   3.8%       1    0.047s
*)
    (*Start Profiling.*)
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_rev_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_binop_table. }
    { Time refine_disjoint_search_for. }
    { Time refine_binop_table. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_rev_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { Time refine_binop_table. }
    { Time refine_disjoint_search_for. }
    { Time refine_binop_table. }
    { Time refine_disjoint_search_for. }
    { Time refine_disjoint_search_for. }
    { simplify parser splitter.
      (*Show Profile.*)
      (*

total time:    106.375s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─rewrite_disjoint_search_for_no_clear --   0.0%  49.7%      20    7.359s
─rewrite_disjoint_search_for -----------   0.0%  49.7%      20    7.359s
─rewrite_once_disjoint_search_for ------   0.0%  49.3%      40    7.313s
─rewrite_once_disjoint_search_for_specia  48.2%  49.0%      40    7.297s
─setoid_rewrite_refine_binop_table_idx -  43.5%  44.1%       4   12.969s
─refine_binop_table --------------------   0.0%  44.1%       4   12.969s
─rewrite_disjoint_rev_search_for_no_clea   0.0%   5.1%       2    2.703s
─rewrite_disjoint_rev_search_for -------   0.0%   5.1%       2    2.703s
─rewrite_once_disjoint_rev_search_for --   0.0%   5.0%       4    2.688s
─rewrite_once_disjoint_rev_search_for_sp   4.9%   5.0%       4    2.656s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─rewrite_disjoint_search_for -----------   0.0%  49.7%      20    7.359s
└rewrite_disjoint_search_for_no_clear --   0.0%  49.7%      20    7.359s
└rewrite_once_disjoint_search_for ------   0.0%  49.3%      40    7.313s
└rewrite_once_disjoint_search_for_specia  48.2%  49.0%      40    7.297s
─refine_binop_table --------------------   0.0%  44.1%       4   12.969s
└setoid_rewrite_refine_binop_table_idx -  43.5%  44.1%       4   12.969s
─rewrite_disjoint_rev_search_for -------   0.0%   5.1%       2    2.703s
└rewrite_disjoint_rev_search_for_no_clea   0.0%   5.1%       2    2.703s
└rewrite_once_disjoint_rev_search_for --   0.0%   5.0%       4    2.688s
└rewrite_once_disjoint_rev_search_for_sp   4.9%   5.0%       4    2.656s
 *)
      Time finish honing parser method.
    }

    Time finish_Sharpening_SplitterADT.

  Time Defined. (* 85 seconds *)

  Lemma ComputationalSplitter
  : FullySharpened (string_spec json'_grammar string_stringlike).
  Proof.
    (*Start Profiling.*)
    Time make_simplified_splitter ComputationalSplitter'. (* 19 s *)
    (*Show Profile.*)
  Time Defined.

Time End IndexedImpl.

Require Export Fiat.Parsers.ParserFromParserADT.
Require Export Fiat.Parsers.ExtrOcamlParsers.
Export Fiat.Parsers.ExtrOcamlParsers.HideProofs.
Require Export Fiat.Parsers.StringLike.OcamlString.

Definition json_parser (str : Coq.Strings.String.string) : bool.
Proof.
  (*Start Profiling.*)
  Time make_parser (@ComputationalSplitter(* _ String.string_stringlike _ _*)). (* 75 seconds *)
  (*Show Profile.*)
Time Defined.

(*Definition json_parser_ocaml (str : Ocaml.Ocaml.string) : bool.
Proof.
  Time make_parser (@ComputationalSplitter _ Ocaml.string_stringlike _ _). (* 0.82 s *)
Defined.*)

(*Recursive Extraction json_parser(*_ocaml*).*)
(*
Definition main_json := premain json_parser.
Definition main_json_ocaml := premain_ocaml json_parser_ocaml.

Parameter reference_json_parser : Coq.Strings.String.string -> bool.
Parameter reference_json_parser_ocaml : Ocaml.Ocaml.string -> bool.
Extract Constant reference_json_parser
=> "fun str ->
  let needs_b : bool Pervasives.ref = Pervasives.ref false in
  try
    (List.iter (fun ch ->
       match ch, !needs_b with
       | 'a', false -> needs_b := true; ()
       | 'b', true  -> needs_b := false; ()
       | _, _       -> raise Not_found)
       str;
     if !needs_b then false else true)
  with
   | Not_found -> false".
Extract Constant reference_json_parser_ocaml
=> "fun str ->
  let needs_b : bool Pervasives.ref = Pervasives.ref false in
  try
    (String.iter (fun ch ->
       match ch, !needs_b with
       | 'a', false -> needs_b := true; ()
       | 'b', true  -> needs_b := false; ()
       | _, _       -> raise Not_found)
       str;
     if !needs_b then false else true)
  with
   | Not_found -> false".

Definition main_json_reference := premain reference_json_parser.
Definition main_json_reference_ocaml := premain_ocaml reference_json_parser_ocaml.

(*
(* val needs_b : bool Pervasives.ref;; *)
let needs_b = Pervasives.ref false;;

let chan = match Array.length Sys.argv with
| 0 | 1 -> Pervasives.stdin
| 2 -> let chan = Pervasives.open_in Sys.argv.(1)
       in Pervasives.at_exit (fun () -> Pervasives.close_in chan);
	  chan
| argc -> Pervasives.exit argc;;

(* val line : string;; *)
let line = Pervasives.input_line chan;;

String.iter (fun ch ->
  match ch, !needs_b with
  | 'a', false -> needs_b := true; ()
  | 'b', true  -> needs_b := false; ()
  | _, _       -> Pervasives.exit 1)
  line;;

Pervasives.exit 0;;
*)
(*
Definition test0 := json_parser "".
Definition test1 := json_parser "ab".
Definition str400 := "abababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababab".
Definition test2 := json_parser (str400 ++ str400 ++ str400 ++ str400).

Recursive Extraction test0 test1 test2.
*)
*)
