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

    Time start sharpening ADT.
    Start Profiling.
    Time start honing parser using indexed representation.
    Show Profile.

    Start Profiling.
    Time hone method "splits".
    Show Profile.
    {
      Start Profiling.
      Time simplify parser splitter.
      Time rewrite_disjoint_search_for.
      Time rewrite_disjoint_rev_search_for.
      Time progress repeat refine_binop_table.
      Time simplify parser splitter.
      Show Profile.
      (*
total time:    350.916s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─rewrite_disjoint_search_for -----------   0.0%  64.2%       1  225.292s
─rewrite_disjoint_search_for_no_clear --   0.0%  64.2%       1  225.284s
─rewrite_once_disjoint_search_for ------   0.0%  64.2%      21   22.164s
─rewrite_once_disjoint_search_for_specia  38.5%  52.1%      21   18.988s
─refine_binop_table --------------------   0.0%  16.0%       5   14.976s
─setoid_rewrite_refine_binop_table_idx -  11.7%  16.0%       4   14.972s
─simplify parser splitter --------------   0.0%  15.3%       2   27.100s
─simplify ------------------------------   0.0%  15.3%       2   27.100s
─simplify_parser_splitter' -------------   0.0%  15.3%      37    7.140s
─setoid_rewrite lem' -------------------  11.6%  12.9%      21    3.340s
─vm_compute ----------------------------   9.6%   9.6%      87    1.216s
─assert T as H' by DisjointRules.solve_d   0.0%   8.6%     160    0.528s
─DisjointRules.solve_disjoint_side_condi   0.0%   8.6%     160    0.528s
─rewrite_disjoint_rev_search_for -------   0.0%   4.5%       1   15.680s
─rewrite_disjoint_rev_search_for_no_clea   0.0%   4.5%       1   15.672s
─rewrite_once_disjoint_rev_search_for --   0.0%   4.5%       2   10.700s
─replace_with_vm_compute_in ------------   0.0%   4.0%      89    0.224s
─replace c with c' in H by (clear; vm_ca   0.0%   4.0%      89    0.224s
─replace_with_at_by --------------------   0.1%   4.0%      89    0.224s
─setoid_rewrite H ----------------------   3.5%   3.8%       4    4.276s
─rewrite_once_disjoint_rev_search_for_sp   2.1%   3.6%       2   10.700s
─induction H ---------------------------   3.2%   3.2%      89    0.180s
─simplify with monad laws --------------   0.0%   3.0%      29    0.800s
─simplify_with_applied_monad_laws ------   0.0%   3.0%      29    0.800s
─rewrite <- !andb_orb_distrib_r_assoc --   2.1%   2.1%      18    6.168s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─rewrite_disjoint_search_for -----------   0.0%  64.2%       1  225.292s
└rewrite_disjoint_search_for_no_clear --   0.0%  64.2%       1  225.284s
└rewrite_once_disjoint_search_for ------   0.0%  64.2%      21   22.164s
 ├─rewrite_once_disjoint_search_for_spec  38.5%  52.1%      21   18.988s
 │ ├─assert T as H' by DisjointRules.sol   0.0%   8.6%     160    0.528s
 │ │└DisjointRules.solve_disjoint_side_c   0.0%   8.6%     160    0.528s
 │ │└vm_compute ------------------------   8.5%   8.5%      80    0.528s
 │ └─replace_with_vm_compute_in --------   0.0%   3.5%      80    0.196s
 │  └replace c with c' in H by (clear; v   0.0%   3.5%      80    0.196s
 │  └replace_with_at_by ----------------   0.1%   3.5%      80    0.196s
 │  └induction H -----------------------   2.8%   2.8%      80    0.164s
 └─setoid_rewrite lem' -----------------  10.8%  12.1%      20    3.340s
─refine_binop_table --------------------   0.0%  16.0%       5   14.976s
└setoid_rewrite_refine_binop_table_idx -  11.7%  16.0%       4   14.972s
└setoid_rewrite H ----------------------   3.5%   3.8%       4    4.276s
─simplify parser splitter --------------   0.0%  15.3%       2   27.100s
└simplify ------------------------------   0.0%  15.3%       2   27.100s
└simplify_parser_splitter' -------------   0.0%  15.3%      37    7.140s
 ├─simplify with monad laws ------------   0.0%   3.0%      29    0.800s
 │└simplify_with_applied_monad_laws ----   0.0%   3.0%      29    0.800s
 └─rewrite <- !andb_orb_distrib_r_assoc    2.1%   2.1%      18    6.168s
─rewrite_disjoint_rev_search_for -------   0.0%   4.5%       1   15.680s
└rewrite_disjoint_rev_search_for_no_clea   0.0%   4.5%       1   15.672s
└rewrite_once_disjoint_rev_search_for --   0.0%   4.5%       2   10.700s
└rewrite_once_disjoint_rev_search_for_sp   2.1%   3.6%       2   10.700s
 *)
      Time finish honing parser method.
    }

    Time finish_Sharpening_SplitterADT.

  Time Defined. (* 132 seconds *)

  Lemma ComputationalSplitter
  : FullySharpened (string_spec json'_grammar string_stringlike).
  Proof.
    Start Profiling.
    Time make_simplified_splitter ComputationalSplitter'.
    Show Profile.
  Time Defined.

Time End IndexedImpl.

Require Export Fiat.Parsers.ParserFromParserADT.
Require Export Fiat.Parsers.ExtrOcamlParsers.
Export Fiat.Parsers.ExtrOcamlParsers.HideProofs.
Require Export Fiat.Parsers.StringLike.OcamlString.

Definition json_parser (str : Coq.Strings.String.string) : bool.
Proof.
  Start Profiling.
  Time make_parser (@ComputationalSplitter(* _ String.string_stringlike _ _*)).
  Show Profile.
Time Defined.

(*Definition json_parser_ocaml (str : Ocaml.Ocaml.string) : bool.
Proof.
  Time make_parser (@ComputationalSplitter _ Ocaml.string_stringlike _ _). (* 0.82 s *)
Defined.*)

Print json_parser(*_ocaml*).

Recursive Extraction json_parser(*_ocaml*).
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
