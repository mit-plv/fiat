(** Sharpened ADT for JavaScript Comments *)
Require Import Fiat.Parsers.Grammars.JSComment.
Require Import Fiat.Parsers.Refinement.Tactics.

Section IndexedImpl.
  Context {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          {HSIP : StringEqProperties Ascii.ascii}.

  Lemma ComputationalSplitter'
  : FullySharpened (string_spec js_comment_grammar HSL).
  Proof.
    (*Start Profiling.*)
    Time splitter_start; splitter_finish.
    (*Show Profile.*)
    (*
total time:      9.520s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─splitter_start ------------------------   0.0%  88.5%       1    8.428s
─simplify parser splitter --------------   0.0%  43.7%       1    4.156s
─simplify_parser_splitter' -------------   0.0%  43.7%      26    0.288s
─simplify ------------------------------   0.0%  43.7%       1    4.156s
─simpl ---------------------------------  40.8%  40.8%     106    3.552s
─start honing parser using indexed repre   0.0%  40.6%       1    3.864s
─start_honing --------------------------   0.0%  40.6%       1    3.864s
─simplify with monad laws --------------   0.0%  16.2%      27    0.172s
─simplify_with_applied_monad_laws ------   0.3%  16.2%      27    0.172s
─splitter_finish -----------------------   0.0%  11.5%       2    1.068s
─finish_honing_by_eq -------------------   0.0%  11.2%       1    1.068s
─finish honing parser method -----------   0.0%  11.2%       1    1.068s
─rewrite General.refineEquiv_pick_eq' --   6.6%  10.5%       3    0.984s
─rewrite <- !Bool.andb_orb_distrib_r ---   4.9%   4.9%      23    0.136s
─hone method "splits" ------------------   0.3%   4.3%       1    0.408s
─unguard -------------------------------   0.0%   4.1%      26    0.100s
─rewrite ?(unguard [0]) ----------------   4.0%   4.1%      26    0.100s
─eapply refine_under_bind_helper_1 -----   3.9%   3.9%     175    0.012s
─eapply refine_under_bind_helper_2 -----   3.5%   3.5%     175    0.012s
─eapply refine_under_bind_helper -------   3.5%   3.5%     175    0.012s
─set (H := E) --------------------------   3.0%   3.0%       1    0.288s
─rewrite !if_aggregate3 by solve_prod_be   1.7%   2.6%       5    0.112s
─rewrite !if_aggregate2 by solve_prod_be   1.8%   2.4%       8    0.068s
─rewrite !if_aggregate -----------------   2.4%   2.4%      12    0.108s
─apply reflexivity ---------------------   2.2%   2.2%     608    0.012s
─apply refine_bind_bind_helper ---------   2.1%   2.1%     177    0.008s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─splitter_start ------------------------   0.0%  88.5%       1    8.428s
 ├─simplify parser splitter ------------   0.0%  43.7%       1    4.156s
 │└simplify ----------------------------   0.0%  43.7%       1    4.156s
 │└simplify_parser_splitter' -----------   0.0%  43.7%      26    0.288s
 │ ├─simplify with monad laws ----------   0.0%  15.9%      25    0.172s
 │ │└simplify_with_applied_monad_laws --   0.3%  15.9%      25    0.172s
 │ │ ├─eapply refine_under_bind_helper_1   3.8%   3.8%     173    0.012s
 │ │ ├─eapply refine_under_bind_helper_2   3.5%   3.5%     173    0.012s
 │ │ ├─eapply refine_under_bind_helper -   3.5%   3.5%     173    0.012s
 │ │ └─apply refine_bind_bind_helper ---   2.1%   2.1%     175    0.008s
 │ ├─rewrite <- !Bool.andb_orb_distrib_r   4.9%   4.9%      23    0.136s
 │ ├─unguard ---------------------------   0.0%   4.1%      26    0.100s
 │ │└rewrite ?(unguard [0]) ------------   4.0%   4.1%      26    0.100s
 │ ├─rewrite !if_aggregate3 by solve_pro   1.7%   2.6%       5    0.112s
 │ ├─rewrite !if_aggregate2 by solve_pro   1.8%   2.4%       8    0.068s
 │ └─rewrite !if_aggregate -------------   2.4%   2.4%      12    0.108s
 ├─start honing parser using indexed rep   0.0%  40.6%       1    3.864s
 │└start_honing ------------------------   0.0%  40.6%       1    3.864s
 │└simpl -------------------------------  40.6%  40.6%       2    3.552s
 └─hone method "splits" ----------------   0.3%   4.3%       1    0.408s
  └set (H := E) ------------------------   3.0%   3.0%       1    0.288s
─splitter_finish -----------------------   0.0%  11.5%       2    1.068s
└finish honing parser method -----------   0.0%  11.2%       1    1.068s
└finish_honing_by_eq -------------------   0.0%  11.2%       1    1.068s
└rewrite General.refineEquiv_pick_eq' --   6.6%  10.5%       3    0.984s
└apply reflexivity ---------------------   2.1%   2.1%     579    0.012s
 *)
  Defined.

  Lemma ComputationalSplitter
  : FullySharpened (string_spec js_comment_grammar HSL).
  Proof.
    make_simplified_splitter ComputationalSplitter'.
  Defined.

End IndexedImpl.

Require Export Fiat.Parsers.ParserFromParserADT.
Require Export Fiat.Parsers.ExtrOcamlParsers.
Export Fiat.Parsers.ExtrOcamlParsers.HideProofs.
Require Export Fiat.Parsers.StringLike.OcamlString.

Definition js_comment_parser (str : Coq.Strings.String.string) : bool.
Proof.
  Time make_parser (@ComputationalSplitter _ String.string_stringlike _ _). (* 0.82 s *)
Defined.

Definition js_comment_parser_ocaml (str : Ocaml.Ocaml.string) : bool.
Proof.
  Time make_parser (@ComputationalSplitter _ Ocaml.string_stringlike _ _). (* 0.82 s *)
Defined.

Definition main_js_comment := premain js_comment_parser.
Definition main_js_comment_ocaml := premain_ocaml js_comment_parser_ocaml.
(*
Parameter reference_js_comment_parser : Coq.Strings.String.string -> bool.
Parameter reference_js_comment_parser_ocaml : Ocaml.Ocaml.string -> bool.
Extract Constant reference_js_comment_parser
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
Extract Constant reference_js_comment_parser_ocaml
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

Definition main_js_comment_reference := premain reference_js_comment_parser.
Definition main_js_comment_reference_ocaml := premain_ocaml reference_js_comment_parser_ocaml.

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
Definition test0 := js_comment_parser "".
Definition test1 := js_comment_parser "ab".
Definition str400 := "abababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababab".
Definition test2 := js_comment_parser (str400 ++ str400 ++ str400 ++ str400).

Recursive Extraction test0 test1 test2.
*)
*)
