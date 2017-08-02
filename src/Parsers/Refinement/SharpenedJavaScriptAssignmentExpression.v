Require Import Fiat.Parsers.Grammars.JavaScriptAssignmentExpression.
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Refinement.DisjointRules.
Require Import Fiat.Parsers.Refinement.DisjointRulesRev.
Require Import Fiat.Parsers.ExtrOcamlParsers. (* for simpl rules for [find_first_char_such_that] *)
Require Import Fiat.Parsers.Refinement.BinOpBrackets.BinOpRules.
Require Import Fiat.Parsers.StringLike.String.

(*Require Coq.micromega.Lia.
Require Coq.PArith.BinPos.
Require Coq.Lists.List.
Require Coq.Sorting.Mergesort.
Require Coq.Structures.OrdersEx.
Require Coq.Strings.Ascii.
Require Coq.Strings.String.
Require Fiat.Parsers.ContextFreeGrammar.Core.
Require Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Fiat.Parsers.ContextFreeGrammar.Reflective.
Require Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Fiat.Parsers.Refinement.PossibleTerminalsSets.*)
Require ExplorationUtil.
Set Ltac Profiling.
Section IndexedImpl.
  (*Context {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSI : StringIso Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          {HSEP : StringEqProperties Ascii.ascii}
          {HSIP : StringIsoProperties Ascii.ascii}.*)

  Lemma ComputationalSplitter'
  : FullySharpened (string_spec javascript_assignment_expression_pregrammar string_stringlike).
  Proof.

    Time start sharpening ADT.

    Reset Ltac Profile.
    Time start honing parser using indexed representation.
    Show Ltac Profile.

    Reset Ltac Profile.
    Time hone method "splits".
    Show Ltac Profile.
    {
      Reset Ltac Profile.
      Time simplify parser splitter.
      Show Ltac Profile.
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for , \s* ... *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for , \s* ... *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for , \s* ... *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for , \s* ... *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* binop search for ... \s* = *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for *= \s* ... N.B. This is different, requires 2-char binop *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* binop search for ... \s* = *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for *= \s* ... N.B. This is different, requires 2-char binop *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* binop search for ... \s* = *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for *= \s* ... N.B. This is different, requires 2-char binop *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* binop search for ... \s* = *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for *= \s* ... N.B. This is different, requires 2-char binop *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* binop search for ... \s* & *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* binop search for ... \s* & *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* binop search for ... \s* & *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* binop search for ... \s* & *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for = \s* ... *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for = \s* ... *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for = \s* ... *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for = \s* ... *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for < \s* ... *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* ??? wtf [true instanceof Boolean instanceof new "instanceof"] and [true instanceof Boolean instanceof new instanceof] *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for < \s* ... *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* ??? wtf [true instanceof Boolean instanceof new "instanceof"] and [true instanceof Boolean instanceof new instanceof] *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for < \s* ... *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* ??? wtf [true instanceof Boolean instanceof new "instanceof"] and [true instanceof Boolean instanceof new instanceof] *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* ??? wtf [true in Object in new "in"] and [true in Object in new in] (invalid parse) *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for < \s* ... *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* ??? wtf [true instanceof Boolean instanceof new "instanceof"] and [true instanceof Boolean instanceof new instanceof] *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* ??? wtf [true in Object in new "in"] and [true in Object in new in] (invalid parse) *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for + \s* ... *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for + \s* ... *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for * \s* ... *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for * \s* ... *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse disjoint + fixed length for ... \s* ++ *) }
      { exfalso; admit. (* reverse disjoint + fixed length for ... \s* ++ *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for , \s* ... *) }
      { exfalso; admit. (* reverse disjoint + fixed length for ... \s* ) *) }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse disjoint + fixed length for ... \s* ] *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* ???  "[]. a . a", "[]. a [ [] + [] ]" *) }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse paren search for \s* (...) N.B. this requires 0-char binops *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse paren search for \s* (...) N.B. this requires 0-char binops *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* ???  "[]. a . a", "[]. a [ [] + [] ]" *) }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse paren search for \s* (...) N.B. this requires 0-char binops *) }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* ???  "[]. a . a", "[]. a [ [] + [] ]" *) }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse paren search for \s* (...) N.B. this requires 0-char binops *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for , \s* ... *) }
      { exfalso; admit. (* reverse disjoint + fixed length for ... \s* ] *) }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse binop search for , \s* ... (hopefully?) *) }
      { exfalso; admit. (* reverse disjoint + fixed length for ... \s* } *) }
      { Time shelve; refine_disjoint_search_for. }
      { exfalso; admit. (* reverse disjoint + fixed length for ... \s* ) *) }
      { Time shelve; refine_disjoint_search_for. }
      (*{ Time Import ExplorationUtil.
        pose javascript_assignment_expression_pregrammar as G.
        print_production javascript_assignment_expression_pregrammar (4, (0, 1)).
        print_productions G "LiteralField".
        print_productions G "LiteralElement".
        print_productions G "AssignmentExpression normal,allowIn".
        print_productions G "MemberOperator".
        print_productions G "CallExpression initial".
        print_productions G "ShortNewSubexpression".
        print_productions G "Arguments".
        print_productions G "FullNewSubexpression".
        print_productions G "FullNewSubexpression".
        print_productions G "PrimaryExpression normal".
        print_productions G "MemberOperator".
        print_chars "MemberOperator".
        print_productions G "ArgumentList".
        print_last_chars "PostfixExpression normal".
        print_productions G "RelationalExpression initial,noIn".
        print_productions G "AdditiveExpression normal".
        print_productions G "MultiplicativeExpression normal".
        print_productions G "UnaryExpression normal".
        print_productions G "PostfixExpression normal".
        print_productions G "LeftSideExpression normal".
        print_productions G "ShortNewExpression".
        print_productions G "Arguments".
        print_productions G "ShortNewSubexpression".
        print_productions G "FullNewSubexpression".
        print_productions G "PrimaryExpression normal".
        print_productions G "SimpleExpression".
        print_productions G "ObjectLiteral".
        print_productions G "Identifier".
        print_productions G "CallExpression normal"
        print_productions G "SimpleExpression".
        print_productions G "AssignmentExpression normal,noIn".
        print_chars "CompoundAssignment".
        print_productions javascript_assignment_expression_pregrammar "Expression initial,noIn".
        print_productions G "AssignmentExpression normal,noIn".
        print_productions javascript_assignment_expression_pregrammar "LeftSideExpression normal".
        print_productions javascript_assignment_expression_pregrammar "AssignmentExpression normal,allowIn".
        print_productions G "CompoundAssignment".*)
      (*{ Require Import ExplorationUtil.
        print_production javascript_assignment_expression_pregrammar (4, (0, 2)).
print_productions javascript_assignment_expression_pregrammar "LiteralField". (*"MemberOperator". *)
        pose javascript_assignment_expression_pregrammar as G.
        print_productions javascript_assignment_expression_pregrammar "LeftSideExpression normal".
        print_productions javascript_assignment_expression_pregrammar "AssignmentExpression normal,allowIn".
        print_productions G "CompoundAssignment".*)

      simplify parser splitter.
      Show Ltac Profile.
      (*
total time:     84.328s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─rewrite_disjoint_search_for -----------   0.0%  39.4%      20    4.268s
─rewrite_disjoint_search_for_no_clear --   0.0%  39.3%      20    4.260s
─rewrite_once_disjoint_search_for ------   0.0%  38.8%      40    4.240s
─rewrite_once_disjoint_search_for_specia  33.6%  38.3%      40    4.212s
─refine_binop_table --------------------   0.0%  37.9%       4    8.036s
─setoid_rewrite_refine_binop_table_idx -  37.0%  37.9%       4    8.032s
─simplify parser splitter --------------   0.0%  18.7%       2   14.980s
─simplify_parser_splitter' -------------   0.0%  18.7%      31   12.444s
─simplify ------------------------------   0.0%  18.7%       2   14.980s
─eapply (refine_opt2_fold_right r_o retv  13.5%  13.5%       1   11.364s
─simplify with monad laws --------------   0.0%   4.4%      30    1.900s
─simplify_with_applied_monad_laws ------   0.0%   4.4%      30    1.900s
─rewrite_disjoint_rev_search_for -------   0.0%   3.9%       2    1.636s
─rewrite_disjoint_rev_search_for_no_clea   0.0%   3.8%       2    1.632s
─rewrite_once_disjoint_rev_search_for --   0.0%   3.8%       4    1.608s
─rewrite_once_disjoint_rev_search_for_sp   3.4%   3.7%       4    1.572s
─specialize (lem' H') ------------------   2.7%   2.7%      44    1.996s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─rewrite_disjoint_search_for -----------   0.0%  39.4%      20    4.268s
└rewrite_disjoint_search_for_no_clear --   0.0%  39.3%      20    4.260s
└rewrite_once_disjoint_search_for ------   0.0%  38.8%      40    4.240s
└rewrite_once_disjoint_search_for_specia  33.6%  38.3%      40    4.212s
└specialize (lem' H') ------------------   2.6%   2.6%      40    1.996s
─refine_binop_table --------------------   0.0%  37.9%       4    8.036s
└setoid_rewrite_refine_binop_table_idx -  37.0%  37.9%       4    8.032s
─simplify parser splitter --------------   0.0%  18.7%       2   14.980s
└simplify ------------------------------   0.0%  18.7%       2   14.980s
└simplify_parser_splitter' -------------   0.0%  18.7%      31   12.444s
 ├─eapply (refine_opt2_fold_right r_o re  13.5%  13.5%       1   11.364s
 └─simplify with monad laws ------------   0.0%   4.4%      30    1.900s
  └simplify_with_applied_monad_laws ----   0.0%   4.4%      30    1.900s
─rewrite_disjoint_rev_search_for -------   0.0%   3.9%       2    1.636s
└rewrite_disjoint_rev_search_for_no_clea   0.0%   3.8%       2    1.632s
└rewrite_once_disjoint_rev_search_for --   0.0%   3.8%       4    1.608s
└rewrite_once_disjoint_rev_search_for_sp   3.4%   3.7%       4    1.572s
 *)
      Time finish honing parser method.
    }

    Time finish_Sharpening_SplitterADT.

  Time Defined. (* 85 seconds *)

  Lemma ComputationalSplitter
  : FullySharpened (string_spec json'_grammar string_stringlike).
  Proof.
    Reset Ltac Profile.
    Time make_simplified_splitter ComputationalSplitter'. (* 19 s *)
    Show Ltac Profile.
  Time Defined.

Time End IndexedImpl.

Require Export Fiat.Parsers.ParserFromParserADT.
Require Export Fiat.Parsers.ExtrOcamlParsers.
Export Fiat.Parsers.ExtrOcamlParsers.HideProofs.
Require Export Fiat.Parsers.StringLike.OcamlString.

Definition json_parser (str : Coq.Strings.String.string) : bool.
Proof.
  Reset Ltac Profiling.
  Time make_parser (@ComputationalSplitter(* _ String.string_stringlike _ _*)). (* 75 seconds *)
  Show Ltac Profile.
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
