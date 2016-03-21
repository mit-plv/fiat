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
Time (idtac;
  let lem := fresh "lem" in
  pose_disjoint_search_for lem;
    (*do 1 ( *)let lem' := fresh "lem'" in
          (idtac;
  let G := (lazymatch goal with
             | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
               => G
             end) in
  match goal with
  | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
    => pose proof (lem idx) as lem';
       do 2 (lazymatch type of lem' with
              | forall a : ?T, _ => idtac; let x := fresh in evar (x : T); specialize (lem' x); subst x
              end);
       let T := match type of lem' with forall a : ?T, _ => T end in
       let H' := fresh in
       assert (H' : T) by solve_disjoint_side_conditions;
       specialize (lem' H'); clear H';
       let x := match type of lem' with
                | context[DisjointLemmas.actual_possible_first_terminals ?ls]
                  => constr:(DisjointLemmas.actual_possible_first_terminals ls)
                end in
       pose x
end)).
Time vm_compute in l; subst l.
let x := (eval cbv delta [x] in l) in
replace

       replace_with_vm_compute_in x lem';
       unfold Equality.list_bin in lem';
       change (orb false) with (fun bv : bool => bv) in lem';
       cbv beta in lem';
       let T := match type of lem' with forall a : ?T, _ => T end in
       let H' := fresh in
       assert (H' : T) by solve_disjoint_side_conditions;
       specialize (lem' H'); clear H'
  end);
  setoid_rewrite lem'; clear lem');
  clear lem).
      exfalso; clear; admit. } exfalso; clear; admit. Grab Existential Variables. exfalso; clear; admit. exfalso; clear; admit.
    Time Defined. (* 8.6 with no disjoint rewrite, 12 with do 5, 26 with 10 *)
Set Printing Depth 100000.

      Time rewrite_disjoint_search_for.
      exfalso; clear; admit. } exfalso; clear; admit. Grab Existential Variables. exfalso; clear; admit. exfalso; clear; admit.
    Time Defined.    (* 1 - 2.28, 2 - 2.6, 3 - 2.6, 4 - 2.74, 5 - 2.8, 6 - 5.97 *)
Set Printing Depth 10000.
About andb_orb_distrib_r_assoc.
        first [
        rewrite <- !andb_orb_distrib_r_assoc ].
        | rewrite !if_aggregate
        | rewrite !beq_0_1_leb
        | rewrite !beq_S_leb ].
        | idtac;
          match goal with
            | [ |- context[If ?b Then ?x Else If ?b' Then ?x Else _] ]
              => idtac
          end;
          progress repeat setoid_rewrite if_aggregate
        | rewrite !if_aggregate2 by solve_prod_beq
        | rewrite !if_aggregate3 by solve_prod_beq
        | progress parser_pull_tac
        | progress (simpl @fst; simpl @snd) ].

      exfalso; clear; admit. } exfalso; clear; admit. Grab Existential Variables. exfalso; clear; admit. exfalso; clear; admit.
    Time Defined.    (* 1 - 2.28, 2 - 2.6, 3 - 2.6, 4 - 2.74, 5 - 2.8, 6 - 5.97 *)

      first [ progress unguard
        | progress autounfold with parser_sharpen_db;
          cbv beta iota zeta;
          simpl @Operations.List.uniquize;
          simpl @List.fold_right
        | rewrite !Bool.orb_false_r
        | rewrite <- !Bool.andb_orb_distrib_r
        | progress simplify with monad laws
        | rewrite <- !Bool.andb_orb_distrib_r
        | rewrite <- !Bool.andb_orb_distrib_l
        | rewrite <- !Bool.orb_andb_distrib_r
        | rewrite <- !Bool.orb_andb_distrib_l
        | rewrite <- !Bool.andb_assoc
        | rewrite <- !Bool.orb_assoc
        | rewrite <- !andb_orb_distrib_r_assoc
        | rewrite !if_aggregate
        | rewrite !beq_0_1_leb
        | rewrite !beq_S_leb
        | idtac;
          match goal with
            | [ |- context[If ?b Then ?x Else If ?b' Then ?x Else _] ]
              => idtac
          end;
          progress repeat setoid_rewrite if_aggregate
        | rewrite !if_aggregate2 by solve_prod_beq
        | rewrite !if_aggregate3 by solve_prod_beq
        | progress parser_pull_tac
        | progress (simpl @fst; simpl @snd) ].

  Time simplify parser splitter.
      Time rewrite_disjoint_rev_search_for.
      Time progress repeat refine_binop_table.
      Time simplify parser splitter.
      Show Profile.
      (*
total time:    324.664s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─rewrite_disjoint_search_for -----------   0.0%  62.4%       1  202.748s
─rewrite_disjoint_search_for_no_clear --   0.0%  62.4%       1  202.740s
─rewrite_once_disjoint_search_for ------   0.0%  62.4%      21   20.084s
─rewrite_once_disjoint_search_for_specia   0.0%  50.2%      21   16.988s
─vm_compute in x' ----------------------  41.1%  41.1%      85    4.552s
─refine_binop_table --------------------   0.0%  16.8%       5   14.424s
─setoid_rewrite_refine_binop_table_idx -   0.4%  16.8%       4   14.420s
─simplify parser splitter --------------   0.0%  16.5%       2   26.996s
─simplify ------------------------------   0.0%  16.5%       2   26.996s
─simplify_parser_splitter' -------------   0.0%  16.5%      38    6.996s
─setoid_rewrite lem' -------------------  11.5%  12.9%      21    3.156s
─vm_compute in c0 ----------------------  12.3%  12.3%       4   10.032s
─vm_compute ----------------------------  10.3%  10.3%      87    1.212s
─assert T as H' by DisjointRules.solve_d   0.0%   9.3%     160    0.592s
─DisjointRules.solve_disjoint_side_condi   0.0%   9.3%     160    0.592s
─rewrite_disjoint_rev_search_for -------   0.0%   4.2%       1   13.704s
─rewrite_disjoint_rev_search_for_no_clea   0.0%   4.2%       1   13.692s
─rewrite_once_disjoint_rev_search_for --   0.0%   4.2%       2    9.520s
─setoid_rewrite H ----------------------   3.6%   3.9%       4    3.940s
─rewrite_once_disjoint_rev_search_for_sp   0.0%   3.5%       2    9.520s
─simplify with monad laws --------------   0.0%   3.2%      29    0.812s
─simplify_with_applied_monad_laws ------   0.0%   3.2%      29    0.812s
─rewrite <- !andb_orb_distrib_r_assoc --   2.2%   2.2%      18    6.084s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─rewrite_disjoint_search_for -----------   0.0%  62.4%       1  202.748s
└rewrite_disjoint_search_for_no_clear --   0.0%  62.4%       1  202.740s
└rewrite_once_disjoint_search_for ------   0.0%  62.4%      21   20.084s
 ├─rewrite_once_disjoint_search_for_spec   0.0%  50.2%      21   16.988s
 │ ├─vm_compute in x' ------------------  38.9%  38.9%      80    4.552s
 │ └─assert T as H' by DisjointRules.sol   0.0%   9.3%     160    0.592s
 │  └DisjointRules.solve_disjoint_side_c   0.0%   9.3%     160    0.592s
 │  └vm_compute ------------------------   9.2%   9.2%      80    0.592s
 └─setoid_rewrite lem' -----------------  10.8%  12.2%      20    3.156s
─refine_binop_table --------------------   0.0%  16.8%       5   14.424s
└setoid_rewrite_refine_binop_table_idx -   0.4%  16.8%       4   14.420s
 ├─vm_compute in c0 --------------------  12.3%  12.3%       4   10.032s
 └─setoid_rewrite H --------------------   3.6%   3.9%       4    3.940s
─simplify parser splitter --------------   0.0%  16.5%       2   26.996s
└simplify ------------------------------   0.0%  16.5%       2   26.996s
└simplify_parser_splitter' -------------   0.0%  16.5%      38    6.996s
 ├─simplify with monad laws ------------   0.0%   3.2%      29    0.812s
 │└simplify_with_applied_monad_laws ----   0.0%   3.2%      29    0.812s
 └─rewrite <- !andb_orb_distrib_r_assoc    2.2%   2.2%      18    6.084s
─rewrite_disjoint_rev_search_for -------   0.0%   4.2%       1   13.704s
└rewrite_disjoint_rev_search_for_no_clea   0.0%   4.2%       1   13.692s
└rewrite_once_disjoint_rev_search_for --   0.0%   4.2%       2    9.520s
└rewrite_once_disjoint_rev_search_for_sp   0.0%   3.5%       2    9.520s
└vm_compute in x' ----------------------   2.2%   2.2%       5    1.588s
 *)
      finish honing parser method.
    }

    finish_Sharpening_SplitterADT.

  Time Defined.

  Lemma ComputationalSplitter
  : FullySharpened (string_spec json'_grammar string_stringlike).
  Proof.
    Start Profiling.
    Time make_simplified_splitter ComputationalSplitter'.
    Show Profile.
  Time Defined.

End IndexedImpl.

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
