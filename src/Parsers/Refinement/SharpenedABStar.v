(** Sharpened ADT for (ab)* *)
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Grammars.ABStar.
Set Implicit Arguments.

Section IndexedImpl.

  Lemma ComputationalSplitter'
  : FullySharpened (string_spec ab_star_grammar).
  Proof.

    start sharpening ADT.
    start honing parser using indexed representation.

    hone method "splits".
    {
      set_evars.
      simplify parser splitter.
      finish honing parser method.
    }
    finish_SharpeningADT_WithoutDelegation.

  Defined.

  Lemma ComputationalSplitter
  : FullySharpened (string_spec ab_star_grammar).
  Proof.
    let impl := (splitter_red (projT1 ComputationalSplitter')) in
    refine (existT _ impl _).
    abstract (exact (projT2 ComputationalSplitter')).
  Defined.

End IndexedImpl.

Require Export Fiat.Parsers.ParserFromParserADT.
Require Export Fiat.Parsers.ExtrOcamlParsers.
Export Fiat.Parsers.ExtrOcamlParsers.HideProofs.

Definition ab_star_parser (str : String.string) : bool.
Proof.
  Time make_parser ComputationalSplitter. (* 0.6 s *)
Defined.

Print ab_star_parser.

Recursive Extraction ab_star_parser.

Definition main_ab_star := premain ab_star_parser.

Parameter reference_ab_star_parser : Coq.Strings.String.string -> bool.
Extract Constant reference_ab_star_parser
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

Definition main_ab_star_reference := premain reference_ab_star_parser.

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
Definition test0 := ab_star_parser "".
Definition test1 := ab_star_parser "ab".
Definition str400 := "abababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababab".
Definition test2 := ab_star_parser (str400 ++ str400 ++ str400 ++ str400).

Recursive Extraction test0 test1 test2.
*)
