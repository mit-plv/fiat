(** Sharpened ADT for (ab)* *)
Require Import Fiat.Parsers.Grammars.ABStar.
Require Import Fiat.Parsers.Refinement.Tactics.

Section IndexedImpl.
  Context {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          {HSIP : StringEqProperties Ascii.ascii}.

  Lemma ComputationalSplitter'
  : FullySharpened (string_spec ab_star_grammar HSL).
  Proof.

    start sharpening ADT.
    start honing parser using indexed representation.

    hone method "splits".
    {
      simplify parser splitter.
      finish honing parser method.
    }

    finish_Sharpening_SplitterADT.

  Defined.

  Lemma ComputationalSplitter
  : FullySharpened (string_spec ab_star_grammar HSL).
  Proof.
    make_simplified_splitter ComputationalSplitter'.
  Defined.

End IndexedImpl.

Require Export Fiat.Parsers.ParserFromParserADT.
Require Export Fiat.Parsers.ExtrOcamlParsers.
Export Fiat.Parsers.ExtrOcamlParsers.HideProofs.
Require Export Fiat.Parsers.StringLike.OcamlString.

Definition ab_star_parser (str : Coq.Strings.String.string) : bool.
Proof.
  Time make_parser (@ComputationalSplitter _ String.string_stringlike _ _). (* 0.82 s *)
Defined.

Definition ab_star_parser_ocaml (str : Ocaml.Ocaml.string) : bool.
Proof.
  Time make_parser (@ComputationalSplitter _ Ocaml.string_stringlike _ _). (* 0.82 s *)
Defined.

Print ab_star_parser_ocaml.

Recursive Extraction ab_star_parser_ocaml.

Definition main_ab_star := premain ab_star_parser.
Definition main_ab_star_ocaml := premain_ocaml ab_star_parser_ocaml.

Parameter reference_ab_star_parser : Coq.Strings.String.string -> bool.
Parameter reference_ab_star_parser_ocaml : Ocaml.Ocaml.string -> bool.
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
Extract Constant reference_ab_star_parser_ocaml
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

Definition main_ab_star_reference := premain reference_ab_star_parser.
Definition main_ab_star_reference_ocaml := premain_ocaml reference_ab_star_parser_ocaml.

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
