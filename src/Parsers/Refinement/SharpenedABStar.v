(** Sharpened ADT for (ab)* *)
Require Import Fiat.Parsers.Grammars.ABStar.
Require Import Fiat.Parsers.Refinement.Tactics.

Section IndexedImpl.
  Context {HSL : StringLike Ascii.ascii}
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
  Time make_parser (@ComputationalSplitter String.string_stringlike _ _). (* 0.82 s *)
Defined.

Definition ab_star_parser_ocaml (str : Ocaml.Ocaml.string) : bool.
Proof.
(*Declare Reduction parser_red0' := cbv beta iota zeta delta [list_to_grammar item_ascii_cons item_of_char list_to_productions BooleanRecognizerOptimized.str_carrier_default projT1 projT2 proj1_sig proj2_sig].
Declare Reduction parser_red4' := cbv beta iota zeta delta [ParserInterface.has_parse ParserFromParserADT.parser projT1 projT2 ComputationalADT.pcMethods ComputationalADT.pcConstructors ilist.ith VectorFacts.Vector_caseS' Vector.caseS ilist.ilist_hd ilist.ilist_tl ilist.prim_fst ilist.prim_snd BooleanRecognizerOptimized.of_string BooleanRecognizerOptimized.to_string StringLike.String StringLike.length StringLike.take StringLike.drop StringLike.get StringLike.is_char StringLike.bool_eq StringLike.beq string_stringlike RDPList.rdp_list_to_production Carriers.default_to_production].
Global Arguments BooleanRecognizerOptimized.inner_nth' {_} _ !_ _ / .
  Time let splitter := ComputationalSplitter in
  let do_simpl_list_map := true in
    idtac;
  let str := match goal with
               | [ str : String.string |- _ ] => constr:str
               | [ str : Ocaml.Ocaml.string |- _ ] => constr:str
             end in
  let b0 := constr:(fun pf => ParserInterface.has_parse (ParserFromParserADT.parser pf splitter) str) in
  let T := match type of b0 with ?T -> _ => constr:T end in
  let quicker_opaque_eq_refl := constr:(_ : eq_refl_vm_cast T) in
  let b := constr:(b0 quicker_opaque_eq_refl) in
  let b' := let term := b in
  let term := match term with
                | context[ParserFromParserADT.parser _ ?splitter]
                  => let splitter' := head splitter in
                     (eval unfold splitter' in term)
                | _ => constr:term
              end in
  let term := (eval parser_red0 in term) in
  let term := (eval parser_red1 in term) in
  let term := (eval parser_red2 in term) in
  let term := (eval parser_red3 in term) in
  let term := (eval parser_red4 in term) in
  let term := (eval cbv beta iota zeta delta [BooleanRecognizerOptimized.rdp_list_to_production_opt item_rect] in term) in
  let term := (eval parser_red5 in term) in
  let term := (eval parser_red6 in term) in
  let term := (eval parser_red7 in term) in
  let term := (eval parser_red8 in term) in
  let term := (eval parser_red9 in term) in
  let term := (eval parser_red10 in term) in
  let term := (eval parser_red11 in term) in
  let term := (eval parser_red12 in term) in
  let term := (eval parser_red13 in term) in
  let term := (eval parser_red14 in term) in
  let term := (eval simpl @BooleanRecognizerOptimized.inner_nth' in term) in
  let term := (eval simpl @List.fold_left in term) in(*
  let term := (match do_simpl_list_map with
                 | true => eval simpl List.map in term
                 | _ => term
               end) in
  let term := (eval parser_red16 in term) in*)
  constr:term in
  (*let b' := (eval cbv beta iota zeta delta [RDPList.rdp_list_to_production Carriers.default_to_production] in b') in
  let b' := parser_red_gen b' do_simpl_list_map in*)
  pose b'.
  .
  parser_red0 in *.
  simpl @RDPList.rdp_list_to_production
  Time make_parser ComputationalSplitter. (* 0.6 s *)*)
  Time make_parser ComputationalSplitter. (* 0.6 s *)
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
