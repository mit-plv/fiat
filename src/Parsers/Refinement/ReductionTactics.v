Require Fiat.Parsers.StringLike.OcamlString.
Require Fiat.Parsers.BooleanRecognizerOptimized.
Require Fiat.Parsers.ParserInterface Fiat.Parsers.ParserFromParserADT.
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.
Require Import Fiat.Common.
Require Import Fiat.Common.BoolFacts.
Require Import Fiat.Common.Wf Fiat.Common.Wf2.
Require Import Fiat.Common.List.Operations.
Require Export Fiat.Parsers.ExtrOcamlPrimitives.
Require Import Fiat.Parsers.StringLike.String.

Global Arguments ilist.ith _ _ _ _ _ !_ / .
Global Arguments min !_ !_.
Global Arguments max !_ !_.
Global Arguments Compare_dec.leb !_ !_.
Global Arguments List.nth {A} !_ !_ _.

Declare Reduction splitter_red0 := cbv beta iota zeta delta [ilist.icons BuildComputationalADT.BuildcADT ilist.inil BuildComputationalADT.cConsBody BuildComputationalADT.cMethBody].

Ltac splitter_red term :=
  let term0 := (eval simpl in term) in
  let term1 := (eval splitter_red0 in term0) in
  let term2 := (eval simpl in term1) in
  let term3 := (eval splitter_red0 in term2) in
  constr:term3.

Global Arguments BooleanRecognizerOptimized.inner_nth' {_} _ !_ _ / .

Declare Reduction parser_red0 := cbv beta iota zeta delta [list_to_grammar production_of_string magic_juxta_append_production magic_juxta_append_productions productions_of_production list_to_productions projT1 projT2 proj1_sig proj2_sig char_test char_to_test_eq or_chars neg_chars production_of_chartest (*magic_juxta_append_from_char_test*)].
Declare Reduction parser_red1 := simpl List.hd.
Declare Reduction parser_red2 := simpl List.fold_right.
Declare Reduction parser_red3 := simpl List.map.
Declare Reduction parser_red4 := cbv beta iota zeta delta [ParserInterface.has_parse ParserFromParserADT.parser projT1 projT2 ComputationalADT.pcMethods ComputationalADT.pcConstructors ilist.ith VectorFacts.Vector_caseS' Vector.caseS ilist.ilist_hd ilist.ilist_tl ilist.prim_fst ilist.prim_snd StringLike.String StringLike.length StringLike.take StringLike.drop StringLike.get StringLike.is_char StringLike.bool_eq StringLike.beq string_stringlike string_stringlikemin OcamlString.Ocaml.string_stringlike OcamlString.Ocaml.string_stringlikemin BooleanRecognizerOptimized.rdp_list_to_production_opt item_rect].
Declare Reduction parser_red5 := opt_red.
Declare Reduction parser_red6 := simpl @fst.
Declare Reduction parser_red7 := simpl @snd.
Declare Reduction parser_red8 := opt2_red.
Declare Reduction parser_red9 := simpl orb.
Declare Reduction parser_red10 := opt3_red.
Declare Reduction parser_red11 := simpl orb.
Declare Reduction parser_red12 := cbv beta iota zeta delta [List.nth' Fix2 Fix2_F].
(*Declare Reduction parser_red6 := simpl @fst.
Declare Reduction parser_red7 := simpl @snd.
Declare Reduction parser_red8 := simpl List.length.
Declare Reduction parser_red9 := simpl List.fold_right.
Declare Reduction parser_red10 := simpl @List.first_index_default.
Declare Reduction parser_red11 := simpl @List.up_to.
Declare Reduction parser_red12 := simpl @Compare_dec.leb.
Declare Reduction parser_red13 := simpl @Operations.List.uniquize.
Declare Reduction parser_red14 := simpl @List.combine.
Declare Reduction parser_red15 := simpl @BooleanRecognizerOptimized.inner_nth'.
(*Declare Reduction parser_red16 := simpl List.map.*)
Declare Reduction parser_red17 := cbv beta iota zeta delta [List.nth' Fix2 Fix2_F].*)

Ltac parser_red_gen term do_simpl_list_map :=
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
  let term := (eval parser_red5 in term) in
  let term := (eval parser_red6 in term) in
  let term := (eval parser_red7 in term) in
  let term := (eval parser_red8 in term) in
  let term := (eval parser_red9 in term) in
  let term := (eval parser_red10 in term) in
  let term := (eval parser_red11 in term) in
  let term := (eval parser_red12 in term) in
(*
  let term := (match do_simpl_list_map with
                 | true => eval simpl List.map in term
                 | _ => term
               end) in
  let term := (eval parser_red17 in term) in*)
  constr:term.

Class eq_refl_vm_cast T := by_vm_cast : T.
Hint Extern 1 (eq_refl_vm_cast _) => clear; abstract (vm_compute; reflexivity) : typeclass_instances.

Ltac make_parser_gen splitter do_simpl_list_map :=
  idtac;
  let str := match goal with
               | [ str : String.string |- _ ] => constr:str
               | [ str : Ocaml.Ocaml.string |- _ ] => constr:str
             end in
  let b0 := constr:(fun pf => ParserInterface.has_parse (ParserFromParserADT.parser pf splitter) str) in
  let T := match type of b0 with ?T -> _ => constr:T end in
  let quicker_opaque_eq_refl := constr:(_ : eq_refl_vm_cast T) in
  let b := constr:(b0 quicker_opaque_eq_refl) in
  let b' := parser_red_gen b do_simpl_list_map in
  exact_no_check b'.

Ltac make_parser splitter := make_parser_gen splitter true.
Ltac make_parser_without_simpl_list_map splitter := make_parser_gen splitter false.

Ltac make_simplified_splitter' splitter :=
  idtac;
  let impl := (splitter_red (projT1 splitter)) in
  refine (existT _ impl _).

Ltac make_simplified_splitter splitter :=
  make_simplified_splitter' splitter;
  abstract (exact (projT2 splitter)).
