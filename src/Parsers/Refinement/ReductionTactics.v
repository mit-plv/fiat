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
Require Import Fiat.Parsers.Refinement.FinishingLemma.

Global Arguments ilist.ith _ _ _ _ _ !_ / .
Global Arguments min !_ !_.
Global Arguments max !_ !_.
Global Arguments Compare_dec.leb !_ !_.
Global Arguments List.nth {A} !_ !_ _.

(** We use these aliases to allow us to unfold Fiat-level [fst] and
    [snd] without unfolding splitter-local [fst] and [snd]. *)
Definition myfst := @fst.
Definition mysnd := @snd.

Declare Reduction splitter_red0 := cbv [Fiat.ADTRefinement.GeneralRefinements.FullySharpened_Start projT1 FinishingLemma.finish_Sharpening_SplitterADT' ilist.icons BuildComputationalADT.BuildcADT ilist.inil BuildComputationalADT.cConsBody BuildComputationalADT.cMethBody fst snd].
Declare Reduction splitter_red1 := cbv [myfst mysnd].

Ltac splitter_red term :=
  let term := (eval splitter_red0 in term) in
  let term := (eval splitter_red1 in term) in
  constr:(term).

Global Arguments BooleanRecognizerOptimized.inner_nth' {_} _ !_ _ / .

Declare Reduction parser_red0 := cbv beta iota zeta delta [list_to_grammar grammar_of_pregrammar pregrammar_productions production_of_string magic_juxta_append_production magic_juxta_append_productions productions_of_production list_to_productions projT1 projT2 proj1_sig proj2_sig char_test char_to_test_eq or_chars and_chars neg_chars production_of_chartest ContextFreeGrammar.Notations.opt'.map ContextFreeGrammar.Notations.opt'.list_of_string ContextFreeGrammar.Notations.opt'.pred ContextFreeGrammar.Notations.opt'.length ContextFreeGrammar.Notations.opt'.substring (*magic_juxta_append_from_char_test*)].
Declare Reduction parser_red1 := simpl List.hd.
Declare Reduction parser_red2 := simpl List.fold_right.
Declare Reduction parser_red3 := simpl List.map.
Declare Reduction parser_red4 := cbv beta iota zeta delta [ParserInterface.parse ParserInterface.has_parse ParserFromParserADT.parser projT1 projT2 ComputationalADT.pcMethods ComputationalADT.pcConstructors ilist.ith VectorFacts.Vector_caseS' Vector.caseS ilist.ilist_hd ilist.ilist_tl ilist.prim_fst ilist.prim_snd StringLike.String StringLike.length StringLike.take StringLike.drop StringLike.get StringLike.is_char StringLike.bool_eq StringLike.beq string_stringlike string_stringlikemin OcamlString.Ocaml.string_stringlike OcamlString.Ocaml.string_stringlikemin BooleanRecognizerOptimized.rdp_list_to_production_opt item_rect grammar_of_pregrammar pregrammar_productions ContextFreeGrammar.Notations.opt'.map ContextFreeGrammar.Notations.opt'.list_of_string ContextFreeGrammar.Notations.opt'.pred ContextFreeGrammar.Notations.opt'.length ContextFreeGrammar.Notations.opt'.substring].
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

Ltac parser_red_gen term :=
  let term := match term with
                | context[ParserFromParserADT.parser _ ?splitter]
                  => let splitter' := head splitter in
                     (eval unfold splitter' in term)
                | _ => constr:(term)
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
  constr:(term).

Class eq_refl_vm_cast T := by_vm_cast : T.
Hint Extern 1 (eq_refl_vm_cast _) => clear; abstract (vm_compute; reflexivity) : typeclass_instances.

(* Work around an anomaly in 8.5 *)
Local Notation type_of x := ((fun T (y : T) => T) _ x).
Ltac type_of_no_anomaly x :=
  let T := constr:(type_of x) in
  (eval cbv beta in T).

Ltac make_Parser splitter :=
  let b0 := constr:(fun pf => ParserFromParserADT.parser pf splitter) in
  let T := match type_of_no_anomaly b0 with ?T -> _ => constr:(T) end in
  let quicker_opaque_eq_refl := constr:(_ : eq_refl_vm_cast T) in
  let b := constr:(b0 quicker_opaque_eq_refl) in
  b.

Ltac make_parser splitter :=
  idtac;
  let str := match goal with
               | [ str : String.string |- _ ] => constr:(str)
               | [ str : Ocaml.Ocaml.string |- _ ] => constr:(str)
             end in
  let b := make_Parser splitter in
  let b := constr:(ParserInterface.has_parse b str) in
  let b' := parser_red_gen b in
  exact_no_check b'.

Ltac make_parser_informative_opaque splitter :=
  idtac;
  let str := match goal with
               | [ str : String.string |- _ ] => constr:(str)
               | [ str : Ocaml.Ocaml.string |- _ ] => constr:(str)
             end in
  let b := make_Parser splitter in
  let b := (eval cbv beta in b) in
  let G := match type_of_no_anomaly b with @ParserInterface.Parser _ ?G _ _ => G end in
  let sound := constr:(ParserInterface.has_parse_sound b str) in
  let b := constr:(ParserInterface.has_parse b str) in
  let b' := parser_red_gen b in
  let v := constr:(match b' as b'' return b = b'' -> option (parse_of_item G str (NonTerminal (Start_symbol G))) with
                   | true => fun pf => Some (sound pf)
                   | false => fun _ => None
                   end (eq_refl b')) in
  exact_no_check v.

Ltac make_parser_informative splitter :=
  idtac;
  let str := match goal with
               | [ str : String.string |- _ ] => constr:(str)
               | [ str : Ocaml.Ocaml.string |- _ ] => constr:(str)
             end in
  let b := make_Parser splitter in
  let b := constr:(ParserInterface.parse b str) in
  let b' := parser_red_gen b in
  exact_no_check b'.

Ltac make_simplified_splitter' splitter :=
  idtac;
  let term := constr:(projT1 splitter) in
  let h := head splitter in
  let term := match constr:(Set) with
              | _ => (eval cbv [h] in term)
              | _ => term
              end in
  let impl := (splitter_red term) in
  refine (existT _ impl _).

Ltac make_simplified_splitter splitter :=
  make_simplified_splitter' splitter;
  abstract (exact (projT2 splitter)).
