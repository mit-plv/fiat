Require Fiat.Parsers.StringLike.OcamlString.
Require Fiat.Parsers.ParserInterface Fiat.Parsers.ParserFromParserADT.
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.
Require Import Fiat.Common.
Require Import Fiat.Common.BoolFacts.
Require Import Fiat.Common.Wf Fiat.Common.Wf2.
Require Export Fiat.Parsers.ExtrOcamlPrimitives.
Require Import Fiat.Parsers.StringLike.String.
Require Import Fiat.Parsers.Refinement.FinishingLemma.
Require Import Fiat.Parsers.ParserInterfaceReflective.

Global Arguments ilist.ith _ _ _ _ _ !_ / .
Global Arguments min !_ !_.
Global Arguments max !_ !_.
Global Arguments Compare_dec.leb !_ !_.
Global Arguments List.nth {A} !_ !_ _.

(** We use these aliases to allow us to unfold Fiat-level [fst] and
    [snd] without unfolding splitter-local [fst] and [snd]. *)
Definition myfst := @fst.
Definition mysnd := @snd.

Declare Reduction splitter_red0 := hnf.
Declare Reduction splitter_red1 := cbv [Fiat.ADTRefinement.GeneralRefinements.FullySharpened_Start projT1 FinishingLemma.finish_Sharpening_SplitterADT' ilist.icons BuildComputationalADT.BuildcADT ilist.inil BuildComputationalADT.cConsBody BuildComputationalADT.cMethBody fst snd].
Declare Reduction splitter_red2 := cbv [myfst mysnd].

Ltac splitter_red term :=
  let term := (eval splitter_red0 in term) in
  let term := (eval splitter_red1 in term) in
  let term := (eval splitter_red2 in term) in
  constr:(term).

(*Global Arguments BooleanRecognizerOptimized.inner_nth' {_} _ !_ _ / .*)

(*(** Coq is stupid and doesn't have a version of [simpl]/[cbv] which unfolds *only* the given list of constants but *does not* unfold them if there's not a constructor in the head position of specified arguments.  See https://coq.inria.fr/bugs/show_bug.cgi?id=4639.  So we write a tactic that works in a specific case. *)
Ltac eval_change_bool term :=
  match eval cbv beta in term with
  | context T[andb true]
    => let term' := context T[fun x : bool => x] in
       eval_change_bool term'
  | context T[andb false]
    => let term' := context T[fun x : bool => false] in
       eval_change_bool term'
  | context T[orb true]
    => let term' := context T[fun x : bool => true] in
       eval_change_bool term'
  | context T[orb false]
    => let term' := context T[fun x : bool => x] in
       eval_change_bool term'
  | context T[@If_Then_Else ?A true]
    => let term' := context T[fun x y : A => x] in
       eval_change_bool term'
  | context T[@If_Then_Else ?A false]
    => let term' := context T[fun x y : A => y] in
       eval_change_bool term'
  | ?term' => term'
  end.*)

Declare Reduction parser_red0 := cbv [ParserInterface.parse ParserInterface.has_parse ParserFromParserADT.parser ParserInterfaceReflective.rhas_parse Semantics.apply_args_for Syntax.map_args_for Semantics.interp_Term_gen_step Semantics.interp_Term_gen SemanticsOptimized.opt.interp_Term Semantics.interp_SimpleTypeCode Semantics.interp_SimpleTypeCode_step pregrammar_idata char_at_matches_interp interp_RCharExpr SemanticsOptimized.opt.interp_RLiteralTerm projT2 projT1 ComputationalADT.pcMethods BuildComputationalADT.getcMethDef ilist.ith VectorFacts.Vector_caseS' Vector.caseS ilist.ilist_hd ilist.ilist_tl ilist.prim_fst ilist.prim_snd ComputationalADT.pcConstructors BuildComputationalADT.getcConsDef BuildComputationalADT.cMethBody BuildComputationalADT.cConsBody StringLike.length String.string_stringlikemin OcamlString.Ocaml.string_stringlikemin irbeq irN_of ascii_interp_RCharExpr_data char_at_matches Common.opt2.fst Common.opt2.snd Common.opt2.beq_nat Common.opt2.leb Common.opt2.andb Common.opt2.orb If_Then_Else].
Declare Reduction parser_red1 := cbv [SemanticsOptimized.opt.nth' SemanticsOptimized.opt.fold_left SemanticsOptimized.opt.map bool_rect_nodep bool_rec_nodep Fix2 Fix2_F].

Ltac parser_red_gen term :=
  let term := match term with
                | context[ParserFromParserADT.parser _ _ ?splitter]
                  => let splitter' := head splitter in
                     (eval unfold splitter' in term)
                | _ => constr:(term)
              end in
  let term := match term with
                | context[ParserFromParserADT.parser (G := ?G) _ _ _]
                  => let G' := head G in
                     (eval unfold G' in term)
                | _ => constr:(term)
              end in
  let term := (eval parser_red0 in term) in
  let term := (eval parser_red1 in term) in
  term.

(* Work around an anomaly in 8.5 *)
Local Notation type_of x := ((fun T (y : T) => T) _ x).
Ltac type_of_no_anomaly x :=
  let T := constr:(type_of x) in
  (eval cbv beta in T).

Ltac make_Parser splitter :=
  let G := match type of splitter with
           | context[pregrammar'_of_pregrammar ?G] => G
           end in
  let preparser := make_ParserReflective G in
  let b0 := constr:(fun pf => ParserFromParserADT.parser preparser pf splitter) in
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
  (*let b := parser_red_gen b in*)
  exact_no_check b.

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
