(** Sharpened ADT for (ab)* *)
Require Import ADTSynthesis.Parsers.Refinement.Tactics.
Require Import ADTSynthesis.Parsers.Grammars.ABStar.
Set Implicit Arguments.

Section IndexedImpl.

  Lemma ComputationalSplitter
  : FullySharpened (string_spec ab_star_grammar).
  Proof.
    start honing parser using indexed representation.

    hone method "splits".
    {
      simplify parser splitter.
      finish honing parser method.
    }

    FullySharpenEachMethodWithoutDelegation.
    extract delegate-free implementation.
    simpl; higher_order_reflexivityT.
  Defined.

End IndexedImpl.

Require Import ADTSynthesis.Parsers.ParserFromParserADT.
Require Import ADTSynthesis.Parsers.ExtrOcamlParsers.

Local Ltac do_compute_in term hyp :=
  let term' := (eval compute in term) in
  change term with term' in hyp.

Local Ltac do_lazy_in term hyp :=
  let term' := (eval lazy in term) in
  change term with term' in hyp.

Local Ltac do_simpl_in term hyp :=
  let term' := (eval simpl in term) in
  change term with term' in hyp.

Local Ltac do_hnf_in term hyp :=
  let term' := (eval hnf in term) in
  change term with term' in hyp.

Local Ltac set_subst_hnf_in term hyp :=
  let H := fresh in
  set (H := term) in hyp;
    hnf in H;
    cbv beta iota zeta delta [H] in hyp;
    subst H.

Local Arguments string_dec : simpl never.
Local Arguments Equality.string_beq : simpl never.
Arguments SplitterFromParserADT.msplits / .
Arguments splits_for / .
Local Notation hextr0 := (ex _).
Local Notation exist' x := (exist _ x _).
Local Notation hextr1 := (or_intror _).
Local Notation hextr2 := (or_introl _).

Definition ab_star_parser' (str : String.string) : bool.
Proof.
  pose (has_parse (parser ComputationalSplitter) str) as impl.
  Timeout 2 cbv beta iota zeta delta [has_parse parser ParserImplementationOptimized.parser transfer_parser List.fold_right] in impl.
  repeat (let impl' := (eval cbv delta [impl] in impl) in
          match impl' with
            | appcontext G[fst (?x, _)] => let G' := context G[x] in change impl' with G' in impl
            | appcontext G[snd (_, ?x)] => let G' := context G[x] in change impl' with G' in impl
          end).
  Timeout 2 cbv beta iota zeta delta [List.map List.hd List.fold_left item_ascii_cons item_of_char item_of_string] in impl.
  repeat (let impl' := (eval cbv delta [impl] in impl) in
          match impl' with
            | appcontext G[fst (?x, _)] => let G' := context G[x] in change impl' with G' in impl
            | appcontext G[snd (_, ?x)] => let G' := context G[x] in change impl' with G' in impl
          end).
  Timeout 2 cbv beta iota zeta delta [BooleanRecognizer.parse_production BooleanRecognizer.parse_item BooleanBaseTypes.split_string_for_production parser_data ParserImplementation.parser_data new_string_of_string] in impl.
  change (orb false) with (fun x : bool => x) in impl.
  cbv beta in impl.
  change (@StringLike.String Ascii.ascii (ParserInterface.string_type
                                            (SplitterFromParserADT.adt_based_splitter
                                               ComputationalSplitter)))
  with ({ r : (String.string * (nat * nat)) | exists orig, AbsR (projT2 ComputationalSplitter) orig r }%type)
    in impl.
  Timeout 2 change ((@StringLike.length _ (ParserInterface.string_type
                                             (SplitterFromParserADT.adt_based_splitter
                                                ComputationalSplitter))))
  with (fun str : { r : (String.string * (nat * nat)) | exists orig, AbsR (projT2 ComputationalSplitter) orig r }%type => ilength (` str)) in impl.
  do_simpl_in (Valid_nonterminals ab_star_grammar) impl.
  Timeout 2 change (new_string_of_base_string ComputationalSplitter str)
  with (str, (0, String.length str)) in impl.
  Timeout 2 cbv beta iota zeta in impl.
  Timeout 2 cbv beta iota zeta delta [splits_for] in impl.
  Timeout 2 cbv beta iota zeta delta [is_char string_type splits_for SplitterFromParserADT.adt_based_splitter] in impl.
  Timeout 2 cbv beta iota zeta delta [SplitterFromParserADT.msplits ComputationalADT.cMethods ComputationalADT.pcMethods] in impl.
  Timeout 2 match eval cbv delta [impl] in impl with
              | context[@projT2 ?A ?B (@projT1 ?C ?D ComputationalSplitter)]
                => set_subst_hnf_in (@projT2 A B (@projT1 C D ComputationalSplitter)) impl
            end.
  Timeout 2 cbv beta iota zeta delta [BuildComputationalADT.getcMethDef BuildComputationalADT.cMethBody] in impl.
(** HERE *)
Locate StringBound.ith_Bounded.
Print StringBound.ith_Bounded.
Print StringBound.BoundedIndex.
Print StringBound.IndexBound.

  Timeout 2 let H := fresh in
            set (H := (projT2 (projT1 ComputationalSplitter))) in impl;
              hnf in H;
              subst H.

  let
  Timeout 2 set_subst_hnf_in (projT2 (projT1 ComputationalSplitter)) impl.
  hnf in X.
  Timeout 2 subst X.
  Opaque AbsR.
  Timeout 2 pose (sf := (splits_for
                         (SplitterFromParserADT.adt_based_splitter
                            ComputationalSplitter))).
  hnf in sf.
  Set Printing Implicit.
  Opaque StringLike.String SplitterFromParserADT.adt_based_StringLike AbsR.
  Opaque ComputationalSplitter.
  Timeout 2 simpl in impl.
  Transparent SplitterFromParserADT.adt_based_StringLike.
  Timeout 2 simpl in impl.
  Arguments SplitterFromParserADT.mis_char / .
  Timeout 2 simpl in impl.
  Unset Printing Implicit.
  Transparent ComputationalSplitter.
  Arguments ComputationalADT.cMethodType / .
  Arguments ComputationalADT.cMethods / .
  Arguments If_Then_Else / .
  repeat (let impl' := (eval cbv delta [impl] in impl) in
          match impl' with
            | appcontext G[ComputationalADT.cMethods
                             (projT1 ComputationalSplitter)
                             {| StringBound.bindex := "splits";
                                StringBound.indexb := ?b |}]
              => let m' := (eval simpl in (ComputationalADT.cMethods
                                             (projT1 ComputationalSplitter)
                                             {| StringBound.bindex := "splits";
                                                StringBound.indexb := b |})) in
                 change ((ComputationalADT.cMethods
                            (projT1 ComputationalSplitter)
                            {| StringBound.bindex := "splits";
                               StringBound.indexb := b |}))
                 with m' in impl
          end).
  Timeout 2 (repeat (let impl' := (eval cbv delta [impl] in impl) in
          match impl' with
            | appcontext G[ComputationalADT.cMethods
                             (projT1 ComputationalSplitter)
                             {| StringBound.bindex := "is_char";
                                StringBound.indexb := ?b |}]
              => let m' := (eval simpl in (ComputationalADT.cMethods
                                             (projT1 ComputationalSplitter)
                                             {| StringBound.bindex := "is_char";
                                                StringBound.indexb := b |})) in
                 change ((ComputationalADT.cMethods
                            (projT1 ComputationalSplitter)
                            {| StringBound.bindex := "is_char";
                               StringBound.indexb := b |}))
                 with m' in impl
          end)).
  Timeout 2 cbv beta iota zeta in impl.
  Timeout 2 (do 6 let impl' := (eval cbv delta [impl] in impl) in
                    match impl' with
                      | appcontext G[fst (?x, ?y)] => change (fst (x, y)) with x in impl
                      | appcontext G[snd (?x, ?y)] => change (snd (x, y)) with y in impl
                    end).
  Opaque ComputationalSplitter.
  Timeout 2 simpl in impl.
  Timeout 5 (let impl' := (eval cbv delta [impl] in impl) in
          match impl' with
            | appcontext G[fst (?x, _)] => let G' := context G[x] in pose G'
            | appcontext G[snd (_, ?x)] => let G' := context G[x] in change impl' with G' in impl
          end).
  Timeout 5 (let impl' := (eval cbv delta [impl] in impl) in
                    match impl' with
                      | appcontext G[fst (?x, ?y)] => timeout 2 change (fst (x, y)) with x in impl
                      | appcontext G[snd (?x, ?y)] => timeout 2 change (snd (x, y)) with y in impl
                    end).

  Timeout 2 simpl in c.
               | appcontext G[snd (_, ?x)] => let G' := context G[x] in change impl' with G' in impl
             end).

  match
  Timeout 4 do_simpl_in (projT1 ComputationalSplitter) impl.
  Arguments SplitterFromParserADT.mis_char / .
    change (splits_for
                         (SplitterFromParserADT.adt_based_splitter
                            ComputationalSplitter)) with sf in impl.

  Timeout 2 simpl in impl.
  Timeout 2 cbv beta iota zeta delta [List.map] in impl.

  Timeout 2 hnf in sf.
  let T := match type of sf with ?T -> _ => constr:T end in
  set (T' := T) in sf;
    change T with T' in sf.
  match eval cbv delta [sf] in sf with
    | fun x : ?T => _ => change T with T' in sf
  end.
  Timeout 2 simpl in sf.
  Timeout 2 cbv delta [sf] in impl.
  subst T' sf.
  Timeout 2 change
  Timeout 2 simpl in sf.
  Timeout 2 let term := constr:() in
  let term' := (eval simpl in term) in
  let term'' := (eval cbv beta in (fun str : { r : (String.string * (nat * nat)) | exists orig, AbsR (projT2 ComputationalSplitter) orig r }%type => term' str)) in
  idtac.
  change term with term'' in impl.
  change term with
Local Ltac do_simpl_in term hyp :=
  let term' := (eval simpl in term) in
  change term with term' in hyp.

  Timeout 2 do_simpl_in () impl.
assert (x : { r : (String.string * (nat * nat)) | exists orig, AbsR (projT2 ComputationalSplitter) orig r }%type) by (exfalso; clear; admit).
pose (splits_for
                                              (SplitterFromParserADT.adt_based_splitter
                                                 ComputationalSplitter) x).
Timeout 2 simpl in l.

Timeout 2 simpl in l.

  Timeout 2 simpl @fst in impl.

  match goal with
    | [
  Timeout 2 unfold List.fold_right in impl.
  Timeout 2 unfold BooleanRecognizer.parse_production in impl.
  Timeout 2 simpl BooleanRecognizer.parse_production in impl.
  cbv beta iota zeta delta [string_has_parse ParserInterface.has_parse base_parser ParserImplementation.parser BooleanRecognizer.parse_nonterminal BooleanRecognizer.parse_nonterminal_or_abort BooleanRecognizer.parse_nonterminal_step BooleanRecognizer.parse_productions BaseTypes.initial_nonterminals_data BooleanBaseTypes.predata ParserImplementation.parser_data RDPList.rdp_list_predata BaseTypes.remove_nonterminal BaseTypes.nonterminals_listT_R BaseTypes.nonterminals_listT RDPList.rdp_list_nonterminals_listT RDPList.rdp_list_nonterminals_listT_R BaseTypes.is_valid_nonterminal RDPList.rdp_list_is_valid_nonterminal BaseTypes.ntl_wf RDPList.rdp_list_remove_nonterminal] in impl.
  Timeout 2 do_simpl_in (Lookup ab_star_grammar) impl.
  Timeout 2 cbv beta iota zeta in impl.
  let impl' := (eval cbv delta [impl] in impl) in exact impl'.
Defined.

Definition ab_star_parser : String.string -> bool
  := Eval cbv zeta delta [ab_star_parser'] in ab_star_parser'.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlIntConv.
Require Import ExtrOcamlNatInt.
Recursive Extraction ab_star_parser.
Proof.


  Timeout 5 simpl in impl.



  cbv beta iota zeta delta [Wf.Fix3] in impl.
  Timeout 2 change ((@StringLike.length _ (ParserInterface.string_type
                                             (SplitterFromParserADT.adt_based_splitter
                                                ComputationalSplitter))))
  with (fun str : { r : (String.string * (nat * nat)) | exists orig, AbsR (projT2 ComputationalSplitter) orig r }%type => ilength (` str)) in impl.
  Timeout 2 change (@StringLike.length  _ (ParserInterface.string_type
                                                (SplitterFromParserADT.adt_based_splitter
                                                   ComputationalSplitter)))
  with (fun str :
  with (fun str : {r : string * (nat * nat) | hextr0} =>
        SplitterFromParserADT.mlength ComputationalSplitter () (` str))
  in impl"), last call failed.
  Timeout 2 do_simpl_in (@StringLike.length _ (ParserInterface.string_type
                                                (SplitterFromParserADT.adt_based_splitter
                                                   ComputationalSplitter))) impl.

  with (exist _ (str, (0, String.length str)) (proj2_sig (new_string_of_base_string ComputationalSplitter str))) in impl.
  Arguments new_string_of_base_string / .

  Timeout 2 do_simpl_in (new_string_of_base_string ComputationalSplitter str) impl.

  Timeout 2 lazy beta iota zeta delta [BaseTypes.remove_nonterminal BaseTypes.nonterminals_listT_R StringLike.String StringLike.length] in impl.
  unfold Lookup in *.

  unfold RelationClasses.reflexivity in impl.
  unfold RelationClasses.Equivalence_Reflexive in impl.
  unfold bool_eq_Equivalence in *.
  Timeout 3 cbv delta [BooleanRecognizer.parse_nonterminal BooleanRecognizer.parse_nonterminal_or_abort] in b.
  Timeout 10 simpl in b.
  let impl := (eval unfold b in b) in
  let impl' := (eval cbv beta iota zeta delta [BooleanRecognizer.parse_nonterminal] in impl) in
  pose impl'.
Timeout 2 simpl in b.
  refine (fun s => has_parse (parser (adt_based_splitter ComputationalSplitter))
                             (exist _ (cConstructors (projT1 ComputationalSplitter) {| StringBound.bindex := "new" |} s) (ex_intro _ s _))).
  abstract (
      pose proof (ADTRefinementPreservesConstructors (projT2 ComputationalSplitter) {| StringBound.bindex := "new" |} s (cConstructors (projT1 ComputationalSplitter) {| StringBound.bindex := "new" |} s) (ReturnComputes _)) as H'';
      computes_to_inv;
      simpl in H'';
      computes_to_inv; subst; assumption
    ).
Defined.

Definition ab_star_parser' : String.string -> bool.
Proof.
Print ab_star_parser.


  hnf.
  simpl.
  simpl.
  pose .
  simpl in *.
  Require Import StringLike.Core StringLike.String.
  Timeout 2 simpl.
  hnf.
  unfold string_type.
  Locate adt_based_splitter.
  pose .
  simpl in c.
  unfold cConstructorType in *.

lazy.
 (s, (0, String.length s))).
    simpl in b.
Require Import StringLike.Core.
simpl in b.
Set Printing All.


Check ab_star_parser.
Check .
