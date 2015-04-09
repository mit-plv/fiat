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
  Defined.

End IndexedImpl.

Require Import ADTSynthesis.Parsers.ParserFromParserADT.

Local Ltac do_compute_in term hyp :=
  let term' := (eval compute in term) in
  change term with term' in hyp.

Local Ltac do_lazy_in term hyp :=
  let term' := (eval lazy in term) in
  change term with term' in hyp.

Local Ltac do_simpl_in term hyp :=
  let term' := (eval simpl in term) in
  change term with term' in hyp.

Local Arguments string_dec : simpl never.
Local Arguments Equality.string_beq : simpl never.
Local Notation hextr0 := (ex _).
Local Notation exist' x := (exist _ x _).
Local Notation hextr1 := (or_intror _).
Local Notation hextr2 := (or_introl _).

Definition ab_star_parser' (str : String.string) : bool.
Proof.
  pose (string_has_parse ComputationalSplitter str) as impl.
  cbv beta iota zeta delta [string_has_parse ParserInterface.has_parse base_parser ParserImplementation.parser BooleanRecognizer.parse_nonterminal BooleanRecognizer.parse_nonterminal_or_abort BooleanRecognizer.parse_nonterminal_step BooleanRecognizer.parse_productions BaseTypes.initial_nonterminals_data BooleanBaseTypes.predata ParserImplementation.parser_data RDPList.rdp_list_predata BaseTypes.remove_nonterminal BaseTypes.nonterminals_listT_R BaseTypes.nonterminals_listT RDPList.rdp_list_nonterminals_listT RDPList.rdp_list_nonterminals_listT_R BaseTypes.is_valid_nonterminal RDPList.rdp_list_is_valid_nonterminal BaseTypes.ntl_wf RDPList.rdp_list_remove_nonterminal] in impl.
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
