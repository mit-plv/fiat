(** Sharpened ADT for (ab)* *)
Require Import ADTSynthesis.Parsers.Refinement.Tactics.
Require Import ADTSynthesis.Parsers.Grammars.ABStar.
Set Implicit Arguments.

Section IndexedImpl.

  Lemma ComputationalSplitter'
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

  Lemma ComputationalSplitter
  : FullySharpened (string_spec ab_star_grammar).
  Proof.
    let impl := (eval simpl in (projT1 ComputationalSplitter')) in
    refine (existT _ impl _).
    abstract (exact (projT2 ComputationalSplitter')).
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
Arguments Equality.ascii_beq !_ !_ / .
Arguments SplitterFromParserADT.mlength / .
Arguments SplitterFromParserADT.mis_char / .
Arguments SplitterFromParserADT.mtake / .
Arguments SplitterFromParserADT.mdrop / .
Arguments SplitterFromParserADT.mto_string / .
Arguments new_string_of_string / .
Arguments ComputationalSplitter / .
Arguments ComputationalADT.cRep / .
Arguments new_string_of_base_string / .
Arguments ComputationalADT.cConstructors / .
Local Notation hextr0 := (ex _).
Local Notation exist' x := (exist _ x _).
Local Notation hextr1 := (or_intror _).
Local Notation hextr2 := (or_introl _).

Time Definition ab_star_parser (str : String.string) : bool
  := Eval simpl in has_parse (parser ComputationalSplitter) str.

Recursive Extraction ab_star_parser.
