(** * The boolean recognizer can work on a projected string type *)
Require Import Fiat.Parsers.GenericRecognizerEquality.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BooleanRecognizer.

Set Implicit Arguments.

Section transfer.
  Context {Char} {HSLM_heavy HSLM_lite : StringLikeMin Char} {G : grammar Char}.
  Context {predata : @parser_computational_predataT Char}.
  Context {split_data : @split_dataT Char HSLM_heavy _}.
  Context {split_data_lite : @split_dataT Char HSLM_lite _}.
  Context {rdata : @parser_removal_dataT' Char G predata}.
  Let data : @boolean_parser_dataT Char HSLM_heavy
    := {| BaseTypes.split_data := split_data |}.
  Local Existing Instance data.
  Context {HSLPr : @StringLikeProj _ HSLM_heavy HSLM_lite _ _ _}.
  Context (str : @String Char HSLM_heavy).

  Let data' : @boolean_parser_dataT Char HSLM_lite
    := {| BaseTypes.split_data := split_data_lite |}.
  Local Existing Instance data'.
  Local Existing Instance boolean_gendata.

  Lemma parse_item_proj
        str_matches_nonterminal str_matches_nonterminal'
        (H : forall nt, str_matches_nonterminal nt = str_matches_nonterminal' nt)
        (offset len : nat) (it : item _)
  : @parse_item' _ HSLM_lite _ (proj str) str_matches_nonterminal offset len it
    = @parse_item' _ HSLM_heavy _ str str_matches_nonterminal' offset len it.
  Proof.
    refine (parse_item_proj _ _ _ _ _ _ _); assumption.
  Qed.

  Lemma parse_production_proj
        (len0 : nat)
        parse_nonterminal parse_nonterminal'
        (H : forall offset len0_minus_len nt,
               parse_nonterminal offset len0_minus_len nt
               = parse_nonterminal' offset len0_minus_len nt)
        offset len0_minus_len (prod : @production_carrierT _ data)
  : @parse_production' _ HSLM_lite _ (proj str) len0 parse_nonterminal offset len0_minus_len prod
    = @parse_production' _ HSLM_heavy _ str len0 parse_nonterminal' offset len0_minus_len prod.
  Proof.
    refine (parse_production_proj _ _ _ _ _ _ _ _); assumption.
  Qed.

  Lemma parse_productions_proj
        (len0 : nat)
        parse_nonterminal parse_nonterminal'
        (H : forall offset len0_minus_len nt,
               parse_nonterminal offset len0_minus_len nt
               = parse_nonterminal' offset len0_minus_len nt)
        offset len0_minus_len prods
  : @parse_productions' _ HSLM_lite _ (proj str) len0 parse_nonterminal offset len0_minus_len prods
    = @parse_productions' _ HSLM_heavy _ str len0 parse_nonterminal' offset len0_minus_len prods.
  Proof.
    refine (parse_productions_proj _ _ _ _ _ _ _ _); assumption.
  Qed.

  Lemma parse_nonterminal_step_proj
        (len0 valid_len : nat)
        parse_nonterminal parse_nonterminal'
        (H : forall p pf valid offset len pf' nt,
               parse_nonterminal p pf valid offset len pf' nt
               = parse_nonterminal' p pf valid offset len pf' nt)
        valid offset len pf nt
  : @parse_nonterminal_step _ HSLM_lite _ (proj str) len0 valid_len parse_nonterminal valid offset len pf nt
    = @parse_nonterminal_step _ HSLM_heavy _ str len0 valid_len parse_nonterminal' valid offset len pf nt.
  Proof.
    refine (parse_nonterminal_step_proj _ _ _ _ _ _ _ _); assumption.
  Qed.

  Lemma parse_nonterminal_or_abort_proj
        (p : nat * nat) (valid : nonterminals_listT)
        (offset len : nat) (pf : len <= fst p) nt
  : @parse_nonterminal_or_abort _ HSLM_lite _ (proj str) p valid offset len pf nt
    = @parse_nonterminal_or_abort _ HSLM_heavy _ str p valid offset len pf nt.
  Proof.
    refine (parse_nonterminal_or_abort_proj _ _ _ _ _ _); assumption.
  Qed.

  Lemma parse_nonterminal'_proj
        (nt : @nonterminal_carrierT Char predata)
  : parse_nonterminal' (proj str) nt = parse_nonterminal' str nt.
  Proof.
    refine (parse_nonterminal'_proj _ _); assumption.
  Qed.

  Lemma parse_nonterminal_proj
        nt
  : parse_nonterminal (proj str) nt = parse_nonterminal str nt.
  Proof.
    refine (parse_nonterminal_proj _ _); assumption.
  Qed.
End transfer.
