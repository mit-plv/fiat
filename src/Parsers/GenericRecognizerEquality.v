(** * The recognizer can work on a projected string type *)
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.GenericBaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.GenericRecognizerExt.
Require Import Fiat.Common.Wf1.
Require Import Fiat.Common.SetoidInstances.
Require Import Fiat.Parsers.GenericRecognizer.

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
  Context {gendata : @generic_parser_dataT Char}.

  Class StringLikeProj :=
    { proj : @String Char HSLM_heavy -> @String Char HSLM_lite;
      length_proj : forall str, length (proj str) = length str;
      char_at_matches_proj : forall offset str ch, char_at_matches offset (proj str) ch = char_at_matches offset str ch;
      unsafe_get_proj : forall offset str, unsafe_get offset (proj str) = unsafe_get offset str;
      split_string_for_production_proj
      : forall idx str offset len,
          @split_string_for_production _ HSLM_lite _ split_data_lite idx (proj str) offset len
          = @split_string_for_production _ HSLM_heavy _ split_data idx str offset len }.

  Context {HSLPr : StringLikeProj}.
  Context (str : @String Char HSLM_heavy).

  Let data' : @boolean_parser_dataT Char HSLM_lite
    := {| BaseTypes.split_data := split_data_lite |}.
  Local Existing Instance data'.

  Lemma parse_item_proj
        str_matches_nonterminal str_matches_nonterminal'
        (H : forall nt, str_matches_nonterminal nt = str_matches_nonterminal' nt)
        (offset len : nat) (it : item _)
  : @parse_item' _ HSLM_lite _ _ (proj str) str_matches_nonterminal offset len it
    = @parse_item' _ HSLM_heavy _ _ str str_matches_nonterminal' offset len it.
  Proof.
    unfold parse_item'.
    destruct it; rewrite ?H; f_equal; try reflexivity.
    rewrite char_at_matches_proj, unsafe_get_proj; reflexivity.
  Qed.

  Lemma parse_production_proj
        (len0 : nat)
        parse_nonterminal parse_nonterminal'
        (H : forall offset len0_minus_len nt,
               parse_nonterminal offset len0_minus_len nt
               = parse_nonterminal' offset len0_minus_len nt)
        offset len0_minus_len (prod : @production_carrierT _ data)
  : @parse_production' _ HSLM_lite _ _ (proj str) len0 parse_nonterminal offset len0_minus_len prod
    = @parse_production' _ HSLM_heavy _ _ str len0 parse_nonterminal' offset len0_minus_len prod.
  Proof.
    unfold parse_production', parse_production'_for.
    simpl.
    set (ls := @to_production Char predata prod).
    generalize (eq_refl : to_production prod = ls).
    clearbody ls.
    revert prod offset len0_minus_len; induction ls; simpl; intros ??? Heq.
    { reflexivity. }
    { f_equal; [].
      rewrite split_string_for_production_proj.
      apply map_Proper_eq; trivial; [].
      intro.
      rewrite IHls.
      { f_equal; [].
        rewrite ?Heq.
        apply parse_item_proj; trivial. }
      { simpl; rewrite production_tl_correct, Heq; reflexivity. } }
  Qed.

  Lemma parse_productions_proj
        (len0 : nat)
        parse_nonterminal parse_nonterminal'
        (H : forall offset len0_minus_len nt,
               parse_nonterminal offset len0_minus_len nt
               = parse_nonterminal' offset len0_minus_len nt)
        offset len0_minus_len prods
  : @parse_productions' _ HSLM_lite _ _ (proj str) len0 parse_nonterminal offset len0_minus_len prods
    = @parse_productions' _ HSLM_heavy _ _ str len0 parse_nonterminal' offset len0_minus_len prods.
  Proof.
    unfold parse_productions'.
    f_equal; [].
    apply map_Proper_eq; trivial; [].
    intro.
    apply parse_production_proj; trivial.
  Qed.

  Lemma parse_nonterminal_step_proj
        (len0 valid_len : nat)
        parse_nonterminal parse_nonterminal'
        (H : forall p pf valid offset len pf' nt,
               parse_nonterminal p pf valid offset len pf' nt
               = parse_nonterminal' p pf valid offset len pf' nt)
        valid offset len pf nt
  : @parse_nonterminal_step _ HSLM_lite _ _ (proj str) len0 valid_len parse_nonterminal valid offset len pf nt
    = @parse_nonterminal_step _ HSLM_heavy _ _ str len0 valid_len parse_nonterminal' valid offset len pf nt.
  Proof.
    unfold parse_nonterminal_step.
    unfold sumbool_rect; simpl.
    repeat match goal with
             | [ |- context[match ?e with _ => _ end] ]
               => destruct e eqn:?
             | _ => solve [ erewrite parse_productions_proj; try reflexivity; cbv beta; trivial ]
             | _ => reflexivity
             | _ => progress simpl @option_rect
           end.
  Qed.

  Lemma parse_nonterminal_or_abort_proj
        (p : nat * nat) (valid : nonterminals_listT)
        (offset len : nat) (pf : len <= fst p) nt
  : @parse_nonterminal_or_abort _ HSLM_lite _ _ (proj str) p valid offset len pf nt
    = @parse_nonterminal_or_abort _ HSLM_heavy _ _ str p valid offset len pf nt.
  Proof.
    unfold parse_nonterminal_or_abort.
    revert valid offset len pf nt.
    match goal with
      | [ |- context[Fix ?wf _ _ ?a] ]
        => induction (wf a); intros
    end.
    rewrite !Fix5_eq by (intros; apply parse_nonterminal_step_ext; trivial).
    apply parse_nonterminal_step_proj; trivial.
  Qed.

  Lemma parse_nonterminal'_proj
        nt
  : parse_nonterminal' (proj str) nt = parse_nonterminal' str nt.
  Proof.
    unfold parse_nonterminal'.
    rewrite length_proj.
    apply parse_nonterminal_or_abort_proj.
  Qed.

  Lemma parse_nonterminal_proj
        nt
  : parse_nonterminal (proj str) nt = parse_nonterminal str nt.
  Proof.
    unfold parse_nonterminal.
    apply parse_nonterminal'_proj.
  Qed.
End transfer.
