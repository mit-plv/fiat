(** * The boolean recognizer can work on a projected string type *)
Require Import Fiat.Parsers.BooleanRecognizer.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Transfer.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BooleanRecognizerCorrect.
Require Import Fiat.Parsers.BooleanRecognizerExt.
Require Import Fiat.Common.Wf.
Require Import Fiat.Common.SetoidInstances.

Set Implicit Arguments.

Section transfer.
  Context {Char} {HSL_heavy HSL_lite : StringLike Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char HSL_heavy}.
  Context {split_data_lite : @split_dataT Char HSL_lite}.

  Class StringLikeProj :=
    { proj : @String Char HSL_heavy -> @String Char HSL_lite;
      length_proj : forall str, length (proj str) = length str;
      drop_proj : forall n str, drop n (proj str) = proj (drop n str);
      take_proj : forall n str, take n (proj str) = proj (take n str);
      is_char_proj : forall str ch, is_char (proj str) ch = is_char str ch;
      split_string_for_production_proj
      : forall it its str,
          @split_string_for_production _ HSL_lite split_data_lite it its (proj str)
          = @split_string_for_production _ HSL_heavy data it its str }.

  Context {HSLPr : StringLikeProj}.

  Local Instance data' : @boolean_parser_dataT Char HSL_lite
    := { predata := predata;
         split_data := split_data_lite }.

  Lemma parse_item_proj
        str_matches_nonterminal str_matches_nonterminal'
        (H : forall nt, str_matches_nonterminal nt = str_matches_nonterminal' nt)
        str it
  : @parse_item' _ HSL_lite _ str_matches_nonterminal (proj str) it
    = @parse_item' _ HSL_heavy _ str_matches_nonterminal' str it.
  Proof.
    unfold parse_item'.
    destruct it.
    { apply is_char_proj. }
    { trivial. }
  Qed.

  Lemma parse_production_proj
        (len0 : nat)
        parse_nonterminal parse_nonterminal'
        (H : forall str len pf' nt,
               parse_nonterminal (proj str) len pf' nt
               = parse_nonterminal' str len pf' nt)
        str len pf prod
  : @parse_production' _ HSL_lite _ len0 parse_nonterminal (proj str) len pf prod
    = @parse_production' _ HSL_heavy _ len0 parse_nonterminal' str len pf prod.
  Proof.
    revert len str pf; induction prod; simpl; intros.
    { reflexivity. }
    { f_equal; [].
      rewrite split_string_for_production_proj.
      apply map_Proper_eq; trivial; [].
      intro.
      rewrite take_proj, drop_proj, IHprod.
      f_equal; [].
      apply parse_item_proj; trivial. }
  Qed.

  Lemma parse_productions_proj
        (len0 : nat)
        parse_nonterminal parse_nonterminal'
        (H : forall str len pf' nt,
               parse_nonterminal (proj str) len pf' nt
               = parse_nonterminal' str len pf' nt)
        str len pf prods
  : @parse_productions' _ HSL_lite _ len0 parse_nonterminal (proj str) len pf prods
    = @parse_productions' _ HSL_heavy _ len0 parse_nonterminal' str len pf prods.
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
        (H : forall p pf valid str len pf' nt,
               parse_nonterminal p pf valid (proj str) len pf' nt
               = parse_nonterminal' p pf valid str len pf' nt)
        valid str len pf nt
  : @parse_nonterminal_step _ HSL_lite G _ len0 valid_len parse_nonterminal valid (proj str) len pf nt
    = @parse_nonterminal_step _ HSL_heavy G _ len0 valid_len parse_nonterminal' valid str len pf nt.
  Proof.
    unfold parse_nonterminal_step.
    unfold sumbool_rect; simpl.
    repeat match goal with
             | [ |- appcontext[match ?e with _ => _ end] ]
               => destruct e eqn:?
             | _ => solve [ apply parse_productions_proj; trivial ]
             | _ => reflexivity
           end.
  Qed.

  Lemma parse_nonterminal_or_abort_proj
        (p : nat * nat) (valid : nonterminals_listT)
        (str : @String Char HSL_heavy) (len : nat) (pf : len <= fst p) nt
  : @parse_nonterminal_or_abort _ HSL_lite G _ p valid (proj str) len pf nt
    = @parse_nonterminal_or_abort _ HSL_heavy G _ p valid str len pf nt.
  Proof.
    unfold parse_nonterminal_or_abort.
    revert valid str len pf nt.
    match goal with
      | [ |- appcontext[Fix ?wf _ _ ?a] ]
        => induction (wf a); intros
    end.
    rewrite !Fix5_eq by (intros; apply parse_nonterminal_step_ext; trivial).
    apply parse_nonterminal_step_proj; trivial.
  Qed.

  Lemma parse_nonterminal'_proj
        (str : @String Char HSL_heavy) nt
  : parse_nonterminal' (G := G) (proj str) nt = parse_nonterminal' (G := G) str nt.
  Proof.
    unfold parse_nonterminal'.
    rewrite length_proj.
    apply parse_nonterminal_or_abort_proj.
  Qed.

  Lemma parse_nonterminal_proj
        (str : @String Char HSL_heavy) nt
  : parse_nonterminal (G := G) (proj str) nt = parse_nonterminal (G := G) str nt.
  Proof.
    unfold parse_nonterminal.
    apply parse_nonterminal'_proj.
  Qed.
End transfer.
