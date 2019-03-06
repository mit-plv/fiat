(** * Every parse tree has a corresponding minimal parse tree *)

Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties.
Require Import Fiat.Parsers.StringLike.LastChar.
Require Import Fiat.Parsers.Reachable.OnlyLast.Reachable.
Require Import Fiat.Parsers.Reachable.OnlyLast.MinimalReachable.
Require Import Fiat.Parsers.Reachable.OnlyLast.MinimalReachableOfReachable.
Require Import Fiat.Parsers.Reachable.MaybeEmpty.MinimalOfCore.
Require Import Fiat.Parsers.Reachable.MaybeEmpty.OfParse.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Common.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section cfg.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {predata : @parser_computational_predataT Char}
          {rdata' : @parser_removal_dataT' _ G predata}.

  Definition for_last_char_reachable_from_parse_of_item'
             (for_last_char_reachable_from_parse_of_productions
              : forall valid0 pats
                       (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
                       (str : String) (p : parse_of G str pats)
                       (Hforall : Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p),
                  for_last_char str (fun ch => inhabited (reachable_from_productions G ch valid0 pats)))
             {valid0 it}
             (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
             (str : String) (p : parse_of_item G str it)
             (Hforall : Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p)
  : for_last_char str (fun ch => inhabited (reachable_from_item G ch valid0 it)).
  Proof.
    destruct p as [ | nt ? p ].
    { rewrite <- for_last_char_singleton by eassumption.
      repeat constructor; assumption. }
    { specialize (for_last_char_reachable_from_parse_of_productions valid0 (G nt) Hsub str p (snd Hforall)).
      revert for_last_char_reachable_from_parse_of_productions.
      apply for_last_char_Proper; [ reflexivity | intros ? [H'] ].
      constructor.
      constructor; simpl in *; [ exact (fst Hforall) | assumption ]. }
  Defined.

  Fixpoint for_last_char_reachable_from_parse_of_productions
             {valid0 pats}
             (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
             (str : String) (p : parse_of G str pats)
             (Hforall : Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p)
             {struct p}
  : for_last_char str (fun ch => inhabited (reachable_from_productions G ch valid0 pats))
  with for_last_char_reachable_from_parse_of_production
         {valid0 pat}
         (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
         (str : String) (p : parse_of_production G str pat)
         (Hforall : Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p)
         {struct p}
       : for_last_char str (fun ch => inhabited (reachable_from_production G ch valid0 pat)).
  Proof.
    { destruct p as [ ?? p | ?? p ]; simpl in *.
      { generalize (for_last_char_reachable_from_parse_of_production valid0 _ Hsub _ p Hforall).
        apply for_last_char_Proper; [ reflexivity | intros ? [H']; constructor ].
        left; assumption. }
      { generalize (for_last_char_reachable_from_parse_of_productions valid0 _ Hsub _ p Hforall).
        apply for_last_char_Proper; [ reflexivity | intros ? [H']; constructor ].
        right; assumption. } }
    { destruct p as [ | [|n] ? p ]; simpl in *.
      { apply for_last_char_nil; assumption. }
      { rewrite <- drop_0.
        generalize (@for_last_char_reachable_from_parse_of_production valid0 _ Hsub _ _ (snd Hforall)).
          apply for_last_char_Proper; [ reflexivity | intros ? [H']; constructor ].
          right; assumption. }
      { specialize (for_last_char_reachable_from_parse_of_production _ _ Hsub _ _ (snd Hforall)).
destruct (Compare_dec.le_lt_dec (length str) (S n)) as [Hle|Hle].
        { pose proof (fun pf => parse_empty_minimal_maybe_empty_parse_of_production Hsub pf _ (snd Hforall)) as Hempty.
          rewrite drop_length in Hempty.
          specialize_by omega.
          generalize (@for_last_char_reachable_from_parse_of_item' for_last_char_reachable_from_parse_of_productions valid0 _ Hsub _ _ (fst Hforall)).
          rewrite take_long by omega.
          apply for_last_char_Proper; [ reflexivity | intros ? [H']; constructor ].
          eapply maybe_empty_production__of__minimal_maybe_empty_production in Hempty; [ | reflexivity ].
          left; assumption. }
        { revert for_last_char_reachable_from_parse_of_production.
          rewrite <- for_last_char__drop by assumption.
          apply for_last_char_Proper; [ reflexivity | intros ? [H']; constructor ].
          right; assumption. } } }
  Defined.

  Definition for_last_char_reachable_from_parse_of_item
             {valid0 it}
             (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
             (str : String) (p : parse_of_item G str it)
             (Hforall : Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p)
  : for_last_char str (fun ch => inhabited (reachable_from_item G ch valid0 it))
    := @for_last_char_reachable_from_parse_of_item' (@for_last_char_reachable_from_parse_of_productions) valid0 it Hsub str p Hforall.

  Definition for_last_char_minimal_reachable_from_parse_of_item
             {valid0 it}
             (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
             (str : String) (p : parse_of_item G str it)
             (Hforall : Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p)
  : for_last_char str (fun ch => inhabited (minimal_reachable_from_item (G := G) valid0 ch valid0 it)).
  Proof.
    setoid_rewrite <- (minimal_reachable_from_item__iff__reachable_from_item Hsub).
    eapply for_last_char_reachable_from_parse_of_item; eassumption.
  Qed.

  Definition for_last_char_minimal_reachable_from_parse_of_production
             {valid0 pat}
             (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
             (str : String) (p : parse_of_production G str pat)
             (Hforall : Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p)
  : for_last_char str (fun ch => inhabited (minimal_reachable_from_production (G := G) valid0 ch valid0 pat)).
  Proof.
    setoid_rewrite <- (minimal_reachable_from_production__iff__reachable_from_production Hsub).
    eapply for_last_char_reachable_from_parse_of_production; eassumption.
  Qed.

  Definition for_last_char_minimal_reachable_from_parse_of_productions
             {valid0 pats}
             (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
             (str : String) (p : parse_of G str pats)
             (Hforall : Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p)
  : for_last_char str (fun ch => inhabited (minimal_reachable_from_productions (G := G) valid0 ch valid0 pats)).
  Proof.
    setoid_rewrite <- (minimal_reachable_from_productions__iff__reachable_from_productions Hsub).
    eapply for_last_char_reachable_from_parse_of_productions; eassumption.
  Qed.
End cfg.
