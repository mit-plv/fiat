(** * Every parse tree has a corresponding minimal parse tree *)

Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.Reachable.MaybeEmpty.Core.
Require Import Fiat.Parsers.Reachable.MaybeEmpty.Minimal.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Reachable.MaybeEmpty.MinimalOfCore.
Require Import Fiat.Common.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section cfg.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {predata : @parser_computational_predataT Char}
          {rdata' : @parser_removal_dataT' _ G predata}.

  Definition parse_empty_maybe_empty_parse_of_item'
             (parse_empty_maybe_empty_parse_of_productions
              : forall valid0 pats
                       (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
                       (str : String) (Hlen : length str = 0) (p : parse_of G str pats)
                       (Hforall : Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p),
                  maybe_empty_productions G valid0 pats)
             {valid0 it}
             (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
             (str : String) (Hlen : length str = 0) (p : parse_of_item G str it)
             (Hforall : Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p)
  : maybe_empty_item G valid0 it.
  Proof.
    destruct p as [ | nt ? p ].
    { exfalso.
      erewrite length_singleton in Hlen by eassumption; omega. }
    { specialize (parse_empty_maybe_empty_parse_of_productions valid0 (G nt) Hsub str Hlen p (snd Hforall)).
      constructor; simpl in *; [ exact (fst Hforall) | assumption ]. }
  Defined.

  Fixpoint parse_empty_maybe_empty_parse_of_productions
             {valid0 pats}
             (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
             (str : String) (Hlen : length str = 0) (p : parse_of G str pats)
             (Hforall : Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p)
             {struct p}
  : maybe_empty_productions G valid0 pats
  with parse_empty_maybe_empty_parse_of_production
         {valid0 pat}
         (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
         (str : String) (Hlen : length str = 0) (p : parse_of_production G str pat)
         (Hforall : Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p)
         {struct p}
       : maybe_empty_production G valid0 pat.
  Proof.
    { destruct p as [ ?? p | ?? p ]; simpl in *.
      { pose proof (parse_empty_maybe_empty_parse_of_production valid0 _ Hsub _ Hlen p Hforall).
        left; assumption. }
      { pose proof (parse_empty_maybe_empty_parse_of_productions valid0 _ Hsub _ Hlen p Hforall).
        right; assumption. } }
    { destruct p as [ | ?? p ]; simpl in *.
      { constructor. }
      { constructor.
        { apply (fun k => @parse_empty_maybe_empty_parse_of_item' parse_empty_maybe_empty_parse_of_productions valid0 _ Hsub _ k _ (fst Hforall)).
          rewrite take_length, Hlen, Min.min_0_r; reflexivity. }
        { apply (fun k => @parse_empty_maybe_empty_parse_of_production valid0 _ Hsub _ k _ (snd Hforall)).
          rewrite drop_length, Hlen; reflexivity. } } }
  Defined.

  Definition parse_empty_maybe_empty_parse_of_item
             {valid0 it}
             (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
             (str : String) (Hlen : length str = 0) (p : parse_of_item G str it)
             (Hforall : Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p)
  : maybe_empty_item G valid0 it
    := @parse_empty_maybe_empty_parse_of_item' (@parse_empty_maybe_empty_parse_of_productions) valid0 it Hsub str Hlen p Hforall.

  Definition parse_empty_minimal_maybe_empty_parse_of_item
             {valid0 it}
             (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
             (str : String) (Hlen : length str = 0) (p : parse_of_item G str it)
             (Hforall : Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p)
  : minimal_maybe_empty_item (G := G) valid0 it.
  Proof.
    eapply minimal_maybe_empty_item__of__maybe_empty_item; try assumption.
    eapply parse_empty_maybe_empty_parse_of_item; eassumption.
  Qed.

  Definition parse_empty_minimal_maybe_empty_parse_of_production
             {valid0 pat}
             (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
             (str : String) (Hlen : length str = 0) (p : parse_of_production G str pat)
             (Hforall : Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p)
  : minimal_maybe_empty_production (G := G) valid0 pat.
  Proof.
    eapply minimal_maybe_empty_production__of__maybe_empty_production; try assumption.
    eapply parse_empty_maybe_empty_parse_of_production; eassumption.
  Qed.

  Definition parse_empty_minimal_maybe_empty_parse_of_productions
             {valid0 pats}
             (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
             (str : String) (Hlen : length str = 0) (p : parse_of G str pats)
             (Hforall : Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p)
  : minimal_maybe_empty_productions (G := G) valid0 pats.
  Proof.
    eapply minimal_maybe_empty_productions__of__maybe_empty_productions; try assumption.
    eapply parse_empty_maybe_empty_parse_of_productions; eassumption.
  Qed.

  Definition parse_empty_from_maybe_empty_parse_of_item'
             (parse_empty_from_maybe_empty_parse_of_productions
              : forall valid0 pats
                       (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
                       (str : String) (Hlen : length str = 0),
                  maybe_empty_productions G valid0 pats
                  -> { p : parse_of G str pats
                           & Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p })
             {valid0 it}
             (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
             (str : String) (Hlen : length str = 0)
             (p : maybe_empty_item G valid0 it)
  : { p : parse_of_item G str it
          & Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p }.
  Proof.
    destruct p as [ nt H p ].
    eapply parse_empty_from_maybe_empty_parse_of_productions in p; [ | eassumption.. ].
    eexists (ParseNonTerminal _ _ (projT1 p)).
    exact (H, projT2 p).
    Grab Existential Variables.
    apply initial_nonterminals_correct, Hsub; assumption.
  Defined.

  Fixpoint parse_empty_from_maybe_empty_parse_of_productions
             {valid0 pats}
             (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
             (str : String) (Hlen : length str = 0)
             (p : maybe_empty_productions G valid0 pats)
             {struct p}
  : { p : parse_of G str pats
          & Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p }
  with parse_empty_from_maybe_empty_parse_of_production
         {valid0 pat}
         (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
         (str : String) (Hlen : length str = 0)
         (p: maybe_empty_production G valid0 pat)
         {struct p}
       : { p : parse_of_production G str pat
               & Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p }.
  Proof.
    { destruct p as [ ?? p | ?? p ]; simpl in *.
      { pose proof (parse_empty_from_maybe_empty_parse_of_production valid0 _ Hsub _ Hlen p) as p'.
        eexists (ParseHead _ (projT1 p')).
        exact (projT2 p'). }
      { pose proof (parse_empty_from_maybe_empty_parse_of_productions valid0 _ Hsub _ Hlen p) as p'.
        eexists (ParseTail _ (projT1 p')).
        exact (projT2 p'). } }
    { destruct p as [ | ?? p0 p1 ]; simpl in *.
      { exists (ParseProductionNil G _ Hlen). constructor. }
      { eapply (@parse_empty_from_maybe_empty_parse_of_item' parse_empty_from_maybe_empty_parse_of_productions) in p0; try assumption.
        eapply (@parse_empty_from_maybe_empty_parse_of_production) in p1; try assumption.
        { eexists (ParseProductionCons _ 0 (projT1 p0) (projT1 p1)).
          exact (projT2 p0, projT2 p1). }
        { rewrite ?take_length, ?drop_length, Hlen; reflexivity. }
        { rewrite ?take_length, ?drop_length, Hlen, Min.min_0_r; reflexivity. } } }
  Defined.

  Definition parse_empty_from_maybe_empty_parse_of_item
             {valid0 it}
             (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
             (str : String) (Hlen : length str = 0)
             (p : maybe_empty_item G valid0 it)
  : { p : parse_of_item G str it
          & Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p }
    := @parse_empty_from_maybe_empty_parse_of_item' (@parse_empty_from_maybe_empty_parse_of_productions) valid0 it Hsub str Hlen p.

  Definition parse_empty_from_minimal_maybe_empty_parse_of_item
             {valid0 it}
             (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
             (str : String) (Hlen : length str = 0)
             (p : minimal_maybe_empty_item (G := G) valid0 it)
  : { p : parse_of_item G str it
          & Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p }.
  Proof.
    eapply parse_empty_from_maybe_empty_parse_of_item; trivial.
    eapply maybe_empty_item__of__minimal_maybe_empty_item; try eassumption; reflexivity.
  Qed.

  Definition parse_empty_from_minimal_maybe_empty_parse_of_production
             {valid0 pat}
             (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
             (str : String) (Hlen : length str = 0)
             (p : minimal_maybe_empty_production (G := G) valid0 pat)
  : { p : parse_of_production G str pat
          & Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p }.
  Proof.
    eapply parse_empty_from_maybe_empty_parse_of_production; trivial.
    eapply maybe_empty_production__of__minimal_maybe_empty_production; try eassumption; reflexivity.
  Qed.

  Definition parse_empty_from_minimal_maybe_empty_parse_of_productions
             {valid0 pats}
             (Hsub : sub_nonterminals_listT valid0 initial_nonterminals_data)
             (str : String) (Hlen : length str = 0)
             (p : minimal_maybe_empty_productions (G := G) valid0 pats)
  : { p : parse_of G str pats
          & Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p }.
  Proof.
    eapply parse_empty_from_maybe_empty_parse_of_productions; trivial.
    eapply maybe_empty_productions__of__minimal_maybe_empty_productions; try eassumption; reflexivity.
  Qed.
End cfg.
