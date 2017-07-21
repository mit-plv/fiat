(** Sharpened ADT for an expression grammar with parentheses *)
Require Import Coq.Init.Wf Coq.Arith.Wf_nat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Equality.
Require Import Coq.Program.Equality.
Require Import Coq.MSets.MSetPositive.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.Wf.
Require Import Fiat.Common.Enumerable.
Require Import Fiat.Common.LogicFacts.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.Splitters.BruteForce.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.BooleanRecognizerFull.
Require Import Fiat.Parsers.BooleanRecognizerCorrect.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.ForallChars.
Require Import Fiat.Parsers.StringLike.FirstChar.
Require Import Fiat.Parsers.StringLike.FirstCharSuchThat.
Require Import Fiat.Parsers.StringLike.LastChar.
Require Import Fiat.Parsers.StringLike.LastCharSuchThat.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.MinimalParseOfParse.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties.
Require Import Fiat.Parsers.ContextFreeGrammar.Fold.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidProperties.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.Refinement.DisjointLemmasEarlyDeclarations.
Require Import Fiat.Parsers.Refinement.PossibleTerminalsSets.
Require Import Fiat.Common.BoolFacts.
Require Fiat.Parsers.Reachable.All.MinimalReachable.
Require Fiat.Parsers.Reachable.All.MinimalReachableOfReachable.
Require Fiat.Parsers.Reachable.All.ReachableParse.
Require Fiat.Parsers.Reachable.OnlyFirst.MinimalReachable.
Require Fiat.Parsers.Reachable.OnlyFirst.MinimalReachableOfReachable.
Require Fiat.Parsers.Reachable.OnlyFirst.ReachableParse.
Require Fiat.Parsers.Reachable.OnlyLast.MinimalReachable.
Require Fiat.Parsers.Reachable.OnlyLast.MinimalReachableOfReachable.
Require Fiat.Parsers.Reachable.OnlyLast.ReachableParse.
Require Fiat.Parsers.Reachable.MaybeEmpty.Core.
Require Fiat.Parsers.Reachable.MaybeEmpty.MinimalOfCore.
Require Fiat.Parsers.Reachable.MaybeEmpty.OfParse.

Set Implicit Arguments.

Local Open Scope string_like_scope.

Local Arguments string_beq : simpl never.

Section search_forward.
  Context {G : pregrammar' Ascii.ascii}
          {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSI : StringIso Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          {HSIP : StringIsoProperties Ascii.ascii}
          (pdata : possible_data G).

  Local Notation possible_terminals_of nt
    := (@all_possible_ascii_of_nt G pdata nt).
  Local Notation possible_first_terminals_of_production its
    := (@possible_first_ascii_of_production G pdata its).
  Local Notation might_be_empty_of_production its
    := (@might_be_empty_of_pr_production G pdata its).

  Lemma terminals_disjoint_search_for_not'
        (str : @String Ascii.ascii HSLM)
        {nt its}
        (H_disjoint : disjoint ascii_beq
                               (possible_terminals_of nt)
                               (possible_first_terminals_of_production its))
        {n}
        (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
        (pits : parse_of_production G (StringLike.drop n str) its)
        (H_reachable : production_is_reachable G (NonTerminal nt :: its))
  : forall_chars__char_in (take n str) (possible_terminals_of nt)
    /\ ((length str <= n /\ might_be_empty_of_production its)
        \/ (for_first_char
              (drop n str)
              (fun ch => negb (list_bin ascii_beq ch (possible_terminals_of nt)))
            /\ n < length str)).
  Proof.
    destruct H_reachable as [ nt' [ prefix [ HinV HinL ] ] ].
    pose proof HinV as HinV';
      rewrite <- (@initial_nonterminals_correct _ G (@rdp_list_predata _ G) (@rdp_list_rdata' _ G)) in HinV'.
    apply and_comm; split.
    { destruct (Compare_dec.le_dec (length str) n); [ left | right ].
      { split; trivial.
        pose proof (drop_length str n) as H.
        rewrite (proj2 (Nat.sub_0_le (length str) n)) in H by assumption.
        generalize dependent (drop n str); clear -pit HinV' HinL HSLP HSIP.
        intros.
        eapply might_be_empty_pr_parse_of_production; eassumption. }
      { split; try omega; [].
        eapply first_char_in__impl__for_first_char;
          [
          | apply possible_first_ascii_parse_of_production; eassumption ].
        intros ch H'.
        apply Bool.negb_true_iff, Bool.not_true_iff_false.
        intro H''.
        apply list_in_bl in H''; [ | apply (@ascii_bl) ].
        eapply fold_right_andb_map_in in H_disjoint; [ | eassumption ].
        apply Bool.negb_true_iff, Bool.not_true_iff_false in H_disjoint.
        apply H_disjoint.
        apply list_in_lb; [ apply (@ascii_lb) | assumption ]. } }
    { apply (all_possible_ascii_of_item_nt pit). }
  Qed.

  Lemma terminals_disjoint_search_for_not
        (str : @String Ascii.ascii HSLM)
        {nt its}
        (H_disjoint : disjoint ascii_beq (possible_terminals_of nt) (possible_first_terminals_of_production its))
        {n}
        (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
        (pits : parse_of_production G (StringLike.drop n str) its)
        (H_reachable : production_is_reachable G (NonTerminal nt :: its))
    : is_first_char_such_that
        (might_be_empty_of_production its)
        str
        n
        (fun ch => negb (list_bin ascii_beq ch (possible_terminals_of nt))).
  Proof.
    pose proof (terminals_disjoint_search_for_not' _ H_disjoint pit pits H_reachable) as H.
    split;
      [ destruct H as [H0 H1]
      | destruct H as [H0 [[H1 H2] | H1]]; solve [ left; eauto | right; eauto ] ].
    revert H0.
    apply forall_chars__char_in__impl__forall_chars.
    intros ch H' H''.
    apply Bool.negb_true_iff, Bool.not_true_iff_false in H''.
    apply H''.
    apply list_in_lb; [ apply (@ascii_lb) | ]; assumption.
  Qed.

  Lemma terminals_disjoint_search_for'
        (str : @String Ascii.ascii HSLM)
        {nt its}
        (H_disjoint : disjoint ascii_beq (possible_terminals_of nt) (possible_first_terminals_of_production its))
        {n}
        (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
        (pits : parse_of_production G (StringLike.drop n str) its)
        (H_reachable : production_is_reachable G (NonTerminal nt :: its))
    : forall_chars (take n str)
                   (fun ch => negb (list_bin ascii_beq ch (possible_first_terminals_of_production its)))
      /\ ((length str <= n /\ might_be_empty_of_production its)
          \/ (first_char_in
                (drop n str)
                (possible_first_terminals_of_production its)
              /\ n < length str)).
  Proof.
    destruct H_reachable as [ nt' [ prefix [ HinV HinL ] ] ].
    pose proof HinV as HinV';
      rewrite <- (@initial_nonterminals_correct _ G (@rdp_list_predata _ G) (@rdp_list_rdata' _ G)) in HinV'.
    apply and_comm; split.
    { destruct (Compare_dec.le_dec (length str) n); [ left | right ].
      { split; trivial.
        pose proof (drop_length str n) as H.
        rewrite (proj2 (Nat.sub_0_le (length str) n)) in H by assumption.
        generalize dependent (drop n str); clear -pit HinV' HinL HSLP HSIP.
        intros.
        eapply might_be_empty_pr_parse_of_production; eassumption. }
      { split; try omega; try assumption.
        apply possible_first_ascii_parse_of_production; assumption. } }
    { eapply forall_chars__char_in__impl__forall_chars.
      { intros ch H'.
        apply Bool.negb_true_iff, Bool.not_true_iff_false.
        intro H''.
        apply list_in_bl in H''; [ | apply (@ascii_bl) ].
        eapply fold_right_andb_map_in in H_disjoint; [ | eassumption ].
        apply Bool.negb_true_iff, Bool.not_true_iff_false in H_disjoint.
        apply H_disjoint.
        apply list_in_lb; [ apply (@ascii_lb) | assumption ]. }
      { apply all_possible_ascii_of_item_nt; assumption. } }
  Qed.

  Lemma terminals_disjoint_search_for
        (str : @String Ascii.ascii HSLM)
        {nt its}
        (H_disjoint : disjoint ascii_beq (possible_terminals_of nt) (possible_first_terminals_of_production its))
        {n}
        (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
        (pits : parse_of_production G (StringLike.drop n str) its)
        (H_reachable : production_is_reachable G (NonTerminal nt :: its))
    : is_first_char_such_that
        (might_be_empty_of_production its)
        str
        n
        (fun ch => list_bin ascii_beq ch (possible_first_terminals_of_production its)).
  Proof.
    pose proof (terminals_disjoint_search_for' _ H_disjoint pit pits H_reachable) as H.
    split;
      [ destruct H as [H0 H1]
      | destruct H as [H0 [[H1 H2] | [H1 ?]]]; [ right | left; split ]; eauto ].
    { revert H0.
      apply forall_chars_Proper; [ reflexivity | ].
      intros ch H' H''.
      apply Bool.negb_true_iff, Bool.not_true_iff_false in H'.
      apply H'.
      assumption. }
    { revert H1.
      apply first_char_in__impl__for_first_char.
      intros ch H'.
      apply list_in_lb; [ apply (@ascii_lb) | ]; assumption. }
  Qed.
End search_forward.

Section search_backward.
  Context {G : pregrammar' Ascii.ascii}
          {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSI : StringIso Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          {HSIP : StringIsoProperties Ascii.ascii}
          (pdata : possible_data G).

  Local Notation possible_terminals_of_production its
    := (@all_possible_ascii_of_production G pdata its).
  Local Notation possible_last_terminals_of nt
    := (@possible_last_ascii_of_nt G pdata nt).
  Local Notation might_be_empty_of nt
    := (@might_be_empty_of_pr_nt G pdata nt).

  Lemma terminals_disjoint_rev_search_for_not'
        (str : @String Ascii.ascii HSLM)
        {nt its}
        (H_disjoint : disjoint ascii_beq (possible_last_terminals_of nt) (possible_terminals_of_production its))
        {n}
        (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
        (pits : parse_of_production G (StringLike.drop n str) its)
        (H_reachable : production_is_reachable G (NonTerminal nt :: its))
  : forall_chars__char_in (drop n str) (possible_terminals_of_production its)
    /\ ((n = 0 /\ might_be_empty_of nt)
        \/ (for_last_char
              (take n str)
              (fun ch => negb (list_bin ascii_beq ch (possible_terminals_of_production its)))
            /\ n > 0)).
  Proof.
    destruct H_reachable as [ nt' [ prefix [ HinV HinL ] ] ].
    pose proof HinV as HinV';
      rewrite <- (@initial_nonterminals_correct _ G (@rdp_list_predata _ G) (@rdp_list_rdata' _ G)) in HinV'.
    apply and_comm; split.
    { destruct (Compare_dec.zerop n); [ left | right ].
      { split; trivial; []; subst.
        eapply might_be_empty_pr_parse_of_item_nt; try eassumption.
        rewrite take_length; reflexivity. }
      { split; try omega; [].
        eapply last_char_in__impl__for_last_char;
          [
          | apply possible_last_ascii_parse_of_item_nt; eassumption ].
        intros ch H'.
        apply Bool.negb_true_iff, Bool.not_true_iff_false.
        intro H''.
        apply list_in_bl in H''; [ | apply (@ascii_bl) ].
        eapply fold_right_andb_map_in in H_disjoint; [ | eassumption ].
        apply Bool.negb_true_iff, Bool.not_true_iff_false in H_disjoint.
        apply H_disjoint.
        apply list_in_lb; [ apply (@ascii_lb) | assumption ]. } }
    { apply all_possible_ascii_of_parse_of_production; assumption. }
  Qed.

  Lemma terminals_disjoint_rev_search_for_not
        (str : @String Ascii.ascii HSLM)
        {nt its}
        (H_disjoint : disjoint ascii_beq (possible_last_terminals_of nt) (possible_terminals_of_production its))
        {n}
        (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
        (pits : parse_of_production G (StringLike.drop n str) its)
        (H_reachable : production_is_reachable G (NonTerminal nt :: its))
    : is_after_last_char_such_that
        str
        n
        (fun ch => negb (list_bin ascii_beq ch (possible_terminals_of_production its))).
  Proof.
    pose proof (terminals_disjoint_rev_search_for_not' _ H_disjoint pit pits H_reachable) as H.
    split;
      [ destruct H as [H0 H1]
      | destruct H as [H0 [[H1 H2] | H1]];
        destruct_head and;
        try solve [ left; eauto
                  | right; eauto
                  | assumption
                  | apply for_last_char_nil; rewrite ?take_length; apply Min.min_case_strong; omega ] ].
    revert H0.
    apply forall_chars__char_in__impl__forall_chars.
    intros ch H' H''.
    apply Bool.negb_true_iff, Bool.not_true_iff_false in H''.
    apply H''; clear H''.
    apply list_in_lb; [ apply (@ascii_lb) | ]; assumption.
  Qed.

  Lemma terminals_disjoint_rev_search_for'
        (str : @String Ascii.ascii HSLM)
        {nt its}
        (H_disjoint : disjoint ascii_beq (possible_last_terminals_of nt) (possible_terminals_of_production its))
        {n}
        (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
        (pits : parse_of_production G (StringLike.drop n str) its)
        (H_reachable : production_is_reachable G (NonTerminal nt :: its))
    : forall_chars (drop n str)
                   (fun ch => negb (list_bin ascii_beq ch (possible_last_terminals_of nt)))
      /\ ((n = 0 /\ might_be_empty_of nt)
          \/ (last_char_in
                (take n str)
                (possible_last_terminals_of nt)
              /\ n > 0)).
  Proof.
    destruct H_reachable as [ nt' [ prefix [ HinV HinL ] ] ].
    pose proof HinV as HinV';
      rewrite <- (@initial_nonterminals_correct _ G (@rdp_list_predata _ G) (@rdp_list_rdata' _ G)) in HinV'.
    apply and_comm; split.
    { destruct (Compare_dec.zerop n); [ left | right ].
      { split; trivial; [].
        eapply might_be_empty_pr_parse_of_item_nt; try eassumption.
        rewrite take_length; subst; reflexivity. }
      { split; try omega; try assumption; [].
        apply possible_last_ascii_parse_of_item_nt; assumption. } }
    { eapply forall_chars__char_in__impl__forall_chars.
      { intros ch H'.
        apply Bool.negb_true_iff, Bool.not_true_iff_false.
        intro H''.
        apply list_in_bl in H''; [ | apply (@ascii_bl) ].
        eapply fold_right_andb_map_in in H_disjoint; [ | eassumption ].
        apply Bool.negb_true_iff, Bool.not_true_iff_false in H_disjoint.
        apply H_disjoint.
        apply list_in_lb; [ apply (@ascii_lb) | eassumption ]. }
      { apply all_possible_ascii_of_parse_of_production; assumption. } }
  Qed.

  Lemma terminals_disjoint_rev_search_for
        (str : @String Ascii.ascii HSLM)
        {nt its}
        (H_disjoint : disjoint ascii_beq (possible_last_terminals_of nt) (possible_terminals_of_production its))
        {n}
        (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
        (pits : parse_of_production G (StringLike.drop n str) its)
        (H_reachable : production_is_reachable G (NonTerminal nt :: its))
    : is_after_last_char_such_that
        str
        n
        (fun ch => list_bin ascii_beq ch (possible_last_terminals_of nt)).
  Proof.
    pose proof (terminals_disjoint_rev_search_for' _ H_disjoint pit pits H_reachable) as H.
    split;
      [ destruct H as [H0 H1]
      | destruct H as [H0 [[H1 H2] | [H1 ?]]];
        try solve [ right; eauto
                  | left; split; eauto
                  | assumption
                  | apply for_last_char_nil; rewrite ?take_length; apply Min.min_case_strong; omega ] ].
    { revert H0.
      apply forall_chars_Proper; [ reflexivity | ].
      intros ch H' H''.
      apply Bool.negb_true_iff, Bool.not_true_iff_false in H'.
      apply H'.
      assumption. }
    { revert H1.
      apply last_char_in__impl__for_last_char.
      intros ch H'.
      apply list_in_lb; [ apply (@ascii_lb) | ]; assumption. }
  Qed.
End search_backward.

Ltac get_grammar :=
  lazymatch goal with
  | [ |- context[ParserInterface.split_list_is_complete_idx ?G] ] => G
  end.

(*Ltac pose_rvalid_for G :=
  lazymatch goal with
  | [ H : is_true (grammar_rvalid G) |- _ ] => idtac
  | _ => let Hvalid := fresh "Hvalid" in
         assert (Hvalid : is_true (grammar_rvalid G))
           by (vm_compute; reflexivity)
  end.
Ltac pose_rvalid := let G := get_grammar in pose_rvalid_for G.*)

Module Export Exports.
  Export DisjointLemmasEarlyDeclarations.
  (** hide the arguments to Build_disjoint_search_data *)
  Local Arguments FromAbstractInterpretation.Build_fold_grammar_data' {_ _ _ _ _} _ _ : assert.
  Notation precomputed_search_data
    := (FromAbstractInterpretation.Build_fold_grammar_data' _ _).

  Ltac do_disjoint_precomputations _ ::=
    let G := get_grammar in
    lazymatch goal with
    | [ |- context[@ParserInterface.split_list_is_complete_idx _ G ?HSLM ?HSL] ]
      => pose (_ : @StringLikeProperties _ HSLM HSL)
    end;
    pose_possible_data_for G.
End Exports.
