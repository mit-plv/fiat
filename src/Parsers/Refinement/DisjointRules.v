(** Refinement rules for disjoint rules *)
Require Import Coq.Lists.List.
Require Import Fiat.Parsers.Refinement.PreTactics.
Require Import Fiat.Computation.Refinements.General.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.StringLike.FirstCharSuchThat.
Require Import Fiat.Parsers.StringLike.FirstChar.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.Refinement.DisjointLemmas.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.StringLike.Core.

Set Implicit Arguments.

Definition search_for_condition
           {HSL : StringLike Ascii.ascii}
           {HSI : StringIso Ascii.ascii}
           (G : grammar Ascii.ascii)
           str its (n : nat)
  := is_first_char_such_that
       (might_be_empty (possible_first_terminals_of_production G its))
       str
       n
       (fun ch => list_bin ascii_beq ch (possible_first_terminals_of_production G its)).

Lemma refine_disjoint_search_for'
      {HSL : StringLike Ascii.ascii}
      {HSI : StringIso Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {HSIP : StringIsoProperties Ascii.ascii}
      (G : grammar Ascii.ascii)
      (Hvalid : grammar_rvalid G)
      {str nt its}
      (H_disjoint : disjoint ascii_beq
                             (possible_terminals_of G nt)
                             (possible_first_terminals_of_production G its))
: refine {splits : list nat
         | split_list_is_complete
             G str
             (NonTerminal nt)
             its splits}
         (n <- { n : nat | n <= length str
                           /\ ((exists n', search_for_condition G str its n')
                               -> search_for_condition G str its n) };
          ret [n]).
Proof.
  intros ls H.
  computes_to_inv; subst.
  destruct H as [H0 H1].
  apply PickComputes.
  intros n ? H_reachable pit pits.
  left.
  pose proof (terminals_disjoint_search_for Hvalid _ H_disjoint pit pits H_reachable) as H'.
  specialize (H1 (ex_intro _ n H')).
  pose proof (is_first_char_such_that_eq_nat_iff H1 H') as H''.
  destruct_head or; destruct_head and; subst;
  rewrite ?Min.min_r by assumption;
  omega.
Qed.

Definition search_for_not_condition
           {HSL : StringLike Ascii.ascii}
           {HSI : StringIso Ascii.ascii}
           (G : grammar Ascii.ascii)
           str nt its n
  := is_first_char_such_that
       (might_be_empty (possible_first_terminals_of_production G its))
       str
       n
       (fun ch => negb (list_bin ascii_beq ch (possible_terminals_of G nt))).

Lemma refine_disjoint_search_for_not'
      {HSL : StringLike Ascii.ascii}
      {HSI : StringIso Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {HSIP : StringIsoProperties Ascii.ascii}
      {G : grammar Ascii.ascii}
      (Hvalid : grammar_rvalid G)
      {str nt its}
      (H_disjoint : disjoint ascii_beq
                             (possible_terminals_of G nt)
                             (possible_first_terminals_of_production G its))
: refine {splits : list nat
         | split_list_is_complete
             G str
             (NonTerminal nt)
             its splits}
         (n <- { n : nat | n <= length str
                           /\ ((exists n', search_for_not_condition G str nt its n')
                               -> search_for_not_condition G str nt its n) };
          ret [n]).
Proof.
  intros ls H.
  computes_to_inv; subst.
  destruct H as [H0 H1].
  apply PickComputes.
  intros n ? H_reachable pit pits.
  left.
  pose proof (terminals_disjoint_search_for_not Hvalid _ H_disjoint pit pits H_reachable) as H'.
  specialize (H1 (ex_intro _ n H')).
  pose proof (is_first_char_such_that_eq_nat_iff H1 H') as H''.
  destruct_head or; destruct_head and; subst;
  rewrite ?Min.min_r by assumption;
  omega.
Qed.

Lemma find_first_char_such_that'_short {Char HSL}
      str P len
: @find_first_char_such_that' Char HSL P len str <= len.
Proof.
  revert str; induction len; simpl; intros; [ reflexivity | ].
  destruct (get (length str - S len) str) eqn:H.
  { edestruct P; try omega.
    apply Le.le_n_S, IHlen. }
  { apply Le.le_n_S, IHlen. }
Qed.

Lemma find_first_char_such_that_short {Char HSL}
      str P
: @find_first_char_such_that Char HSL str P <= length str.
Proof.
  apply find_first_char_such_that'_short.
Qed.

Lemma is_first_char_such_that__find_first_char_such_that {Char} {HSL} {HSLP : @StringLikeProperties Char HSL} str P
      might_be_empty
      (H : exists n, is_first_char_such_that might_be_empty str n (fun ch => is_true (P ch)))
: is_first_char_such_that might_be_empty str (@find_first_char_such_that Char HSL str P) (fun ch => is_true (P ch)).
Proof.
  unfold find_first_char_such_that.
  destruct H as [n H].
  set (len := length str).
  setoid_replace str with (drop (length str - len) str) at 1
    by (subst; rewrite Minus.minus_diag, drop_0; reflexivity).
  setoid_replace str with (drop (length str - len) str) in H
    by (subst; rewrite Minus.minus_diag, drop_0; reflexivity).
  assert (len <= length str) by reflexivity.
  clearbody len.
  generalize dependent str; revert n.
  induction len; simpl; intros n str IH Hlen.
  { apply first_char_such_that_0.
    rewrite drop_length.
    rewrite NPeano.Nat.sub_0_r in IH |- *.
    rewrite Minus.minus_diag.
    split.
    { apply for_first_char_nil.
      rewrite drop_length; omega. }
    { generalize dependent str.
      induction n; intros str H Hlen.
      { apply first_char_such_that_0 in H.
        rewrite drop_length, Minus.minus_diag in H.
        destruct_head and; trivial. }
      { apply first_char_such_that_past_end in H; [ | rewrite drop_length; omega ].
        left; assumption. } } }
  { pose proof (singleton_exists (take 1 (drop (length str - S len) str))) as H'.
    rewrite take_length, drop_length in H'.
    destruct H' as [ch H']; [ apply Min.min_case_strong; intros; omega | ].
    rewrite get_drop.
    rewrite (proj1 (get_0 _ _) H').
    destruct (P ch) eqn:H''.
    { apply first_char_such_that_0.
      rewrite drop_length.
      split; [ | right; omega ].
      apply (for_first_char__take 0).
      rewrite <- for_first_char_singleton by eassumption; trivial. }
    { apply is_first_char_such_that_drop.
      destruct n.
      { apply first_char_such_that_0 in IH.
        destruct IH as [IH _].
        apply (for_first_char__take 0) in IH.
        rewrite <- for_first_char_singleton in IH by eassumption; unfold is_true in *; congruence. }
      { apply is_first_char_such_that_drop in IH.
        destruct IH as [IH _].
        rewrite drop_drop in IH |- *; simpl in IH |- *.
        replace (S (length str - S len)) with (length str - len) in IH |- * by omega.
        split.
        { eapply IHlen; try eassumption; [].
          omega. }
        { apply (for_first_char__take 0).
          rewrite <- for_first_char_singleton by eassumption; congruence. } } } }
Qed.

Lemma refine_find_first_char_such_that {Char} {HSL : StringLike Char} {HSLP : @StringLikeProperties Char HSL}
      (str : @String Char HSL)
      (P : Char -> bool)
      might_be_empty
: refine { n : nat | n <= length str
                     /\ ((exists n', is_first_char_such_that might_be_empty str n' P)
                         -> is_first_char_such_that might_be_empty str n P) }
         (ret (find_first_char_such_that str P)).
Proof.
  intros v H.
  computes_to_inv; subst.
  apply PickComputes.
  split; [ apply find_first_char_such_that_short | ].
  apply is_first_char_such_that__find_first_char_such_that.
Qed.

Lemma refine_disjoint_search_for
      {HSL : StringLike Ascii.ascii}
      {HSI : StringIso Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {HSIP : StringIsoProperties Ascii.ascii}
      {G : grammar Ascii.ascii}
      {str nt its}
      (Hvalid : grammar_rvalid G)
      (H_disjoint : disjoint ascii_beq
                             (possible_terminals_of G nt)
                             (possible_first_terminals_of_production G its))
: refine {splits : list nat
         | split_list_is_complete
             G str
             (NonTerminal nt)
             its splits}
         (ret [find_first_char_such_that str (fun ch => list_bin ascii_beq ch (possible_first_terminals_of_production G its))]).
Proof.
  rewrite refine_disjoint_search_for' by assumption.
  setoid_rewrite refine_find_first_char_such_that.
  simplify with monad laws; reflexivity.
Qed.

Lemma refine_disjoint_search_for_not
      {HSL : StringLike Ascii.ascii}
      {HSI : StringIso Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {HSIP : StringIsoProperties Ascii.ascii}
      {G : grammar Ascii.ascii} {str nt its}
      (Hvalid : grammar_rvalid G)
      (H_disjoint : disjoint ascii_beq
                             (possible_terminals_of G nt)
                             (possible_first_terminals_of_production G its))
: refine {splits : list nat
         | split_list_is_complete
             G str
             (NonTerminal nt)
             its splits}
         (ret [find_first_char_such_that str (fun ch => negb (list_bin ascii_beq ch (possible_terminals_of G nt)))]).
Proof.
  rewrite refine_disjoint_search_for_not' by assumption.
  setoid_rewrite refine_find_first_char_such_that.
  simplify with monad laws; reflexivity.
Qed.
