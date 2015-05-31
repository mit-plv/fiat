Require Import Coq.Lists.List Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Import Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.SetoidInstances.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Common.
Require Import Fiat.Common.SetoidInstances.

Set Implicit Arguments.

Section cfg.
  Context {Char} {HSL : StringLike Char}
          {pdata : paren_balanced_hiding_dataT Char}.

  Local Ltac induction_str_len str :=
    let len := fresh "len" in
    set (len := length str);
      generalize (eq_refl : length str = len);
      clearbody len; revert str;
      induction len; intros str ?.



  Definition paren_balanced'_step (ch : Char) (pbh_rest : nat -> bool) (start_level : nat)
    : bool
      := if is_bin_op ch
         then pbh_rest start_level
         else if is_open ch
              then pbh_rest (S start_level)
              else if is_close ch
                   then ((Compare_dec.gt_dec start_level 0)
                           && pbh_rest (pred start_level))%bool
                   else pbh_rest start_level.

    Definition paren_balanced' (str : String) (start_level : nat)
    : bool
      := fold
           paren_balanced'_step
           (fun _ => true)
           str
           start_level.

    Lemma paren_balanced'_nil (str : String) (H : length str = 0)
    : paren_balanced' str = fun _ => true.
    Proof.
      apply fold_nil; assumption.
    Qed.

    Lemma paren_balanced'_recr {HSLP : StringLikeProperties Char} (str : String)
    : paren_balanced' str
      = match get 0 str with
          | Some ch => paren_balanced'_step ch (paren_balanced' (drop 1 str))
          | None => fun _ => true
        end.
    Proof.
      apply fold_recr.
    Qed.

    Global Instance paren_balanced'_Proper1 {HSLP : StringLikeProperties Char}
    : Proper (beq ==> eq ==> eq) paren_balanced'.
    Proof.
      unfold paren_balanced'.
      repeat intro; subst.
      match goal with
        | [ |- ?f ?x = ?g ?x ] => cut (f = g); [ let H := fresh in intro H; rewrite H; reflexivity | ]
      end.
      setoid_subst_rel beq.
      reflexivity.
    Qed.

    Typeclasses Opaque paren_balanced'.
    Opaque paren_balanced'.

    Lemma paren_balanced'_S {HSLP : StringLikeProperties Char} (str : String) n
    : paren_balanced' str n -> paren_balanced' str (S n).
    Proof.
      revert n.
      induction_str_len str.
      { rewrite paren_balanced'_nil by assumption; simpl.
        reflexivity. }
      { specialize (IHlen (drop 1 str)).
        rewrite drop_length in IHlen.
        repeat match goal with
                 | [ H : ?A -> ?B |- _ ] => let H' := fresh in assert (H' : A) by omega; specialize (H H'); clear H'
               end.
        rewrite paren_balanced'_recr.
        destruct (singleton_exists (take 1 str)) as [ch H''].
        { rewrite take_length, H; reflexivity. }
        { rewrite (proj1 (get_0 _ _) H'').
          unfold paren_balanced'_step.
          repeat match goal with
                   | [ |- context[if ?f ch then _ else _] ] => destruct (f ch) eqn:?
                   | _ => reflexivity
                   | _ => solve [ eauto with nocore ]
                   | _ => progress simpl in *
                   | _ => setoid_rewrite Bool.andb_true_iff
                   | _ => intro
                   | [ H : and _ _ |- _ ] => destruct H
                   | [ H : bool_of_sumbool (Compare_dec.gt_dec ?a ?b) = true |- _ ] => destruct (Compare_dec.gt_dec a b)
                   | _ => congruence
                   | [ H : ?n > 0 |- _ ] => is_var n; destruct n
                 end. } }
    Qed.

    Lemma paren_balanced'_le {HSLP : StringLikeProperties Char} (str : String) n1 n2 (H : n1 <= n2)
    : paren_balanced' str n1 -> paren_balanced' str n2.
    Proof.
      apply Minus.le_plus_minus in H.
      revert str.
      generalize dependent (n2 - n1).
      intros diff ?; subst n2; revert n1.
      induction diff; simpl.
      { intros ?? H.
        replace (n1 + 0) with n1 by omega.
        assumption. }
      { intro n1.
        replace (n1 + S diff) with (S (n1 + diff)) by omega.
        intros.
        eauto using paren_balanced'_S with nocore. }
    Qed.

    Definition paren_balanced (str : String) := paren_balanced' str 0.
  End paren_balanced_def.
