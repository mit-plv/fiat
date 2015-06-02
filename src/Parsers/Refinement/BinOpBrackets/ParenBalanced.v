(** * Build a table for the next binop at a given level *)
Require Import Coq.Lists.List Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Import Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Common.

Set Implicit Arguments.

Section specific.
  Context {Char} {HSL : StringLike Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}.

  Local Ltac induction_str_len str :=
    let len := fresh "len" in
    set (len := length str);
      generalize (eq_refl : length str = len);
      clearbody len; revert str;
      induction len; intros str ?.

  Section paren_balanced_def.
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

    Global Instance paren_balanced'_step_Proper {ch}
    : Proper ((eq ==> eq) ==> eq ==> eq) (paren_balanced'_step ch).
    Proof.
      unfold paren_balanced'_step.
      repeat intro; subst.
      unfold respectful in *.
      edestruct Compare_dec.gt_dec; simpl;
      repeat match goal with
               | _ => reflexivity
               | [ |- context[if ?e then _ else _] ] => destruct e
               | [ H : _ |- _ ] => apply H
             end.
    Qed.

    Definition paren_balanced' (str : String) (start_level : nat)
    : bool
      := fold
           paren_balanced'_step
           Compare_dec.zerop
           str
           start_level.

    Lemma paren_balanced'_nil (str : String) (H : length str = 0)
    : paren_balanced' str = Compare_dec.zerop.
    Proof.
      apply fold_nil; assumption.
    Qed.

    Lemma paren_balanced'_recr {HSLP : StringLikeProperties Char} (str : String)
    : paren_balanced' str
      = match get 0 str with
          | Some ch => paren_balanced'_step ch (paren_balanced' (drop 1 str))
          | None => Compare_dec.zerop
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

    (*Lemma paren_balanced'_S {HSLP : StringLikeProperties Char} (str : String) n
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
                   | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
                   | _ => reflexivity
                   | _ => solve [ eauto with nocore ]
                   | _ => progress simpl in *
                   | _ => setoid_rewrite Bool.andb_true_iff
                   | _ => intro
                   | [ H : and _ _ |- _ ] => destruct H
                   | [ H : bool_of_sumbool ?x = true |- _ ] => destruct x
                   | _ => progress subst
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
    Qed.*)

    Definition paren_balanced (str : String) := paren_balanced' str 0.

    Global Instance paren_balanced_Proper1 {HSLP : StringLikeProperties Char}
    : Proper (beq ==> eq) paren_balanced.
    Proof.
      repeat intro.
      unfold paren_balanced.
      setoid_subst_rel beq.
      reflexivity.
    Qed.
  End paren_balanced_def.

  Section paren_balanced_hiding_def.
    Definition paren_balanced_hiding'_step (ch : Char) (pbh_rest : nat -> bool) (start_level : nat)
    : bool
      := if is_bin_op ch
         then ((Compare_dec.gt_dec start_level 0)
                 && pbh_rest start_level)%bool
         else paren_balanced'_step ch pbh_rest start_level.

    Global Instance paren_balanced_hiding'_step_Proper {ch}
    : Proper ((eq ==> eq) ==> eq ==> eq) (paren_balanced_hiding'_step ch).
    Proof.
      unfold paren_balanced_hiding'_step.
      repeat intro; subst.
      edestruct Compare_dec.gt_dec; simpl;
      repeat match goal with
               | _ => reflexivity
               | [ H : _ |- _ ] => erewrite !H; reflexivity
             end.
    Qed.

    Definition paren_balanced_hiding' (str : String) (start_level : nat)
    : bool
      := fold
           paren_balanced_hiding'_step
           (Compare_dec.zerop)
           str
           start_level.

    Lemma paren_balanced_hiding'_nil (str : String) (H : length str = 0)
    : paren_balanced_hiding' str = Compare_dec.zerop.
    Proof.
      apply fold_nil; assumption.
    Qed.

    Lemma paren_balanced_hiding'_recr {HSLP : StringLikeProperties Char} (str : String)
    : paren_balanced_hiding' str
      = match get 0 str with
          | Some ch => paren_balanced_hiding'_step ch (paren_balanced_hiding' (drop 1 str))
          | None => Compare_dec.zerop
        end.
    Proof.
      apply fold_recr.
    Qed.

    Global Instance paren_balanced_hiding'_Proper1 {HSLP : StringLikeProperties Char}
    : Proper (beq ==> eq ==> eq) paren_balanced_hiding'.
    Proof.
      unfold paren_balanced_hiding'.
      repeat intro; subst.
      match goal with
        | [ |- ?f ?x = ?g ?x ] => cut (f = g); [ let H := fresh in intro H; rewrite H; reflexivity | ]
      end.
      setoid_subst_rel beq.
      reflexivity.
    Qed.

    Typeclasses Opaque paren_balanced_hiding'.
    Opaque paren_balanced_hiding'.

    (*Lemma paren_balanced_hiding'_S {HSLP : StringLikeProperties Char} (str : String) n
    : paren_balanced_hiding' str n -> paren_balanced_hiding' str (S n).
    Proof.
      revert n.
      induction_str_len str.
      { rewrite paren_balanced_hiding'_nil by assumption; simpl.
        reflexivity. }
      { specialize (IHlen (drop 1 str)).
        rewrite drop_length in IHlen.
        repeat match goal with
                 | [ H : ?A -> ?B |- _ ] => let H' := fresh in assert (H' : A) by omega; specialize (H H'); clear H'
               end.
        rewrite paren_balanced_hiding'_recr.
        destruct (singleton_exists (take 1 str)) as [ch H''].
        { rewrite take_length, H; reflexivity. }
        { rewrite (proj1 (get_0 _ _) H'').
          unfold paren_balanced_hiding'_step, paren_balanced'_step.
          repeat match goal with
                   | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
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

    Lemma paren_balanced_hiding'_le {HSLP : StringLikeProperties Char} (str : String) n1 n2 (H : n1 <= n2)
    : paren_balanced_hiding' str n1 -> paren_balanced_hiding' str n2.
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
        eauto using paren_balanced_hiding'_S with nocore. }
    Qed.*)

    Definition paren_balanced_hiding (str : String) := paren_balanced_hiding' str 0.

    Global Instance paren_balanced_hiding_Proper1 {HSLP : StringLikeProperties Char}
    : Proper (beq ==> eq) paren_balanced_hiding.
    Proof.
      repeat intro.
      unfold paren_balanced_hiding.
      setoid_subst_rel beq.
      reflexivity.
    Qed.
  End paren_balanced_hiding_def.

  Section paren_balanced_to_hiding.
    Lemma paren_balanced_hiding_impl_paren_balanced' {HSLP : StringLikeProperties Char} n (str : String)
    : paren_balanced_hiding' str n -> paren_balanced' str n.
    Proof.
      revert n.
      induction_str_len str.
      { rewrite paren_balanced_hiding'_nil, paren_balanced'_nil by assumption; trivial. }
      { specialize (IHlen (drop 1 str)).
        rewrite drop_length, <- Minus.pred_of_minus in IHlen.
        specialize (IHlen (f_equal pred H)).
        rewrite paren_balanced_hiding'_recr, paren_balanced'_recr.
        edestruct get as [ch|]; trivial; [].
        unfold paren_balanced_hiding'_step, paren_balanced'_step.
        destruct (is_bin_op ch); try reflexivity;
        intros [|?]; simpl;
        destruct (is_open ch), (is_close ch);
        eauto with nocore;
        try (unfold is_true; intros; congruence). }
    Qed.

    Lemma paren_balanced_hiding_impl_paren_balanced {HSLP : StringLikeProperties Char} (str : String)
    : paren_balanced_hiding str -> paren_balanced str.
    Proof.
      apply paren_balanced_hiding_impl_paren_balanced'.
    Qed.

    (*Lemma paren_balanced_impl_paren_balanced_hiding' {HSLP : StringLikeProperties Char} n (str : String)
    : paren_balanced' str n -> paren_balanced_hiding' str (S n).
    Proof.
      revert n.
      induction_str_len str.
      { rewrite paren_balanced_hiding'_nil, paren_balanced'_nil by assumption; trivial. }
      { specialize (IHlen (drop 1 str)).
        rewrite drop_length, <- Minus.pred_of_minus in IHlen.
        specialize (IHlen (f_equal pred H)).
        rewrite paren_balanced_hiding'_recr, paren_balanced'_recr.
        edestruct get as [ch|]; trivial; [].
        unfold paren_balanced_hiding'_step, paren_balanced'_step.
        destruct (is_bin_op ch); simpl; eauto with nocore; [].
        intros [|?]; simpl;
        destruct (is_open ch), (is_close ch);
        eauto with nocore;
        try (unfold is_true; intros; congruence). }
    Qed.

    Lemma paren_balanced_impl_paren_balanced_hiding'_lt {HSLP : StringLikeProperties Char} n n' (Hlt : n < n') (str : String)
    : paren_balanced' str n -> paren_balanced_hiding' str n'.
    Proof.
      apply Minus.le_plus_minus in Hlt.
      generalize dependent (n' - S n).
      intros n'' ?; subst.
      revert n.
      induction n''.
      { intro.
        rewrite <- plus_n_O.
        apply paren_balanced_impl_paren_balanced_hiding'. }
      { simpl in *.
        intros n H'.
        apply paren_balanced_hiding'_S.
        rewrite NPeano.Nat.add_succ_r; eauto with nocore. }
    Qed.*)
  End paren_balanced_to_hiding.
End specific.

Global Opaque paren_balanced' paren_balanced_hiding'.
