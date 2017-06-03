(** * Build a table for the next binop at a given level *)
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Common.

Set Implicit Arguments.

Section specific.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char}.
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

    Lemma paren_balanced'_split {HSLP : StringLikeProperties Char}
          (str : String) (n : nat) (level1 level2 : nat)
          (H1 : paren_balanced' (take n str) level1)
          (H2 : paren_balanced' (drop n str) level2)
    : paren_balanced' str (level1 + level2).
    Proof.
      revert n level1 level2 H1 H2.
      set (len := length str).
      generalize (eq_refl : length str = len).
      clearbody len.
      revert str.
      induction len as [|len IHlen].
      { intros str Hlen ???.
        rewrite !paren_balanced'_nil
          by (rewrite ?drop_length, ?take_length, Hlen; destruct n; reflexivity).
        destruct level1, level2; simpl; intros; congruence. }
      { intros str Hlen ???.
        specialize (IHlen (drop 1 str)).
        specialize_by (rewrite drop_length; omega).
        specialize (IHlen (pred n)).
        destruct n as [|n].
        { clear IHlen.
          rewrite drop_0.
          rewrite !paren_balanced'_nil
            by (rewrite ?drop_length, ?take_length, Hlen; reflexivity).
          destruct level1; simpl; intros; [ assumption | congruence ]. }
        { simpl in *.
          setoid_rewrite drop_drop in IHlen.
          setoid_rewrite take_drop in IHlen.
          rewrite !NPeano.Nat.add_1_r in IHlen.
          specialize (fun H' level1 H => IHlen level1 level2 H H').
          intros H1 H2.
          specialize_by assumption.
          rewrite paren_balanced'_recr in H1 |- *.
          rewrite get_take_lt in H1 by omega.
          destruct (get 0 str) eqn:H'.
          { unfold paren_balanced'_step in *.
            repeat match goal with
                     | _ => progress simpl in *
                     | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
                     | [ IHlen : forall level : nat, _ -> _, H : is_true (paren_balanced' _ _) |- _ ]
                       => specialize (IHlen _ H)
                     | [ IHlen : forall level : nat, _ -> _, H : paren_balanced' _ _ = true |- _ ]
                       => specialize (IHlen _ H)
                     | _ => solve [ eauto with nocore ]
                     | [ H : is_true (andb _ _) |- _ ] => apply Bool.andb_true_iff in H
                     | _ => progress split_and
                     | [ |- is_true (andb _ _) ] => apply Bool.andb_true_iff
                     | _ => congruence
                     | _ => omega
                     | [ H : context[bool_of_sumbool ?e] |- _ ] => destruct e; simpl in H
                     | [ |- context[bool_of_sumbool ?e] ] => destruct e; simpl
                     | [ |- _ /\ _ ] => split
                     | [ H : context[pred ?x] |- _ ] => is_var x; destruct x
                   end. }
          { apply no_first_char_empty in H'.
            omega. } } }
    Qed.

    Lemma paren_balanced'_split_0 {HSLP : StringLikeProperties Char}
          (str : String) (n : nat) (level : nat)
          (H1 : paren_balanced' (take n str) 0)
          (H2 : paren_balanced' (drop n str) level)
    : paren_balanced' str level.
    Proof.
      change level with (0 + level).
      eapply paren_balanced'_split; eassumption.
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

    Lemma paren_balanced_hiding'_split {HSLP : StringLikeProperties Char}
          (str : String) (n : nat) (level1 level2 : nat)
          (H1 : if Compare_dec.gt_dec level2 0
                then paren_balanced' (take n str) level1
                else paren_balanced_hiding' (take n str) level1)
          (H2 : paren_balanced_hiding' (drop n str) level2)
    : paren_balanced_hiding' str (level1 + level2).
    Proof.
      revert n level1 level2 H1 H2.
      set (len := length str).
      generalize (eq_refl : length str = len).
      clearbody len.
      revert str.
      induction len as [|len IHlen].
      { intros str Hlen ???.
        rewrite !paren_balanced_hiding'_nil
          by (rewrite ?drop_length, ?take_length, Hlen; destruct n; reflexivity).
        destruct level1, level2; simpl; intros; congruence. }
      { intros str Hlen ???.
        specialize (IHlen (drop 1 str)).
        specialize_by (rewrite drop_length; omega).
        specialize (IHlen (pred n)).
        destruct n as [|n].
        { clear IHlen.
          rewrite drop_0.
          rewrite ?paren_balanced_hiding'_nil, ?paren_balanced'_nil
            by (rewrite ?drop_length, ?take_length, Hlen; reflexivity).
          destruct level1, level2; simpl; intros; first [ assumption | congruence ]. }
        { simpl in *.
          setoid_rewrite drop_drop in IHlen.
          rewrite !NPeano.Nat.add_1_r in IHlen.
          specialize (fun H' level1 H => IHlen level1 level2 H H').
          intros H1 H2.
          specialize_by assumption.
          rewrite paren_balanced_hiding'_recr in H1 |- *.
          rewrite paren_balanced'_recr in H1.
          rewrite !get_take_lt in H1 by omega.
          destruct (get 0 str) eqn:H'.
          { unfold paren_balanced_hiding'_step, paren_balanced'_step in *.
            repeat match goal with
                     | _ => progress simpl in *
                     | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
                     | [ IHlen : forall level : nat, is_true (?f _ _) -> _, H : is_true (?f _ _) |- _ ]
                       => specialize (IHlen _ H)
                     | [ IHlen : forall level : nat, is_true (?f _ _) -> _, H : ?f _ _ = true |- _ ]
                       => specialize (IHlen _ H)
                     | _ => solve [ eauto with nocore ]
                     | [ H : is_true (andb _ _) |- _ ] => apply Bool.andb_true_iff in H
                     | _ => progress split_and
                     | [ |- is_true (andb _ _) ] => apply Bool.andb_true_iff
                     | _ => congruence
                     | _ => omega
                     | [ H : context[take _ (drop _ _)] |- _ ] => setoid_rewrite take_drop in H
                     | [ H : context[(_ + 1)%nat] |- _ ] => rewrite !NPeano.Nat.add_1_r in H
                     | [ H : context[bool_of_sumbool ?e] |- _ ] => destruct e; simpl in H
                     | [ H : context[match ?e with left _ => _ | right _ => _ end] |- _ ] => destruct e; simpl in H
                     | [ |- context[bool_of_sumbool ?e] ] => destruct e; simpl
                     | [ |- _ /\ _ ] => split
                     | [ H : context[pred ?x] |- _ ] => is_var x; destruct x
                   end. }
          { apply no_first_char_empty in H'.
            omega. } } }
    Qed.

    Lemma paren_balanced_hiding'_split_0 {HSLP : StringLikeProperties Char}
          (str : String) (n : nat) (level : nat)
          (H1 : if Compare_dec.gt_dec level 0
                then paren_balanced' (take n str) 0
                else paren_balanced_hiding' (take n str) 0)
          (H2 : paren_balanced_hiding' (drop n str) level)
    : paren_balanced_hiding' str level.
    Proof.
      change level with (0 + level).
      eapply paren_balanced_hiding'_split; eassumption.
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
