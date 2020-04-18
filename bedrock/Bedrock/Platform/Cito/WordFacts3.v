Set Implicit Arguments.

Require Import Coq.Arith.Arith Bedrock.Platform.AutoSep. (* necessary for lemmas related to N *)

(* usuful and safe hints *)
Hint Rewrite Npow2_nat : N.
Local Hint Resolve bound_N_nat : N.
Hint Rewrite natToWord_wordToNat : N.


(* ============================================================================
 * goodsize tactic
 * ========================================================================= *)

Ltac goodsize :=
  match goal with
    | [ |- (_ < pow2 32)%nat ] => apply goodSize_danger
    | _ => idtac
  end;
  match goal with
    | [ H: goodSize ?n |- goodSize _ ] => solve [apply goodSize_weaken with n; auto]
    | _ => auto
  end.


(* ============================================================================
 * roundTrip-related lemmas and roundtrip tactic
 * ========================================================================= *)

Corollary wordToNat_natToWord_idempotent_W : forall n,
                                               goodSize n ->
                                               wordToNat (natToW n) = n.
intros; apply wordToNat_natToWord_idempotent; auto.
Qed.
Hint Rewrite wordToNat_natToWord_idempotent_W using solve [goodsize] : N.

Corollary roundTrip : forall sz n : nat,
                        (n < pow2 sz)%nat -> wordToNat (natToWord sz n) = n.
intros; apply wordToNat_natToWord_idempotent; nomega.
Qed.
Hint Rewrite roundTrip using solve [eauto] : N.

Lemma natToW_wordToNat : forall w:W, natToW (wordToNat w) = w.
  intros; rewrite <- natToWord_wordToNat; auto.
Qed.
Hint Rewrite natToW_wordToNat : N.

Ltac roundtrip := pre_nomega; unfold natToW; repeat rewrite wordToNat_natToWord_idempotent_W by goodsize.



(* ============================================================================
 * word to nat
 * ========================================================================= *)

Theorem wordToNat_inj : forall sz (x y:word sz),
                          wordToNat x = wordToNat y -> x = y.
  intros.
  apply (f_equal (natToWord sz)) in H.
  autorewrite with N in *.
  assumption.
Qed.

Theorem wordToNat_inj' : forall sz (x y:word sz), x <> y ->
                                                  wordToNat x <> wordToNat y.
  intros.
  contradict H.
  apply wordToNat_inj; assumption.
Qed.


(* ============================================================================
 * nat to word
 * ========================================================================= *)
Transparent goodSize.

Lemma goodSize_natToW_wlt_lt : forall n m:nat, goodSize n -> goodSize m ->
                                               natToW n < natToW m -> (n < m)%nat.
  unfold goodSize, natToW.
  generalize dependent 32; intros; nomega.
Qed.

Lemma natToWord_pow2' : forall(sz k:nat)(w:word sz),
                          natToWord sz (k * pow2 sz) ^+ w = w.
  induction k; intros; simpl.

  apply wplus_unit.

  rewrite natToWord_plus.
  rewrite <- wplus_assoc.
  rewrite natToWord_pow2.
  rewrite wplus_unit.
  apply IHk.
Qed.

Lemma natToWord_pow2_zero: forall sz n, $ (n * pow2 sz) = natToWord sz 0.
  intros.
  rewrite <- (wplus_unit $ (n * pow2 sz)).
  rewrite wplus_comm.
  apply natToWord_pow2'.
Qed.

Lemma natToWord_pow2_factor : forall (sz:nat)(w:word sz), exists n, forall k,
                                                                      (n < pow2 sz)%nat /\ w = natToWord sz (k * pow2 sz + n).
  intros.
  exists (wordToNat w).
  intro.
  split.
  apply (wordToNat_bound w).
  rewrite natToWord_plus.
  rewrite natToWord_pow2'.
  rewrite natToWord_wordToNat.
  reflexivity.
Qed.

Corollary word_eq_natToWord : forall (sz:nat)(w:word sz), exists n,
                                (n < pow2 sz)%nat /\ w = natToWord sz n.
intros.
generalize natToWord_pow2_factor; intro.
specialize (H sz w).
destruct H.
specialize (H 0).
destruct H.
simpl in H0.
exists x; auto.
Qed.

Corollary W_eq_natToW : forall(w:W), exists n, goodSize n /\ w = natToW n.
intros.
generalize word_eq_natToWord; intro.
specialize (H 32 w).
destruct H.
destruct H.
exists x.
unfold goodSize.
split; auto.
Qed.

Opaque goodSize.


(* ============================================================================
 * destruct_word
   Turn word arithmetic into nat arithmetic.
 * ========================================================================= *)

Ltac destruct_word sz w n :=
  let H := fresh "W" in
  let Hub := fresh "Wub" in
  let Heq := fresh "Weq" in
  assert (H:exists w', (w' < pow2 sz)%nat /\ w = natToWord sz w') by
      apply word_eq_natToWord;
    elim H; clear H; intros n H; elim H; intros Hub Heq; rewrite Heq in *; clear H Heq w.

Ltac destruct_W w n :=
  let H := fresh "W" in
  let Hub := fresh "Wub" in
  let Heq := fresh "Weq" in
  assert (H:exists w', goodSize w' /\ w = natToW w') by
      apply W_eq_natToW;
    elim H; clear H; intros n H; elim H; intros Hub Heq; rewrite Heq in *; clear H Heq w.

Ltac destruct_all_words := repeat
                             match goal with
                               | [w : word ?sz |- _ ] =>
                                 is_var w; let w' := fresh "w" in destruct_word sz w w'
                               | [w : W |- _ ] =>
                                 is_var w; let w' := fresh "w" in destruct_W w w'
                             end.


(* ============================================================================
 * word equalities with operators
 * ========================================================================= *)

Lemma natToW_plus_pow2 : forall n:nat, natToW n = natToW (n + pow2 32).
  intro.
  unfold natToW.
  rewrite natToWord_plus.
  rewrite natToWord_pow2.
  words.
Qed.

Lemma wneg_natToW_pow2_minus : forall n:nat, goodSize n ->
                                             ^~ (natToW n) = natToW (pow2 32 - n).
  intros.
  unfold wneg.
  rewrite NToWord_nat.
  rewrite N2Nat.inj_sub.
  rewrite Npow2_nat.
  rewrite natToWordToN.
  rewrite Nat2N.id.
  reflexivity.
  assumption.
Qed.

Lemma wordToNat_wminus : forall n m:W, n <= m ->
                                       wordToNat (m ^- n) = wordToNat m - wordToNat n.
  intros.
  destruct_all_words.

  assert (natToW (pow2 32 + (w - w0)) = (natToW (w - w0))).
  rewrite plus_comm.
  rewrite <- natToW_plus_pow2.
  reflexivity.
  unfold natToW in *.

  unfold wminus.
  rewrite wneg_natToW_pow2_minus; auto.
  rewrite <- natToWord_plus.
  rewrite NPeano.Nat.add_sub_assoc.
  rewrite plus_comm.
  rewrite <- NPeano.Nat.add_sub_assoc.
  rewrite H0.
  autorewrite with N.
  reflexivity.
  apply wle_goodSize; auto.
  apply lt_le_weak.
  apply goodSize_danger; auto.
Qed.

Corollary wordToNat_wplus : forall sz x y:nat, (x + y < pow2 sz)%nat ->
                                               wordToNat (natToWord sz x ^+ natToWord sz y) = x + y.
intros.
rewrite <- natToWord_plus.
rewrite roundTrip; auto.
Qed.


(* ============================================================================
 * word inequalities
 * ========================================================================= *)

Lemma wle_wneq_wlt : forall i j:W, i <= j -> i <> j -> i < j.
  intros.
  destruct_all_words.
  apply wordToNat_inj' in H0.
  autorewrite with N in *.
  nomega.
Qed.

Lemma wle_wle_antisym : forall n m:W, n <= m -> m <= n -> n = m.
  intros.
  destruct_all_words.
  f_equal.
  nomega.
Qed.
