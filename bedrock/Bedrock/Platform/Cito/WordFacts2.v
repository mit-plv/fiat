Require Import Coq.omega.Omega.
Set Implicit Arguments.

Require Import Bedrock.Platform.AutoSep Coq.Arith.Arith.

(* usuful and safe hints *)
Local Hint Resolve bound_N_nat : N.
Hint Rewrite Npow2_nat : N.
Hint Rewrite natToWord_wordToNat : N.

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

Lemma natToWord_inj' : forall sz a b, goodSize a -> goodSize b
                                      -> natToWord sz a <> $ b
                                      -> a <> b.
  intros; intro; subst; congruence.
Qed.


(* ============================================================================
 * nat to W
 * ========================================================================= *)

Transparent goodSize.

Lemma goodSize_natToW_wlt_lt : forall n m:nat, goodSize n -> goodSize m ->
                                               natToW n < natToW m -> (n < m)%nat.
  unfold goodSize, natToW.
  generalize dependent 32; intros; nomega.
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

Lemma wneg_natToW_pow2_minus : forall n:nat, goodSize n ->
                                             ^~ (natToW n) = natToW (pow2 32 - n).
  unfold wneg; intros.
  rewrite NToWord_nat.
  autorewrite with N; reflexivity.
Qed.

Lemma natToW_plus_pow2 : forall n : nat, natToW (pow2 32 + n) = $ n.
  unfold natToW; intros.
  rewrite natToWord_plus.
  rewrite natToWord_pow2.
  words.
Qed.


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

Ltac destruct_words := repeat
                         match goal with
                           | w : W |- context[?w] =>
                             is_var w; let w' := fresh "w" in destruct_W w w'
                           | w : word 32 |- context[?w] =>
                             is_var w; let w' := fresh "w" in destruct_W w w'
                           | w : word ?sz |- context[?w] =>
                             is_var w; let w' := fresh "w" in destruct_word sz w w'
                         end.


(* ============================================================================
 * goodsize tactic
 * ========================================================================= *)

Ltac goodsize :=
  match goal with
    | |- (_ < pow2 32)%nat => apply goodSize_danger
    | _ => idtac
  end;
  match goal with
    | [ H: goodSize _ |- goodSize _ ]
      => solve [apply (goodSize_weaken _ _ H); auto; omega]
    | |- goodSize _ => solve [auto]
    | _ => omega
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

Lemma wordToNat_wplus' : forall sz (x y: word sz),
                           (wordToNat x + wordToNat y < pow2 sz)%nat
                           -> wordToNat (x ^+ y) = wordToNat x + wordToNat y.
  intros.
  destruct_words.
  rewrite <- natToWord_plus.
  rewrite roundTrip; auto.
  pre_nomega; auto.
  rewrite wordToNat_natToWord_idempotent in * by nomega.
  rewrite wordToNat_natToWord_idempotent in * by nomega.
  auto.
Qed.

Corollary wordToNat_wplus'' : forall sz (x y: nat), (x + y < pow2 sz)%nat
                                                    -> wordToNat ($ x ^+ natToWord sz y) = x + y.
intros.
rewrite wordToNat_wplus' by nomega.
rewrite ! roundTrip; auto.
Qed.

Corollary wordToNat_wminus'' : forall sz (x y: nat), (x < pow2 sz)%nat
                                                     -> (y <= x)%nat
                                                     -> wordToNat ($ x ^- natToWord sz y) = x - y.
intros.
rewrite wordToNat_wminus by nomega.
rewrite ! roundTrip; auto.
Qed.

Lemma mult_S : forall x y, (x <= x * S y)%nat.
  intros; rewrite mult_comm; simpl; apply le_plus_l.
Qed.
Local Hint Resolve mult_S.

Local Hint Resolve mult_comm.

Corollary wordToNat_wmult_W : forall (x y: nat), goodSize (x * y)%nat
                                                 -> wordToNat (natToW x ^* natToW y) = x * y.
intros.
unfold natToW in *.
destruct x, y; simpl; auto.
assert (wordToNat (natToWord 32 0) = 0).
rewrite roundTrip by goodsize; auto.
rewrite wordToNat_wmult.
unfold natToW in *; rewrite H0; omega.
rewrite H0; simpl; goodsize.

assert (goodSize (S x)) by goodsize.
assert (goodSize (S y)).
{
  apply (goodSize_weaken _ _ H).
  rewrite mult_comm; auto.
}
rewrite wordToNat_wmult.
rewrite ! roundTrip by goodsize; simpl; omega.
rewrite ! roundTrip by goodsize; auto.
Qed.


(* ============================================================================
 * natToWord and operators
 * ========================================================================= *)

Lemma natToWord_mult : forall sz x y, natToWord sz (x * y)
                                      = natToWord _ x ^* natToWord _ y.
  unfold "^*", wordBin; intros.
  pre_nomega.
  rewrite <- Nat2N.inj_mul.
  rewrite NToWord_nat.
  pre_nomega.

  destruct (wordToNat_natToWord' sz x).
  rewrite <- H at 1.
  remember (wordToNat $ (x)) as x'.

  rewrite mult_plus_distr_r.
  rewrite natToWord_plus.
  replace (x0 * pow2 sz * y)%nat with ((x0 * y) * pow2 sz)%nat.
  rewrite natToWord_pow2_zero.
  rewrite <- natToWord_plus.
  rewrite plus_0_r.

  destruct (wordToNat_natToWord' sz y).
  rewrite <- H0 at 1.
  remember (wordToNat $ (y)) as y'.
  rewrite mult_plus_distr_l.
  rewrite natToWord_plus.
  replace (x' * (x1 * pow2 sz))%nat with ((x' * x1) * pow2 sz)%nat by apply mult_assoc_reverse.
  rewrite natToWord_pow2_zero.
  rewrite <- natToWord_plus; auto.

  rewrite 2 mult_assoc_reverse.
  f_equal.
  apply mult_comm.
Qed.


(* ============================================================================
 * simplification tactic
 * ========================================================================= *)

Ltac roundtrip :=
  pre_nomega; unfold natToW in *;
  repeat match goal with
           | _ => rewrite wordToNat_natToWord_idempotent_W in * by goodsize
           | _ => rewrite wordToNat_wminus'' in * by goodsize
           | _ => rewrite wordToNat_wminus in * by nomega
           | _ => rewrite wordToNat_wplus'' in * by goodsize
           | _ => rewrite wordToNat_wplus' in * by goodsize
           | _ => rewrite wordToNat_wmult_W in * by goodsize
           | _ => rewrite wordToNat_wmult in * by goodsize

           | H: _ |- _ => rewrite <- natToW_minus in H by omega; unfold natToW in H
           | H: _ |- _ => rewrite <- natToWord_plus in H
           | H: _ |- _ => rewrite <- natToWord_mult in H
           | H: natToWord ?sz _ = natToWord ?sz _ |- _
             => apply natToWord_inj with sz _ _ in H; try goodsize
           | H: not (natToWord ?sz _ = natToWord ?sz _) |- _
             => apply natToWord_inj' with sz _ _ in H; try goodsize
         end.


(* ============================================================================
 * word equality lemmas
 * ========================================================================= *)

Definition eq_W_dec : forall x y : W, { x = y } + { x <> y }.
  intros.
  destruct (Word.weqb x y) eqn:Heq; [apply weqb_sound in Heq | ]; auto.
  right; intro.
  apply weqb_true_iff in H; congruence.
Qed.

Lemma weqb_false_iff : forall sz (x y : word sz), Word.weqb x y = false <-> x <> y.
  intros.
  split; intros.
  intro Eq; apply weqb_true_iff in Eq; congruence.
  case_eq (Word.weqb x y); intro; auto.
  apply weqb_sound in H0; congruence.
Qed.

Lemma weqb_refl : forall w, weqb w w = true.
  intros; apply weqb_true_iff; auto.
Qed.
Hint Rewrite weqb_refl : N.

Lemma weqb_refl' : forall x y, x = y -> weqb x y = true.
  intros; subst; autorewrite with N; auto.
Qed.
Hint Rewrite weqb_refl' using solve [auto; words] : N.

Lemma weqb_diff : forall w1 w2, w1 <> w2 -> weqb w1 w2 = false.
  intros; apply weqb_false_iff; auto.
Qed.
Hint Rewrite weqb_diff using solve [auto; discriminate] : N.


(* ============================================================================
 * word operators
 * ========================================================================= *)

Lemma wplus_unit_r : forall sz w, w ^+ natToWord sz 0 = w.
  intros; rewrite wplus_comm; rewrite wplus_unit; auto.
Qed.
Hint Rewrite wplus_unit wplus_unit_r : N.

Lemma wminus_unit : forall sz w, w ^- natToWord sz 0 = w.
  intros.
  unfold "^-", "^~".
  roundtrip.
  rewrite N.sub_0_r.
  rewrite NToWord_nat.
  roundtrip.
  rewrite natToWord_pow2.
  autorewrite with N; auto.
Qed.

Lemma wmult_zero : forall w, natToW 0 ^* w = natToW 0.
  auto.
Qed.

Lemma wmult_zero_r : forall w, w ^* natToW 0 = natToW 0.
  intros; roundtrip; rewrite wmult_comm; auto.
Qed.
Hint Rewrite wmult_zero wmult_zero_r : N.


(* ============================================================================
 * natToW and operators
 * ========================================================================= *)

Lemma natToW_S_wminus_1 : forall n, $ (S n) ^- $1 = natToW n.
  unfold natToW; intros.
  replace (S n) with (n + 1) by omega; rewrite natToWord_plus.
  words.
Qed.
Hint Rewrite natToW_S_wminus_1 : N.


(* ============================================================================
 * word inequalities
 * ========================================================================= *)

Lemma wle_wneq_wlt : forall i j:W, i <= j -> i <> j -> i < j.
  intros; destruct_words.
  apply wordToNat_inj' in H0.
  autorewrite with N in *; nomega.
Qed.

Lemma wle_wle_antisym : forall n m:W, n <= m -> m <= n -> n = m.
  intros; destruct_words; f_equal; nomega.
Qed.
