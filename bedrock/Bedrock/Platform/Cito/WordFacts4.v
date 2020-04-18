Set Implicit Arguments.

Require Import Bedrock.Platform.AutoSep.
Require Import Bedrock.Platform.Cito.WordFacts2 Bedrock.Platform.Cito.WordFacts3.
Require Import Coq.Arith.Arith.

(* ============================================================================
 * N lemmas and Local Hints
 * ========================================================================= *)

Lemma S_minus: forall n, n<>0->S(n-1)=n.
  induction n; simpl; intuition.
Qed.
Lemma not0: forall (j i:W), i<j -> wordToNat j <> 0.
  intros. contradict H. nomega.
Qed.
Local Hint Resolve not0: list_ineq.
Hint Rewrite S_minus using solve [eauto 2 with list_ineq]: N.

Lemma easy_comparison: forall i x, i< natToW x -> (wordToNat i < x)%nat.
  intros.
  destruct_all_words.
  roundtrip.
  unfold natToW in *.
  destruct (lt_dec x (pow2 32)); auto.
  autorewrite with N in *; auto.
Qed.
Local Hint Resolve easy_comparison: list_ineq.

Lemma non_zero_wge1 : forall w:W, w <> $0 -> $1 <= w.
  intros.
  destruct_all_words; pre_nomega; unfold natToW in *.
  destruct w0; [congruence | auto].
Qed.

Local Hint Resolve non_zero_wge1.

Lemma word_minus_plus: forall w:W, w <> $0
                                   -> wordToNat (w ^- $1) + 1= wordToNat w.
  intros.
  assert ($1 <= w) by auto.
  rewrite wordToNat_wminus by auto.
  destruct_all_words; nomega.
Qed.

Lemma word_minus_plus': forall w:W, wordToNat (w ^- $1 ^+ $1) = wordToNat w.
  intros; f_equal; words.
Qed.

Hint Rewrite roundTrip_0: N.
Hint Rewrite word_minus_plus word_minus_plus' using solve [auto] : N.

Lemma word_plus: forall w:W, (exists j:W, w < j )
                             -> wordToNat (w ^+ $1) = wordToNat w + 1.
  intros.
  destruct H.
  destruct_all_words.
  pre_nomega; rewrite wordToNat_wplus; goodsize; nomega.
Qed.

Hint Rewrite word_plus using solve [eauto 2]: N.

Lemma word_minus: forall w:W, (exists j:W, j < w)
                              -> wordToNat (w ^- $1) = wordToNat w - 1.
  intros.
  destruct H.
  destruct_all_words.
  rewrite wordToNat_wminus; nomega.
Qed.

Lemma minus_plus_one: forall x:W, (exists j:W, j < x)
                                  -> wordToNat x - 1 + 1 = wordToNat x.
  intros.
  destruct H; nomega.
Qed.
Hint Rewrite word_minus minus_plus_one using solve [eauto 2] : N.


Lemma minus_plus_not0: forall x, x <> natToW 0
                                 -> natToW 0 <= x ^- natToW 1 ^+ natToW 1.
  intros; nomega.
Qed.
Local Hint Immediate minus_plus_not0.

Lemma minus_not0: forall x y:W , x <> 0 -> x = y -> x ^- $1 < y.
  intros; subst.
  assert ($1 <= y) by auto.
  destruct_all_words.
  pre_nomega; rewrite wordToNat_wminus by auto; nomega.
Qed.
Local Hint Immediate minus_not0.
Lemma plus1_ineq: forall i j x, (j< x) -> i<j -> i ^+ natToW 1 <= j ^+ natToW 1.
  intros; nomega.
Qed.
Local Hint Immediate plus1_ineq.
Lemma minus_plus_ineq: forall i j x : W, j ^- $1 < x
                                         -> i < j
                                         ->  i <= j ^- $1 ^+ $1.
  intros; nomega.
Qed.
Local Hint Immediate minus_plus_ineq.

Lemma plus1_S : forall n, n + 1 = S n.
  intros.
  rewrite Plus.plus_comm.
  simpl.
  auto.
Qed.
Hint Rewrite plus1_S: N.

Hint Rewrite roundTrip_1: N.
Lemma plus_minus_plus_ineq: forall i j x : W,
                              j < x -> i < j
                              -> i ^+ $1 <= j ^- $1 ^+ $1.
  intros; nomega.
Qed.
Local Hint Immediate plus_minus_plus_ineq.
Lemma minus_ineq: forall i j x : W, j < x -> i < j -> j ^- $1 < x.
  intros; nomega.
Qed.
Local Hint Immediate minus_ineq.


Lemma wordToNat_ineq: forall (i j:W), i<j -> (wordToNat i < wordToNat j)%nat.
  intros; nomega.
Qed.
Lemma wordNatToNatWord_ineq: forall (i:W) (j:nat), i < $ j -> (wordToNat i < j)%nat.
  intros; auto with list_ineq.
Qed.
Local Hint Resolve wordToNat_ineq  wordNatToNatWord_ineq: list_ineq.
