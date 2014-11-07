Require Import Memory IL.

Lemma weqb_false_iff :
  forall {sz} (w1 w2: @Word.word sz),
    Word.weqb w1 w2 = false <-> w1 <> w2.
Proof.
  split; try rewrite <- Word.weqb_true_iff in *; try congruence.
  destruct (Word.weqb w1 w2); intuition.
Qed.

Lemma weqb_false :
  forall w1 w2,
    w1 <> w2 ->
    IL.weqb w1 w2 = false.
Proof.
  setoid_rewrite <- weqb_false_iff.
  intros; assumption.
Qed.

Lemma weqb_refl :
  forall sz w,
    @Word.weqb sz w w = true.
Proof.
  induction w.
  
  reflexivity.
  destruct b; simpl; rewrite IHw; reflexivity.
Qed.

Definition BoolToW (b: bool) := if b then (Word.natToWord 32 1) else (Word.natToWord 32 0).

Definition WToBool (w: @Word.word 32) := negb (Word.weqb w (Word.natToWord 32 0)).

Lemma BoolToW_invert : forall b, WToBool (BoolToW b) = b.
Proof.
  destruct b; intuition.
Qed.
