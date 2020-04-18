Require Import Memory.
Require Import Word.

Lemma weqb_complete (x y : W) : x = y -> Word.weqb x y = true.
Proof.
  intros; subst.
  eapply weqb_true_iff; eauto.
Qed.

Lemma weqb_false_intro (x y : W) : x <> y -> weqb x y = false.
Proof.
  intros H.
  destruct (Sumbool.sumbool_of_bool (weqb x y)) as [Heq | Heq]; trivial.
  eapply weqb_true_iff in Heq; subst.
  intuition.
Qed.

