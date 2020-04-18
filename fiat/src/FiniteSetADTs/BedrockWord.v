Require Export Fiat.FiniteSetADTs.WordInterface.
Require Export Bedrock.Memory Bedrock.IL.

Set Implicit Arguments.

Module Export BedrockWordW <: BedrockWordT.
  Definition W := Memory.W.

  Definition wzero := (@Word.natToWord 32 0).
  Definition wplus := (@Word.wplus 32).
  Definition wminus := (@Word.wminus 32).
  Definition weq := @Word.weqb 32.

  Definition wlt := IL.wltb.

  Definition from_nat := @Word.natToWord 32.

  Lemma weq_iff x : forall y, x = y <-> weq x y = true.
  Proof.
    symmetry; apply Word.weqb_true_iff.
  Qed.

  Lemma wlt_irrefl x : wlt x x = false.
  Proof.
    unfold wlt, wltb.
    destruct (Word.wlt_dec x x).
    pose proof (Word.lt_le w); congruence.
    reflexivity.
  Qed.

  Lemma wlt_true_iff :
    forall x y,
      wlt x y = true <-> Word.wlt x y.
  Proof.
    intros.
    unfold wlt, IL.wltb.
    destruct (Word.wlt_dec x y); intuition.
  Qed.

  Lemma wlt_false_iff :
    forall x y,
      wlt x y = false <-> ~ Word.wlt x y.
  Proof.
    intros.
    unfold wlt, IL.wltb.
    destruct (Word.wlt_dec x y); intuition.
  Qed.

  Lemma wlt_trans x : forall y z, wlt x y = true -> wlt y z = true -> wlt x z = true.
  Proof.
    intros.
    rewrite wlt_true_iff in *.
    unfold Word.wlt in *.
    eapply BinNat.N.lt_trans; eauto.
  Qed.

  Lemma wle_antisym x : forall y, wlt x y = false -> wlt y x = false -> x = y.
  Proof.
    intros.
    rewrite wlt_false_iff in *.
    unfold Word.wlt in *.
    rewrite BinNat.N.nlt_ge in *.
    apply Word.wordToN_inj.
    apply BinNat.N.le_antisymm; intuition.
  Qed.

  Lemma wle_asym x : forall y, wlt x y = true -> wlt y x = false.
  Proof.
    intro y; rewrite wlt_true_iff, wlt_false_iff.
    unfold Word.wlt.
    apply BinNat.N.lt_asymm.
  Qed.
End BedrockWordW.
