Require Export Bedrock.Word.
Require Import Fiat.Common.DecideableEnsembles.

Lemma wordToNat_lt sz
  : forall w w' : word sz,
    wlt w w' ->
    lt (wordToNat w) (wordToNat w').
Proof.
  intros.
  unfold wlt, BinNat.N.lt in H.
  rewrite !wordToN_nat, <- Nnat.Nat2N.inj_compare,
  <- Compare_dec.nat_compare_lt in H.
  eassumption.
Qed.

Lemma natToWord_wlt sz
  : forall n n' : nat,
    BinNat.N.lt (BinNat.N.of_nat n) (Npow2 sz)
    -> BinNat.N.lt (BinNat.N.of_nat n') (Npow2 sz)
    -> lt n n'
    -> wlt (natToWord sz n) (natToWord sz n').
Proof.
  unfold wlt; intros.
  rewrite !wordToN_nat.
  rewrite !wordToNat_natToWord_idempotent; eauto.
  unfold BinNat.N.lt; rewrite <- Nnat.Nat2N.inj_compare.
  eapply Compare_dec.nat_compare_lt; eassumption.
Qed.

Instance Query_eq_word {n} : Query_eq (Word.word n) :=
  {| A_eq_dec := @Word.weq n |}.
