Require Import Bedrock.Memory.

Lemma lt_BinNat_lt:
  forall (p p' : nat),
    lt p p' ->
    BinNat.N.lt (BinNat.N.of_nat p) (BinNat.N.of_nat p').
Proof.
  intros; Nomega.nomega.
Qed.

Lemma BinNat_lt_S:
  forall (p p' : nat),
    BinNat.N.lt (BinNat.N.of_nat p) (BinNat.N.of_nat p') ->
    BinNat.N.lt (BinNat.N.of_nat (S p)) (BinNat.N.of_nat (S p')).
Proof.
  intros; Nomega.nomega.
Qed.

Lemma BinNat_lt_of_nat_S:
  forall (p : nat) (q : BinNums.N),
    BinNat.N.lt (BinNat.N.of_nat (S p)) q ->
    BinNat.N.lt (BinNat.N.of_nat p) q.
Proof.
  intros; Nomega.nomega.
Qed.

Lemma BinNat_lt_Fin_to_nat:
  forall (N : nat) (idx : Fin.t N),
    BinNat.N.lt (BinNat.N.of_nat (projT1 (Fin.to_nat idx))) (BinNat.N.of_nat N).
Proof.
  intros.
  pose proof (projT2 (Fin.to_nat idx)).
  Nomega.nomega.
Qed.
