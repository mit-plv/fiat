Require Export Fiat.FiniteSetADTs.WordInterface.

Set Implicit Arguments.

Module Export BedrockWord : BedrockWordT.
  Definition W := nat.
  Definition wzero := 0.
  Definition wplus := plus.
  Definition wminus := minus.
  Definition from_nat (x : nat) := x.
  Fixpoint weq (x : nat) (y : nat) : bool :=
    match x, y with
      | 0, 0 => true
      | 0, S _ => false
      | S _, 0 => false
      | S x', S y' => weq x' y'
    end.
  Fixpoint wlt (x : nat) (y : nat) : bool :=
    match x, y with
      | 0, 0 => false
      | 0, S _ => true
      | S _, 0 => false
      | S x', S y' => wlt x' y'
    end.
  Lemma weq_iff x : forall y, x = y <-> weq x y = true.
  Proof.
    induction x; intro y; destruct y;
    split; simpl;
    intro H;
    first [ reflexivity
          | exfalso; revert H; clear; intro H; abstract inversion H
          | apply (f_equal pred) in H; simpl in H; apply IHx; assumption
          | apply (f_equal S); apply IHx; assumption ].
  Qed.
  Lemma wlt_irrefl x : wlt x x = false.
  Proof.
    induction x; simpl; congruence.
  Qed.
  Lemma wlt_trans x : forall y z, wlt x y = true -> wlt y z = true -> wlt x z = true.
  Proof.
    induction x; intros [|?] [|?]; simpl; intros;
    try congruence.
    eapply IHx; eassumption.
  Qed.
  Lemma wle_antisym x : forall y, wlt x y = false -> wlt y x = false -> x = y.
  Proof.
    induction x; intros [|?]; intros; simpl in *;
    try congruence.
    apply f_equal.
    eapply IHx; eassumption.
  Qed.
  Lemma wle_asym x : forall y, wlt x y = true -> wlt y x = false.
  Proof.
    induction x; intros [|?]; simpl; intros;
    try congruence.
    eapply IHx; eassumption.
  Qed.
End BedrockWord.
