Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep.


Definition div4S := SPEC("n") reserving 1
  Al m,
  PRE[V] [| wordToNat (V "n") = m * 4 |]%nat
  POST[R] [| wordToNat R = m |].

Definition m := bmodule "numops" {{
  bfunction "div4"("n", "acc") [div4S]
    "acc" <- 0;;

    [Al m,
      PRE[V] [| wordToNat (V "n") = m * 4 |]%nat
      POST[R] [| R = natToW m ^+ V "acc" |] ]
    While ("n" >= 4) {
      "acc" <- "acc" + 1;;
      "n" <- "n" - 4
    };;

    Return "acc"
  end
}}.

Section ok.
  Lemma use_pred : forall (w : W) n,
    wordToNat w = n * 4
    -> natToW 4 <= w
    -> wordToNat w - 4 = (pred n) * 4.
    intros.
    nomega.
  Qed.

  Hint Immediate use_pred.

  Lemma roundTrip_4 : wordToNat (natToW 4) = 4.
    auto.
  Qed.

  Hint Rewrite roundTrip_4 : N.

  Lemma cancel_pred : forall n m rv acc,
    natToW 4 <= n
    -> wordToNat n = m * 4
    -> rv = natToW (pred m) ^+ (acc ^+ natToW 1)
    -> rv = natToW m ^+ acc.
    intros; subst.
    rewrite Minus.pred_of_minus.
    rewrite natToW_minus by nomega; words.
  Qed.

  Hint Immediate cancel_pred.

  Lemma finish : forall rv acc n m,
    rv = acc
    -> n < natToW 4
    -> wordToNat n = m * 4
    -> rv = natToW m ^+ acc.
    intros; subst.
    assert (m0 = 0) by nomega.
    words.
  Qed.

  Hint Immediate finish.
  Hint Rewrite <- plus_n_O : sepFormula.

  Lemma switch_up : forall (w : W) n rv,
    wordToNat w = n * 4
    -> rv = natToW n
    -> wordToNat rv = n.
    intros; subst.
    apply wordToNat_natToWord_idempotent.
    change (goodSize n).
    eapply goodSize_weaken.
    instantiate (1 := wordToNat w).
    eauto.
    omega.
  Qed.

  Hint Immediate switch_up.

  Theorem ok : moduleOk m.
    vcgen; abstract (sep_auto; eauto).
  Qed.
End ok.
