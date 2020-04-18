Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep.

Set Implicit Arguments.

Lemma wordToNat_positive : forall w : W,
  ($0 < w)%word
  -> wordToNat w = S (wordToNat (w ^- $1)).
  intros.
  replace (wordToNat w) with (wordToNat ($1 ^+ (w ^- $1))) by (f_equal; words).
  rewrite wordToNat_wplus; auto.
  assert ($1 <= w)%word.
  pre_nomega.
  change (wordToNat $0) with 0 in *.
  change (wordToNat $1) with 1.
  omega.
  rewrite wordToNat_wminus; auto.
  change (wordToNat $1) with 1.
  replace (1 + (wordToNat w - 1)) with (wordToNat w); auto.
  nomega.
Qed.
