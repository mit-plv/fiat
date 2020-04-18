Require Import Coq.Lists.List.
Require Import Bedrock.sep.Array.

Set Implicit Arguments.

Fixpoint upd_sublist big base small :=
  match small with
    | nil => big
    | x :: xs => upd_sublist (updN big base x) (1 + base) xs
  end.

Lemma length_updN : forall a b c, length (updN a b c) = length a.
  induction a; simpl; intuition.
  destruct b; simpl; auto.
Qed.

Lemma length_upd_sublist' : forall b a n, length (upd_sublist a n b) = length a.
  induction b; simpl; intuition.
  rewrite IHb.
  apply length_updN.
Qed.

Lemma length_upd_sublist : forall a n b, length (upd_sublist a n b) = length a.
  auto using length_upd_sublist'.
Qed.
