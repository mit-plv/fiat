Lemma iff_not_iff P Q : (P <-> Q) -> (~ P <-> ~ Q).
Proof.
  split; intros; intuition.
Qed.

