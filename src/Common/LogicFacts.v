Section LogicFacts.
  Lemma or_false :
    forall (P: Prop), P \/ False <-> P.
  Proof.
    tauto.
  Qed.

  Lemma false_or :
    forall (P Q: Prop),
      (False <-> P \/ Q) <-> (False <-> P) /\ (False <-> Q).
  Proof.
    tauto.
  Qed.

  Lemma false_or' :
    forall (P Q: Prop),
      (P \/ Q <-> False) <-> (False <-> P) /\ (False <-> Q).
  Proof.
    tauto.
  Qed.

  Lemma equiv_false :
    forall P,
      (False <-> P) <-> (~ P).
  Proof.
    tauto.
  Qed.

  Lemma equiv_false' :
    forall P,
      (P <-> False) <-> (~ P).
  Proof.
    tauto.
  Qed.

  Lemma and_True :
    forall P,
      (P /\ True) <-> P.
  Proof.
    tauto.
  Qed.

  Lemma not_exists_forall :
    forall {A} (P: A -> Prop),
      (~ (exists a, P a)) <-> (forall a, ~ P a).
  Proof.
    firstorder.
  Qed.

  Lemma not_and_implication :
    forall (P Q: Prop),
      ( ~ (P /\ Q) ) <-> (P -> ~ Q).
  Proof.
    firstorder.
  Qed.

  Lemma eq_sym_iff :
    forall {A} x y, @eq A x y <-> @eq A y x.
  Proof.
    split; intros; symmetry; assumption.
  Qed.
End LogicFacts.
