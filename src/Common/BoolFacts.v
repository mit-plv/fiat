Require Import Coq.Strings.String Coq.Arith.Arith Coq.ZArith.BinInt Coq.NArith.BinNat Coq.Bool.Bool.

Section BoolFacts.
  Lemma collapse_ifs_dec :
    forall P (b: {P} + {~P}),
      (if (if b then true else false) then true else false) =
      (if b then true else false).
  Proof.
    destruct b; reflexivity.
  Qed.

  Lemma collapse_ifs_bool :
    forall (b: bool),
      (if (if b then true else false) then true else false) =
      (if b then true else false).
  Proof.
    destruct b; reflexivity.
  Qed.

  Lemma string_dec_bool_true_iff :
    forall s1 s2,
      (if string_dec s1 s2 then true else false) = true <-> s1 = s2.
  Proof.
    intros s1 s2; destruct (string_dec s1 s2); simpl; intuition.
    discriminate.
  Qed.

  Lemma eq_nat_dec_bool_true_iff :
    forall n1 n2,
      (if eq_nat_dec n1 n2 then true else false) = true <-> n1 = n2.
  Proof.
    intros n1 n2; destruct (eq_nat_dec n1 n2); simpl; intuition; discriminate.
  Qed.

  Lemma eq_N_dec_bool_true_iff :
    forall n1 n2 : N, (if N.eq_dec n1 n2 then true else false) = true <-> n1 = n2.
  Proof.
    intros; destruct (N.eq_dec _ _); intuition; discriminate.
  Qed.

  Lemma eq_Z_dec_bool_true_iff :
    forall n1 n2 : Z, (if Z.eq_dec n1 n2 then true else false) = true <-> n1 = n2.
  Proof.
    intros; destruct (Z.eq_dec _ _); intuition; discriminate.
  Qed.

  Lemma bool_equiv_true:
    forall (f g: bool),
      (f = true <-> g = true) <-> (f = g).
  Proof.
    intros f g; destruct f, g; intuition.
  Qed.

  Lemma if_negb :
    forall {A} (b: bool) (x y: A), (if negb b then x else y) = (if b then y else x).
  Proof.
    intros; destruct b; simpl; reflexivity.
  Qed.

  Lemma andb_implication_preserve :
    forall a b, (a = true -> b = true) -> a = b && a.
  Proof. intros; destruct a; destruct b; symmetry; auto. Qed.

  Lemma andb_permute :
    forall a b c, a && (b && c) = b && (a && c).
  Proof.
    intros; repeat rewrite andb_assoc;
    replace (a && b) with (b && a) by apply andb_comm; reflexivity.
  Qed.
End BoolFacts.
