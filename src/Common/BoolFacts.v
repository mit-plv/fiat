Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Arith.Arith Coq.ZArith.BinInt Coq.NArith.BinNat Coq.Bool.Bool.

Module Export Bool.
  Delimit Scope boolr_scope with boolr.
  Definition orbr (b1 b2 : bool) := if b2 then true else b1.
  Definition andbr (b1 b2 : bool) := if b2 then b1 else false.
  Global Arguments orbr _ !_ / .
  Global Arguments andbr _ !_ / .
  Infix "||" := orbr : boolr_scope.
  Infix "&&" := andbr : boolr_scope.
End Bool.

Section BoolFacts.
  Lemma orbr_orb b1 b2 : orbr b1 b2 = orb b1 b2.
  Proof. destruct b1, b2; reflexivity. Qed.
  Lemma andbr_andb b1 b2 : andbr b1 b2 = andb b1 b2.
  Proof. destruct b1, b2; reflexivity. Qed.
  Lemma fold_left_andb_andbr ls
    : forall b, List.fold_left andbr ls b = List.fold_left andb ls b.
  Proof.
    induction ls; simpl; trivial.
    intro; rewrite IHls, andbr_andb.
    reflexivity.
  Qed.
  Lemma fold_left_orb_orbr ls
    : forall b, List.fold_left orbr ls b = List.fold_left orb ls b.
  Proof.
    induction ls; simpl; trivial.
    intro; rewrite IHls, orbr_orb.
    reflexivity.
  Qed.

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

  Lemma ascii_dec_bool_true_iff :
    forall s1 s2,
      (if ascii_dec s1 s2 then true else false) = true <-> s1 = s2.
  Proof.
    intros s1 s2; destruct (ascii_dec s1 s2); simpl; intuition.
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

  Lemma bool_rect_andb x y z
  : bool_rect (fun _ => bool) x y z
    = orb (andb (negb z) y) (andb z x).
  Proof.
    destruct x, y, z; reflexivity.
  Qed.

  Lemma andb_orb_distrib_r_assoc
  : forall b1 b2 b3 b4 : bool, ((b1 && (b2 || b3)) || b4)%bool = (b1 && b2 || ((b1 && b3) || b4))%bool.
  Proof.
    repeat intros []; reflexivity.
  Qed.
End BoolFacts.
