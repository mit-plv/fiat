Require Import Coq.omega.Omega.
Require Import Bedrock.Word Bedrock.SepIL Bedrock.IL Bedrock.Memory.


Fixpoint allocated (base : W) (offset len : nat) : HProp :=
  match len with
    | O => Emp
    | S len' => (Ex v, (match offset with
                          | O => base
                          | _ => base ^+ $ (offset)
                        end) =*> v) * allocated base (4+offset) len'
  end%Sep.

Notation "p =?> len" := (allocated p O len) (at level 39) : Sep_scope.

Theorem allocated_extensional : forall base offset len, HProp_extensional (allocated base offset len).
  destruct len; reflexivity.
Qed.

Hint Immediate allocated_extensional.


Lemma Himp_refl : forall p, p ===> p.
  intros; hnf; intros; hnf; intros.
  apply PropX.Imply_I.
  apply PropX.Env.
  simpl; auto.
Qed.

Lemma allocated_shift_base' : forall base base' len offset offset',
  base ^+ $ (offset) = base' ^+ $ (offset')
  -> allocated base offset len ===> allocated base' offset' len.
Proof.
  induction len; intros.

  apply Himp_refl.

  unfold allocated; fold allocated.
  match goal with
    | [ |- context[(?X =*> _)%Sep] ] =>
      assert (X = base ^+ natToW offset)
  end.
  destruct offset; auto.
  W_eq.
  rewrite H0; clear H0.

  match goal with
    | [ |- context[(?X =*> _)%Sep] ] =>
      match X with
        | context[offset'] => assert (X = base' ^+ natToW offset')
      end
  end.
  destruct offset'; auto.
  W_eq.
  rewrite H0; clear H0.

  match goal with
    | [ H : ?X = _ |- context[(?Y =*> _)%Sep] ] => change Y with X; rewrite H
  end.
  intro. apply himp_star_frame. apply himp_ex. reflexivity.
  eapply IHlen. repeat rewrite natToW_plus.
  repeat rewrite (wplus_comm (natToW 4)).
  repeat rewrite wplus_assoc.
  unfold natToW in *. rewrite H. reflexivity.
Qed.

Theorem allocated_shift_base : forall base base' len len' offset offset',
  base ^+ $ (offset) = base' ^+ $ (offset')
  -> len = len'
  -> allocated base offset len ===> allocated base' offset' len'.
  intros; subst; apply allocated_shift_base'; auto.
Qed.

Lemma disjoint'_emp : forall addrs, disjoint' addrs (smem_emp' _) (smem_emp' _).
  induction addrs; simpl; intuition.
Qed.

Lemma join'_emp : forall addrs, smem_emp' _ = join' addrs (smem_emp' _) (smem_emp' _).
  induction addrs; simpl; intuition.
  congruence.
Qed.

Lemma split_empty : forall m, semp m
  -> split m m m.
  unfold semp; intros; subst.
  split.
  apply disjoint'_emp.

  apply join'_emp.
Qed.

Theorem allocated_split : forall base len' len offset,
  (len' <= len)%nat
  -> allocated base offset len ===> allocated base offset len' * allocated base (offset + 4 * len') (len - len').
Proof.
  induction len'; inversion 1.
  { simpl. intro. unfold empB, starB.
    rewrite heq_star_emp_r. reflexivity. }
  { replace (offset + 4 * 0) with offset by omega.
    simpl minus.
    unfold allocated at 2. unfold empB, starB. intro. rewrite heq_star_emp_l. reflexivity. }
  { replace (S len' - S len') with 0 by omega. intro.
    unfold allocated at 3. unfold empB, starB. rewrite heq_star_emp_r. reflexivity. }
  { subst.
    replace (offset + 4 * S len') with ((4 + offset) + 4 * len') by omega.
    unfold allocated at 1 2; fold allocated.
    unfold empB, starB, exB. intro.
    rewrite heq_star_assoc.
    repeat rewrite heq_ex_star.
    apply himp_ex. intros.
    apply himp_star_frame. reflexivity.
    simpl minus. eapply IHlen'. omega. }
Qed.

Theorem allocated_join : forall base len' len offset,
  (len' <= len)%nat
  -> allocated base offset len' * allocated base (offset + 4 * len') (len - len') ===> allocated base offset len.
Proof.
  induction len'; inversion 1.
  { intro; unfold starB, empB; simpl. rewrite heq_star_emp_r. reflexivity. }
  { replace (offset + 4 * 0) with offset by omega.
    simpl minus.
    unfold allocated at 1. unfold empB, starB. intro. rewrite heq_star_emp_l. reflexivity. }
  { replace (S len' - S len') with 0 by omega. intro.
    unfold allocated at 3. unfold empB, starB. rewrite heq_star_emp_r. reflexivity. }
  { subst.
    replace (offset + 4 * S len') with ((4 + offset) + 4 * len') by omega.
    unfold allocated at 1 3; fold allocated.
    unfold empB, starB, exB. intro.
    rewrite heq_star_assoc.
    repeat rewrite heq_ex_star.
    apply himp_ex. intros.
    apply himp_star_frame. reflexivity.
    simpl minus. eapply IHlen'. omega. }
Qed.
