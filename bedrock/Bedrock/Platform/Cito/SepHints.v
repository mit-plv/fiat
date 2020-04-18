Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep.

Fixpoint gen_str n : string :=
  match n with
    | O => EmptyString
    | S n' => String "0" (gen_str n')
  end.

Fixpoint gen_ns n :=
  match n with
    | O => nil
    | S n' => gen_str n' :: gen_ns n'
  end.

Lemma gen_ns_len : forall n, length (gen_ns n) = n.
  induction n; simpl; intuition.
Qed.

Lemma gen_str_inj : forall a b, gen_str a = gen_str b -> a = b.
  induction a; induction b; simpl; intuition.
Qed.

Lemma fold_gen_str : forall n, String "0" (gen_str n) = gen_str (S n).
  eauto.
Qed.

Lemma longer_str_not_in : forall r n, (n <= r)%nat -> ~ List.In (gen_str r) (gen_ns n).
  induction r; induction n; simpl; intuition.
  rewrite fold_gen_str in *.
  eapply gen_str_inj in H1.
  intuition.
Qed.

Hint Resolve longer_str_not_in.
Hint Constructors NoDup.

Lemma gen_ns_NoDup : forall n, NoDup (gen_ns n).
  induction n; simpl; intuition.
Qed.

Hint Resolve gen_ns_NoDup.

Lemma behold_the_array_ls : forall len p, p =?> len ===> Ex ls, [| length ls = len |] * array ls p.
  intros; unfold array; rewrite <- (gen_ns_len len); eapply Himp_trans; [ eapply behold_the_array | rewrite gen_ns_len; sepLemma; rewrite length_toArray; rewrite gen_ns_len ]; eauto.
Qed.

Lemma buf_2_fwd : forall p len, (2 <= len)%nat -> p =?> len ===> p =?> 2 * (p ^+ $8) =?> (len - 2).
  destruct len; simpl; intros; try omega.
  destruct len; simpl; intros; try omega.
  sepLemma; eapply allocated_shift_base; [ words | intuition ].
Qed.

Definition hints_buf_2_fwd : TacPackage.
  prepare buf_2_fwd tt.
Defined.

Definition hints_array : TacPackage.
  prepare behold_the_array_ls tt.
Defined.

Definition hints_buf_2_fwd_array : TacPackage.
  prepare (buf_2_fwd, behold_the_array_ls) tt.
Defined.
