Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Malloc Coq.Arith.Arith.
Require Import Bedrock.Platform.Cito.GeneralTactics.

Set Printing Coercions.

Definition array_with_size ls p : HProp := let len := length ls in ([| p <> $8 /\ freeable (p ^- $8) (len + 2) /\ goodSize (len + 2) |] * (p ^- $8) =?> 1 * (p ^- $4) =*> natToW len * array ls p)%Sep.

Definition my_mallocS : spec := SPEC("n") reserving 8
  PRE[V] [| goodSize (wordToNat (V "n") + 2) |] * mallocHeap 0
  POST[R] Ex ls, [| length ls = wordToNat (V "n") |] * array_with_size ls R * mallocHeap 0.

Definition m := bimport[["malloc"!"malloc" @ [mallocS] ]] bmodule "my_malloc" {{
  bfunction "malloc"("n", "tmp") [my_mallocS]
    "tmp" <- "n" + 2;;
    "tmp" <-- Call "malloc"!"malloc"(0, "tmp")
    [PRE[V,R] [| goodSize (wordToNat (V "n") + 2) |] * [| R <> 0 |] * [| freeable R (wordToNat (V "n" ^+ $2)) |] * R =?> 2 * (R ^+ $8) =?> wordToNat (V "n")
     POST[R'] Ex ls, [| length ls = wordToNat (V "n") |] * array_with_size ls R' ];;
    "tmp" + 4 *<- "n";;
    Return "tmp" + 8
  end
}}.

Lemma wplus_ne : forall (a b c : W), a <> b -> a ^+ c <> b ^+ c.
  intros; destruct (weq (a ^+ c) (b ^+ c)); eauto.
Qed.

Lemma wplus_ne_0 : forall (a c : W), a <> 0 -> a ^+ c <> c.
  intros; pattern c at 2; replace c with ($0 ^+ c); [ eapply wplus_ne; eauto | words ].
Qed.

Hint Resolve wplus_ne_0.

Lemma wplus_wminus : forall (a b : W), a ^+ b ^- b = a.
  intros; words.
Qed.

Lemma roundTrip_2 : wordToNat (natToW 2) = 2.
  compute; auto.
Qed.

Lemma wordToNat_wplus_2 : forall (w : W), goodSize (wordToNat w + 2) -> wordToNat (w ^+ natToW 2) = wordToNat w + 2.
  intros; eapply wordToNat_wplus; rewrite roundTrip_2; eauto.
Qed.

Lemma goodSize_le_wordToNat_wplus : forall w : W, goodSize (wordToNat w + 2) -> (2 <= wordToNat (w ^+ natToW 2))%nat.
  intros; pre_nomega; rewrite wordToNat_wplus_2 by eauto; omega.
Qed.

Hint Resolve goodSize_le_wordToNat_wplus.

Lemma goodSize_le_wplus : forall w : W, goodSize (wordToNat w + 2) -> natToW 2 <= w ^+ natToW 2.
  intros; pre_nomega; rewrite roundTrip_2; eauto.
Qed.

Hint Resolve goodSize_le_wplus.

Ltac tag :=
  match goal with
    H : goodSize (_ + 2) |- _ => generalize H; eapply goodSize_le_wordToNat_wplus in H; intro
  end.

Lemma wplus_minus_2 : forall (w : W), goodSize (wordToNat w + 2) -> wordToNat (w ^+ $2) - 2 = wordToNat w.
  intros; rewrite wordToNat_wplus_2 by eauto; intuition.
Qed.

Lemma buf_2_fwd : forall p len, (2 <= len)%nat -> p =?> len ===> p =?> 2 * (p ^+ $8) =?> (len - 2).
  destruct len; simpl; intros; try omega.
  destruct len; simpl; intros; try omega.
  sepLemma; eapply allocated_shift_base; [ words | intuition ].
Qed.

Definition hints : TacPackage.
  prepare buf_2_fwd tt.
Defined.

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

Lemma fold_gen_str : forall n, String "0" (gen_str n) = gen_str (S n).
  eauto.
Qed.

Lemma gen_str_inj : forall a b, gen_str a = gen_str b -> a = b.
  induction a; induction b; simpl; intuition.
Qed.

Lemma longer_str_not_in : forall r n, (n <= r)%nat -> ~ In (gen_str r) (gen_ns n).
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

Definition hints2 : TacPackage.
  prepare behold_the_array_ls tt.
Defined.

Theorem m_ok : moduleOk m.
  vcgen; unfold array_with_size.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  post; evaluate hints; descend; tag; repeat (try rewrite wplus_minus_2 by eauto; step hints); eauto; words.
  sep_auto.
  sep_auto.
  sep hints2; rewriter; [ | rewrite wplus_wminus; rewrite wordToNat_wplus_2 in * | unfold natToW; rewrite natToWord_wordToNat; step hints2 ]; eauto.
Qed.
