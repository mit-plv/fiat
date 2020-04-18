Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep.


Lemma allocate_array' : forall p n offset,
  allocated p offset n ===> Ex ls, [| length ls = n |] * array ls (p ^+ $ (offset)).
  induction n; simpl.

  sepLemma.
  instantiate (1 := nil); auto.
  sepLemma.

  intros; sepLemmaLhsOnly.
  etransitivity; [ eapply himp_star_frame; [ apply IHn | reflexivity ] | ]; clear IHn.
  sepLemmaLhsOnly.
  apply himp_ex_c; exists (x :: x0).
  sepLemma.
  etransitivity; [ eapply himp_star_frame; [ apply Arrays.ptsto32m'_in | reflexivity ] | ].
  etransitivity; [ | apply ptsto32m'_out ].
  simpl.
  destruct offset; simpl.
  replace (p ^+ natToW 0) with p by words; sepLemma.
  etransitivity; [ | apply ptsto32m'_shift_base ].
  instantiate (1 := 4); reflexivity.
  auto.
  replace (p ^+ natToW (S offset) ^+ $0) with (p ^+ natToW (S offset)) by words.
  sepLemma.
  etransitivity; [ | apply ptsto32m'_shift_base ].
  instantiate (1 := 4).
  rewrite <- wplus_assoc.
  rewrite <- natToW_plus.
  replace (S offset + 4) with (S (S (S (S (S offset))))) by omega.
  reflexivity.
  auto.
Qed.

Inductive make_array : Prop := MakeArray.

Hint Constructors make_array.

Lemma allocate_array : forall p n,
  p = p
  -> make_array
  -> p =?> n ===> Ex ls, [| length ls = n |] * array ls p.
  intros; eapply Himp_trans; [ apply allocate_array' | ].
  replace (p ^+ $0) with p by words; apply Himp_refl.
Qed.

Lemma free_array' : forall p n offset,
  Ex ls, [| length ls = n |] * array ls (p ^+ $ (offset)) ===> allocated p offset n.
  sepLemma.
  etransitivity; [ apply ptsto32m_allocated | ].
  etransitivity; [ apply allocated_shift_base | ].
  3: sepLemma.
  unfold natToW; W_eq.
  auto.
Qed.

Inductive dissolve_array : Prop := DissolveArray.

Hint Constructors dissolve_array.

Lemma free_array : forall p n,
  p = p
  -> dissolve_array
  -> Ex ls, [| length ls = n |] * array ls p ===> p =?> n.
  intros; eapply Himp_trans; [ | apply free_array' ].
  replace (p ^+ $0) with p by words; apply Himp_refl.
Qed.

Lemma selN_updN_eq : forall v a n,
  (n < length a)%nat
  -> Array.selN (Array.updN a n v) n = v.
  induction a; destruct n; simpl; intuition.
Qed.

Lemma selN_upd_eq : forall v a n,
  (n < length a)%nat
  -> goodSize (length a)
  -> Array.selN (Array.upd a (natToW n) v) n = v.
  intros; rewrite upd_updN.
  apply selN_updN_eq; auto.
  eauto using goodSize_weaken.
Qed.

Lemma inc : forall n (w : W) l,
  n = wordToNat l
  -> w < natToW n
  -> w ^+ natToW 1 <= l.
  intros; subst.
  assert (exists b, w < b) by eauto.
  pre_nomega.
  destruct H.
  erewrite <- next; eauto.
  unfold natToW in *; rewrite natToWord_wordToNat in *.
  auto.
Qed.

Theorem natToW_wordToNat : forall w : W,
  natToW (wordToNat w) = w.
  intros; apply natToWord_wordToNat.
Qed.

Theorem wordToNat_inj : forall sz (u v : word sz),
  wordToNat u = wordToNat v
  -> u = v.
  intros; rewrite <- (natToWord_wordToNat u); rewrite <- (natToWord_wordToNat v); congruence.
Qed.

Ltac match_locals :=
  match goal with
    | [ _ : context[locals ?NS ?X _ _] |- context[locals ?NS ?Y _ _] ] => equate X Y
  end; descend.

Local Hint Extern 1 (@eq W _ _) => words.
