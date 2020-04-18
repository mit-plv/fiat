Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Malloc Coq.Arith.Arith.
Require Import Bedrock.Platform.Cito.GeneralTactics.
Require Import Bedrock.Platform.Cito.MyMalloc.

Definition my_freeS : spec := SPEC("ptr") reserving 8
  PRE[V] Ex ls, array_with_size ls (V "ptr") * mallocHeap 0
  POST[_] mallocHeap 0.

Definition m := bimport[["malloc"!"free" @ [freeS] ]] bmodule "my_free" {{
  bfunction "free"("ptr", "len", "tmp") [my_freeS]
    "tmp" <- "ptr" - 4;;
    "len" <-* "tmp";;
    "len" <- "len" + 2;;
    "tmp" <- "ptr" - 8;;
    Call "malloc"!"free"(0, "tmp", "len")
    [PRE[_, _] mallocHeap 0
     POST[_] mallocHeap 0 ];;
    Return 0
  end
}}.

Set Printing Coercions.

Lemma wplus_ne : forall (a b c : W), a <> b -> a ^- c <> b ^- c.
  intros; destruct (weq (a ^- c) (b ^- c)); eauto.
Qed.

Lemma wminus_0_eq : forall (a b : W), a ^- b = natToW 0 -> a = b.
  intros.
  destruct (weq a b).
  eauto.
  contradict H.
  replace (natToW 0) with (b ^- b).
  eapply wplus_ne; eauto.
  words.
Qed.

Lemma wordToNat_natToW : forall n, goodSize n -> wordToNat (natToW n) = n.
  intros; eapply wordToNat_natToWord_idempotent; eauto.
Qed.

Lemma wminus_wplus : forall a b : W, a ^- b ^+ b = a.
  intros; words.
Qed.

Lemma plus_minus : forall a b, a + b - b = a.
  intros; intuition.
Qed.
Lemma buf_2_bwd : forall p len, (2 <= len)%nat -> p =?> 2 * (p ^+ $8) =?> (len - 2) ===> p =?> len.
  destruct len; simpl; intros; try omega.
  destruct len; simpl; intros; try omega.
  sepLemma; eapply allocated_shift_base; [ words | intuition ].
Qed.
Lemma consume_the_array : forall ls p, array ls p ===> p =?> length ls.
  intros; apply ptsto32m_allocated.
Qed.
Definition hints : TacPackage.
  prepare tt buf_2_bwd.
Defined.
Definition hints2 : TacPackage.
  prepare consume_the_array tt.
Defined.

Theorem ok : moduleOk m.
  vcgen; unfold array_with_size.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  post.
  evaluate auto_ext.
  descend.
  step hints.
  intro.
  eapply wminus_0_eq in H8.
  eauto.
  rewrite wordToNat_natToW.
  eauto.
  eauto.
  assert (2 <= wordToNat (natToW (Datatypes.length x2 + 2)))%nat.
  rewrite wordToNat_natToW.
  eauto.
  eauto.
  step hints.
  rewrite wminus_wplus.
  rewrite wordToNat_natToW.
  rewrite plus_minus.
  step hints2.
  eauto.
  step auto_ext.
  descend.
  step auto_ext.
  step auto_ext.
  step auto_ext.
  step auto_ext.
  step auto_ext.
  step auto_ext.
  step auto_ext.
  words.
  step auto_ext.
  sep_auto.
  sep_auto.
  sep_auto.
Qed.
