Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep.
Require Import Coq.Lists.List.

Require Import Bedrock.Platform.Cito.SepHintsUtil.

Set Implicit Arguments.

Section TopSection.

  Local Open Scope nat.

  Definition splittable A (ls : list A) pos := pos <= length ls.

  Definition array_to_split ls p (_ : nat) := array ls p.

  Lemma replace_array_to_split : forall ls p pos, array ls p = array_to_split ls p pos.
    eauto.
  Qed.

  Opaque mult.

  Lemma array_split : forall ls p pos, splittable ls pos -> array_to_split ls p pos ===> array (firstn pos ls) p * array (skipn pos ls) (p ^+ $ (4 * pos)).
    intros.
    eapply Himp_trans; [ apply ptsto32m'_in | ].
    eapply Himp_trans; [ | apply Himp_star_frame; apply ptsto32m'_out ].
    apply ptsto32m'_split; auto.
  Qed.

  Definition to_elim (_ : list W) := True.

  Lemma array_elim : forall ls p, to_elim ls -> array ls p ===> p =?> length ls.
    intros.
    eapply Himp_trans; [ apply ptsto32m'_in | ].
    eapply Himp_trans; [ apply ptsto32m'_elim | ].
    replace (p ^+ $0) with p by words.
    apply Himp_refl.
  Qed.

  Definition buf_to_split p len (_ : nat) := (p =?> len)%Sep.

  Definition buf_splittable (len pos : nat) := pos <= len.

  Lemma buf_split_bwd : forall p len pos, buf_splittable len pos -> p =?> pos * (p ^+ $ (4 * pos)) =?> (len - pos) ===> buf_to_split p len pos.
    intros.
    eapply Himp_trans; [ | apply allocated_join ].
    apply Himp_star_frame.
    apply Himp_refl.
    2: auto.
    apply allocated_shift_base; auto.
    rewrite <- wplus_assoc.
    do 2 f_equal.
    rewrite <- natToWord_plus.
    f_equal; omega.
  Qed.

  Definition hints_array_split : TacPackage.
    prepare array_split tt.
  Defined.

  Definition hints_array_elim : TacPackage.
    prepare array_elim tt.
  Defined.

  Definition hints_buf_split_bwd : TacPackage.
    prepare tt buf_split_bwd.
  Defined.

End TopSection.
