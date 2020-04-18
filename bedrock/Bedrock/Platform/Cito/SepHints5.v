Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.Cito.SepHintsUtil Bedrock.Platform.Cito.SepHints2.

Set Implicit Arguments.

Section TopSection.

  Lemma split_buf : forall p len pos, buf_splittable len pos -> buf_to_split p len pos ===> p =?> pos * (p ^+ $ (4 * pos)) =?> (len - pos).
    unfold buf_splittable, buf_to_split; intros.
    eapply Himp_trans; [ apply allocated_split | ].
    eassumption.
    apply Himp_star_frame; try apply Himp_refl.
    apply allocated_shift_base; auto.
    rewrite <- wplus_assoc.
    do 2 f_equal.
    rewrite <-natToW_plus.
    unfold natToW; f_equal.
    omega.
  Qed.

  Definition hints_split_buf : TacPackage.
    prepare split_buf tt.
  Defined.

  Definition to_intro_array (_ : W) := True.

  Lemma intro_array' : forall p len base,
    (p ^+ natToW base) =?> len ===>
    Ex ls, [| length ls = len |] * ptsto32m' nil p base ls.
    induction len; simpl; intros.
    apply Himp_ex_c; exists nil.
    sepLemma.

    eapply Himp_trans; [ apply Himp_star_frame; [
      apply Himp_refl | apply allocated_shift_base ] | ].
    3: eapply Himp_trans; [ apply Himp_star_frame; [
      apply Himp_refl | apply IHlen ] | ].
    instantiate (1 := base + 4).
    do 2 rewrite <- wplus_assoc.
    do 2 rewrite <- natToWord_plus.
    do 2 f_equal; omega.
    auto.
    eapply Himp_trans; [ apply Himp_ex_star | ].
    eapply Himp'_ex; intro x.
    eapply Himp_trans; [ apply Himp_star_comm | ].
    eapply Himp_trans; [ apply Himp_ex_star | ].
    eapply Himp'_ex; intro xs.
    apply Himp_ex_c; exists (x :: xs).
    sepLemma.
    replace (base + 4) with (S (S (S (S base)))) by omega.
    reflexivity.
  Qed.

  Lemma intro_array : forall len p, to_intro_array p -> p =?> len ===> Ex ls, [| length ls = len |] * array ls p.
    intros.
    replace (p =?> len)%Sep with ((p ^+ natToW 0) =?> len)%Sep.
    eapply Himp_trans; [ apply intro_array' | ].
    apply Himp_ex; intros.
    apply Himp_star_frame.
    apply Himp_refl.
    apply ptsto32m'_out.
    repeat f_equal; words.
  Qed.

  Definition combined_locals vars1 vars2 vs1 vs2 p  := locals (vars1 ++ vars2) (merge vs1 vs2 vars1) 0 p.

  Lemma fold_combined_locals : forall vars1 vars2 vs1 vs2 p, locals (vars1 ++ vars2) (merge vs1 vs2 vars1) 0 p = combined_locals vars1 vars2 vs1 vs2 p.
    eauto.
  Qed.

  Definition locals_combinable A (vars vars2 : list A) := NoDup (vars ++ vars2).

  Opaque mult.

  Lemma combine_locals : forall vars1 vars2 vs1 vs2 p,
    locals_combinable vars1 vars2
    -> locals vars1 vs1 0 p * locals vars2 vs2 0 (p ^+ $ (4 * length vars1)) ===> combined_locals vars1 vars2 vs1 vs2 p.
    unfold locals, locals_combinable; sepLemma.
    unfold combined_locals, locals.
    sepLemma.
    eapply Himp_trans; [ | apply ptsto32m'_out ].
    eapply Himp_trans; [ | apply ptsto32m'_merge ].
    2: auto.
    eapply Himp_trans; [ apply Himp_star_frame; apply SepHintsUtil.ptsto32m'_in | ].
    apply Himp_star_frame.
    apply Himp_refl.
    eapply Himp_trans; [ | eapply ptsto32m'_shift_base ].
    instantiate (2 := 4 * length vars1).
    replace (0 + 4 * length vars1 - 4 * length vars1) with 0 by omega.
    apply Himp_refl.
    omega.
    apply agree_on_refl.
  Qed.

  Definition hints_intro_array : TacPackage.
    prepare intro_array tt.
  Defined.

  Definition hints_combine_locals : TacPackage.
    prepare tt combine_locals.
  Defined.

  Definition locals_to_split vars1 vars2 vs p := locals (vars1 ++ vars2) vs 0 p.

  Lemma fold_locals_to_split : forall vars1 vars2 vs p, locals (vars1 ++ vars2) vs 0 p = locals_to_split vars1 vars2 vs p.
    eauto.
  Qed.

  Lemma split_locals : forall vars1 vars2 vs p, locals_to_split vars1 vars2 vs p ===> locals vars1 vs 0 p * locals vars2 vs 0 (p ^+ $ (4 * length vars1)).
    unfold locals_to_split, locals; intros.
    sepLemma.
    eauto using NoDup_unapp1.
    eauto using NoDup_unapp2.
    eapply Himp_trans; [ apply SepHintsUtil.ptsto32m'_in | ].
    eapply Himp_trans; [ | apply Himp_star_frame; apply SepHintsUtil.ptsto32m'_out ].
    eapply Himp_trans; [ apply ptsto32m'_split | ].
    apply Himp_star_frame; try apply Himp_refl.
    eapply Himp_trans; [ apply ptsto32m'_shift_base' | ].
    Focus 2.
    apply Himp_refl'; f_equal.
    omega.
    omega.
  Qed.

  Definition hints_split_locals : TacPackage.
    prepare split_locals tt.
  Defined.

End TopSection.
