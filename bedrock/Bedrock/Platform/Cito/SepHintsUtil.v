Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep.
Require Import Coq.Lists.List.

Set Implicit Arguments.

Section TopSection.

  Local Open Scope nat.

  Opaque mult.

  Lemma ptsto32m'_out : forall p ls n,
    ptsto32m' nil p n ls ===> ptsto32m nil p n ls.
    induction ls; simpl; intros.
    apply Himp_refl.
    eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl
      | apply IHls ] | ].
    destruct ls; simpl in *.
    destruct n.
    replace (p ^+ $0) with p by words.
    eapply Himp_trans; [ apply Himp_star_comm | ].
    apply Himp_star_Emp.
    eapply Himp_trans; [ apply Himp_star_comm | ].
    apply Himp_star_Emp.
    destruct n; simpl.
    replace (p ^+ $0) with p by words.
    apply Himp_refl.
    apply Himp_refl.
  Qed.

  Lemma ptsto32m'_in : forall p ls n,
    ptsto32m nil p n ls ===> ptsto32m' nil p n ls.
    induction ls; simpl; intros.
    apply Himp_refl.
    eapply Himp_trans; [ | apply Himp_star_frame; [ apply Himp_refl
      | apply IHls ] ].
    destruct ls; simpl in *.
    destruct n.
    replace (p ^+ $0) with p by words.
    eapply Himp_trans; [ | apply Himp_star_comm ].
    apply Himp_star_Emp'.
    eapply Himp_trans; [ | apply Himp_star_comm ].
    apply Himp_star_Emp'.
    destruct n; simpl.
    replace (p ^+ $0) with p by words.
    apply Himp_refl.
    apply Himp_refl.
  Qed.

  Lemma ptsto32m'_split' : forall p ls2 ls1 base,
    ptsto32m' nil p base (ls1 ++ ls2) ===>
    star (ptsto32m' nil p base ls1)
    (ptsto32m' nil (p ^+ $ (4 * length ls1)) base ls2).
    induction ls1; simpl; intros.

    change (4 * 0) with 0.
    replace (p ^+ $0) with p by words.
    apply Himp_star_Emp'.

    eapply Himp_trans; [ apply Himp_star_frame; [
      apply Himp_refl | apply IHls1 ] | ].
    sepLemma.
    eapply Himp_trans; [ apply ptsto32m'_shift_base' | ].
    instantiate (1 := 4).
    auto.
    apply Himp_refl'; f_equal; try omega.
    unfold natToW.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.
    do 2 f_equal.
    auto.
  Qed.

  Lemma ptsto32m'_split : forall p ls pos base,
    pos <= length ls
    -> ptsto32m' nil p base ls ===>
    star (ptsto32m' nil p base (firstn pos ls))
    (ptsto32m' nil (p ^+ $ (4 * pos)) base (skipn pos ls)).
    intros.
    pattern ls at 1.
    replace ls with (firstn pos ls ++ skipn pos ls).
    replace (4 * pos) with (4 * length (firstn pos ls)).
    apply ptsto32m'_split'.
    rewrite firstn_length.
    rewrite Min.min_l; auto.
    apply firstn_skipn.
  Qed.

  Lemma ptsto32m'_elim : forall p ls base,
    ptsto32m' nil p base ls ===> (p ^+ $ base) =?> length ls.
    induction ls; simpl; intros.

    apply Himp_refl.

    apply Himp_star_frame.
    sepLemma.
    eapply Himp_trans; [ | apply allocated_shift_base ].
    eapply Himp_trans; [ | apply IHls ].
    apply Himp_refl.
    do 2 rewrite <- wplus_assoc.
    do 2 rewrite <- natToWord_plus.
    do 2 f_equal.
    omega.
    auto.
  Qed.

End TopSection.
