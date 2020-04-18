Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep.
Require Import Bedrock.Platform.Cito.SyntaxExpr.

Require Import Bedrock.StringSet.
Import StringSet.
Require Import Coq.FSets.FSetProperties.
Module Import SSP := Properties StringSet.

Set Implicit Arguments.

Section TopLevel.

  Variable vars : list string.

  Variable temp_size : nat.

  Variable exprs : list Expr.

  Variable base dst : nat.

  Definition is_state sp vs temps dst dst_buf : HProp :=
    (locals vars vs 0 (sp ^+ $8) *
     array temps (sp ^+ $8 ^+ $ (4 * length vars)) *
     array dst_buf (sp ^+ $ dst))%Sep.

  Definition new_pre : assert :=
    x ~> ExX, Ex vs, Ex temps, Ex dst_buf,
    ![^[is_state x#Sp vs temps dst dst_buf] * #0]x /\
    [| length temps = temp_size /\
       length exprs = length dst_buf |].

  Require Import Bedrock.Platform.Cito.SemanticsExpr.
  Require Import Bedrock.Platform.Cito.DepthExpr.
  Require Import Bedrock.Platform.Cito.Max.

  Definition depth := max_list 0 (map depth exprs).

  Require Bedrock.Platform.Cito.CompileExpr.
  Require Import Bedrock.Platform.Cito.ListFacts5.

  Local Open Scope nat.

  Definition runs_to x_pre x :=
    forall specs other vs temps dst_buf,
      interp specs (![is_state x_pre#Sp vs temps dst dst_buf * other ] x_pre)
      -> length temps = temp_size
      -> length exprs = length dst_buf
      -> Regs x Sp = x_pre#Sp /\
      exists changed,
        interp specs (![is_state (Regs x Sp) vs (upd_sublist temps base changed) dst (map (eval vs) exprs) * other ] (fst x_pre, x)) /\
        length changed <= depth.

  Definition post (pre : assert) :=
    st ~> Ex st_pre,
    pre (fst st, st_pre) /\
    [| runs_to (fst st, st_pre) (snd st) |].

  Definition imply (pre new_pre: assert) := forall specs x, interp specs (pre x) -> interp specs (new_pre x).

  Require Import Bedrock.Platform.Cito.FreeVarsExpr.
  Require Import Bedrock.Platform.Cito.Union.

  Definition syn_req exprs base :=
    Subset (union_list (map free_vars exprs)) (of_list vars) /\
    base + depth <= temp_size /\
    List.Forall (fun e => DepthExpr.depth e <= depth) exprs.

  Definition verifCond base pre := imply pre new_pre :: syn_req exprs base :: nil.

  Variable imports : LabelMap.t assert.

  Variable imports_global : importsGlobal imports.

  Variable modName : string.

  Definition Seq2 := @Seq_ _ imports_global modName.

  Definition Skip := Straightline_ imports modName nil.

  Fixpoint Seq ls :=
    match ls with
      | nil => Skip
      | a :: ls' => Seq2 a (Seq ls')
    end.

  Definition Strline := Straightline_ imports modName.

  Definition SaveRv lv := Strline (IL.Assign lv (RvLval (LvReg Rv)) :: nil).

  Definition stack_slot (n : nat) := LvMem (Sp + n)%loc.

  Definition compile_expr e n := CompileExpr.compile vars temp_size imports_global modName e n.

  Fixpoint do_compile exprs base dst :=
    match exprs with
      | nil => nil
      | x :: xs =>
        compile_expr x base
          :: SaveRv (stack_slot dst)
          :: do_compile xs base (4 + dst)
    end.

  Definition body := Seq (do_compile exprs base dst).

  Require Import Bedrock.Platform.Wrap.

  Opaque mult.
  Opaque evalInstrs.

  Lemma array_out : forall a p,
    length a > 0
    -> array a p ===> p =*> Array.selN a 0 * array (tl a) (p ^+ $4).
    clear_fancy; destruct a; unfold array; simpl; intros.
    inversion H.
    destruct a.
    sepLemma.
    apply Himp_star_frame; try apply Himp_refl.
    eapply Himp_trans; [ apply ptsto32m_shift_base' | ].
    instantiate (1 := 4); auto.
    apply Himp_refl.
  Qed.

  Lemma change_hyp : forall P Q specs st,
    interp specs (![P] st)
    -> P ===> Q
    -> interp specs (![Q] st).
    intros.
    eapply Imply_sound.
    rewrite sepFormula_eq.
    apply H0.
    rewrite sepFormula_eq in *; auto.
  Qed.

  Lemma array_in : forall a p,
    length a > 0
    -> p =*> Array.selN a 0 * array (tl a) (p ^+ $4) ===> array a p.
    clear_fancy; destruct a; unfold array; simpl; intros.
    inversion H.
    destruct a.
    sepLemma.
    apply Himp_star_frame; try apply Himp_refl.
    eapply Himp_trans; [ | apply ptsto32m_shift_base ].
    instantiate (1 := 4); auto.
    apply Himp_refl.
    auto.
  Qed.

  Lemma In_union_list : forall x exprs0,
    In x (fold_right union empty (map free_vars exprs0))
    -> In x (fold_right union empty (map free_vars exprs0)).
    induction exprs0; simpl; intuition.
  Qed.

  Lemma postOk : forall specs exprs base dst pre x,
    interp specs (Postcondition (Seq (do_compile exprs base dst) pre) x)
    -> imply pre (x ~> ExX, Ex vs, Ex temps, Ex dst_buf,
      ![^[is_state x#Sp vs temps dst dst_buf] * #0]x /\
      [| length temps = temp_size /\
        length exprs = length dst_buf |])
    -> syn_req exprs base
    -> exists x0, interp specs (pre (fst x, x0))
        /\ forall specs other vs temps dst_buf,
          interp specs (![is_state (Regs x0 Sp) vs temps dst dst_buf * other ] (fst x, x0))
          -> length temps = temp_size
          -> length exprs = length dst_buf
          -> Regs (snd x) Sp = Regs x0 Sp /\
          exists changed,
            interp specs (![is_state (Regs (snd x) Sp) vs (upd_sublist temps base changed) dst (map (eval vs) exprs) * other ] (fst x, snd x)) /\
            length changed <= depth.
    induction exprs0; post.

    clear_fancy.
    Transparent evalInstrs.
    simpl in H3.
    Opaque evalInstrs.
    injection H3; clear H3; intros; subst.
    descend.
    eauto.
    descend.
    instantiate (1 := nil); simpl.
    destruct dst_buf; simpl in *; auto.
    discriminate.
    simpl; auto.

    apply IHexprs0 in H; clear IHexprs0; auto.
    Focus 2.
    hnf; post.
    apply H0 in H3; clear H0; post.
    unfold is_state in H2.
    assert (interp specs0
      (![locals vars x4 0 (Regs x2 Sp ^+ $ (8)) *
        array x5 (Regs x2 Sp ^+ $ (8) ^+ $ (4 * Datatypes.length vars)) *
        (array x6 (Regs x2 Sp ^+ $ (dst0)) *
        ![fun m : ST.settings * smem => x3 m]) ]
      (fst x0, x2))).
    clear H; clear_fancy.
    step auto_ext.
    clear H2.
    apply H5 in H3; clear H5; post.
    unfold stack_slot in H4.
    clear H; clear_fancy.
    Opaque evalInstrs.
    Opaque evalInstrs.

    eapply change_hyp in H5.
    Focus 2.
    apply Himp_star_frame; [ apply Himp_refl | ].
    apply Himp_star_frame; [ | apply Himp_refl ].
    apply array_out; omega.
    destruct x6; simpl in *; try discriminate.
    evaluate auto_ext.
    destruct x0; simpl in *.
    descend.
    replace (Regs x2 Sp ^+ natToW dst0 ^+ natToW 4) with (Regs x2 Sp ^+ natToW (S (S (S (S dst0)))))
      in H9.
    unfold is_state.
    unfold CompileExpr.is_state in H9.
    step auto_ext.
    rewrite H.
    step auto_ext.
    rewrite <- H3.
    step auto_ext.
    rewrite <- wplus_assoc.
    unfold natToW.
    rewrite <- natToWord_plus.
    repeat f_equal.
    omega.
    rewrite length_upd_sublist; auto.
    auto.

    post.
    post.
    eexists; split; eauto.
    intros.
    clear H2.
    unfold is_state in H.
    assert (interp specs0
      (![CompileExpr.is_state vars (Regs x2 Sp) vs temps
        * (array dst_buf (Regs x2 Sp ^+ $ (dst0)) * other ) ]
      (fst x, x2))).
    unfold CompileExpr.is_state.
    clear H0; clear_fancy.
    step auto_ext.
    clear H.
    apply H5 in H2; clear H5.
    generalize H6; intro Hs.
    apply H2 in Hs; clear H2.
    destruct x; simpl in *.
    destruct Hs as [ ? [ ? [ ? [ ? [ ] ] ] ] ].
    simpl in *.
    eapply change_hyp in H2.
    Focus 2.
    apply Himp_star_frame; [ apply Himp_refl | ].
    apply Himp_star_frame; [ | apply Himp_refl ].
    apply array_out; omega.
    unfold stack_slot in H4.
    clear H0; clear_fancy.
    evaluate auto_ext.
    destruct dst_buf; simpl in *; try discriminate.
    assert (interp specs0
      (![is_state (Regs x0 Sp) vs (upd_sublist temps base0 x) (S (S (S (S dst0)))) dst_buf *
        ((Regs x2 Sp ^+ natToW dst0) =*> Regs x1 Rv * other)] (s, x0))).
    unfold is_state.
    unfold CompileExpr.is_state in H9.
    step auto_ext.
    rewrite <- H0.
    unfold natToW.
    rewrite H.
    rewrite <- H0.
    step auto_ext.
    rewrite <- wplus_assoc.
    unfold natToW.
    rewrite <- natToWord_plus.
    replace (dst0 + 4) with (S (S (S (S dst0)))) by omega.
    step auto_ext.
    clear H9.
    apply H3 in H10; clear H3; auto.
    post.
    congruence.

    assert (length (upd_sublist (upd_sublist temps base0 x) base0 x3)
      = length temps).
    repeat rewrite length_upd_sublist; reflexivity.
    eapply CompileExpr.get_changed in H9.
    post.
    descend.
    rewrite <- H12.
    Focus 3.
    instantiate (1 := base0 + max (length x) (length x3)).
    omega.
    Focus 2.
    destruct H1.
    destruct (NPeano.Nat.max_spec (length x) (length x3)); intuition.
    inversion_clear H16.
    omega.
    unfold is_state in *.
    eapply change_hyp.
    Focus 2.
    apply Himp_star_frame; [ | eapply Himp_refl ].
    apply Himp_star_frame; [ eapply Himp_refl | ].
    Opaque evalInstrs.

    apply array_in; simpl; auto.
    simpl.
    replace (Regs s0 Sp ^+ $ (dst0) ^+ $ (4))
      with (Regs s0 Sp ^+ ($ (dst0) ^+ $ (4))) by words.
    rewrite <- natToWord_plus.
    replace (dst0 + 4) with (S (S (S (S dst0)))) by omega.
    generalize dependent (map (eval vs) exprs0); intros.
    step auto_ext.
    replace (Regs x2 Sp) with (Regs s0 Sp) by congruence.
    step auto_ext.

    intros.
    repeat rewrite CompileExpr.upd_sublist_unchanged by auto; reflexivity.

    intros.
    generalize (Max.le_max_l (length x) (length x3)).
    generalize (Max.le_max_r (length x) (length x3)); intros.
    repeat rewrite CompileExpr.upd_sublist_unchanged_high by auto; reflexivity.

    rewrite length_upd_sublist; auto.
    unfold syn_req in *; intuition.
    hnf; intros.
    apply H2.
    simpl.
    unfold union_list.
    simpl.
    Opaque evalInstrs.

    eapply In_union_list with (exprs0 := a :: exprs0); eauto.
    simpl.
    eapply StringFacts.union_iff; eauto.
    inversion H4; auto.
  Qed.
  Opaque evalInstrs.

  Lemma verifCondOk : forall exprs base dst pre,
    imply pre (x ~> ExX, Ex vs, Ex temps, Ex dst_buf,
      ![^[is_state x#Sp vs temps dst dst_buf] * #0]x /\
      [| length temps = temp_size /\
        length exprs = length dst_buf |])
    -> syn_req exprs base
    -> vcs (VerifCond (Seq (do_compile exprs base dst) pre)).
    induction exprs0; wrap0.

    Transparent evalInstrs.
    discriminate.
    Opaque evalInstrs.

    clear IHexprs0; clear_fancy.
    hnf; post.
    apply H in H1; clear H; post.
    unfold is_state, CompileExpr.is_state in *.
    assert (interp specs
      (![locals vars x1 0 ((x) # (Sp) ^+ $ (8)) *
        array x2 ((x) # (Sp) ^+ $ (8) ^+ $ (4 * Datatypes.length vars)) *
        (array x3 ((x) # (Sp) ^+ $ (dst0)) *
        ![fun m : ST.settings * smem => x0 m]) ] x)).
    step auto_ext.
    clear H1.
    descend.
    step auto_ext.
    auto.

    unfold syn_req, CompileExpr.syn_req in *; intuition.
    hnf; intros.
    apply H1.
    simpl.
    unfold union_list.
    simpl.

    apply StringFacts.union_iff; auto.
    inversion H3; omega.

    clear IHexprs0; clear_fancy.
    apply H in H3; clear H; post.
    unfold is_state in H1.
    assert (interp specs
      (![locals vars x1 0 (Regs x Sp ^+ $ (8)) *
        array x2 (Regs x Sp ^+ $ (8) ^+ $ (4 * Datatypes.length vars)) *
        (array x3 (Regs x Sp ^+ $ (dst0)) *
        ![fun m : ST.settings * smem => x0 m]) ] (stn, x))).
    step auto_ext.
    clear H1.
    apply H4 in H3; clear H4; post.
    eapply change_hyp in H4.
    Focus 2.
    apply Himp_star_frame; [ apply Himp_refl | ].
    apply Himp_star_frame; [ | apply Himp_refl ].
    apply array_out; omega.
    destruct x3; simpl in *; try discriminate.
    unfold stack_slot in *.
    evaluate auto_ext.

    apply IHexprs0; clear IHexprs0; clear_fancy.
    Focus 2.
    unfold syn_req in *; intuition.
    hnf; intros.
    apply H1.
    simpl.
    unfold union_list; simpl.
    eapply In_union_list with (exprs0 := a :: exprs0); eauto.
    apply StringFacts.union_iff; eauto.
    inversion H3; auto.
    hnf; post.
    apply H in H2; clear H; post.
    unfold is_state in H1.
    assert (interp specs
      (![CompileExpr.is_state vars (Regs x1 Sp) x3 x4
        * (array x5 (Regs x1 Sp ^+ $ (dst0)) * ![fun m : ST.settings * smem => x2 m]) ]
      (fst x, x1))).
    unfold CompileExpr.is_state.
    step auto_ext.
    clear H1.
    apply H4 in H2; clear H4; post.
    eapply change_hyp in H4.
    Focus 2.
    apply Himp_star_frame; [ apply Himp_refl | ].
    apply Himp_star_frame; [ | apply Himp_refl ].
    apply array_out; omega.
    destruct x5; simpl in *; try discriminate.
    unfold stack_slot in *.
    evaluate auto_ext.
    destruct x; simpl in *.
    descend.
    rewrite H4.
    rewrite <- H2.
    unfold is_state.
    unfold CompileExpr.is_state in H9.
    step auto_ext.
    rewrite <- H2.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.
    replace (dst0 + 4) with (S (S (S (S dst0)))) by omega.
    step auto_ext.
    rewrite length_upd_sublist; auto.
    congruence.
  Qed.

  Definition compile : cmd imports modName.
    refine (Wrap imports imports_global modName body post (verifCond base) _ _).
    Opaque evalInstrs.

    abstract (unfold verifCond; wrap0;
      match goal with
        | [ H : interp _ _ |- _ ] => eapply postOk in H; post; descend; eauto
      end).
    Opaque evalInstrs.

    abstract (unfold verifCond; wrap0; eauto using verifCondOk).
  Defined.

End TopLevel.
