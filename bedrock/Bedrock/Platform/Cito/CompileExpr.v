Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep.
Require Import Bedrock.Platform.Cito.SyntaxExpr.

Require Import Bedrock.StringSet.
Import StringSet.
Require Import Coq.FSets.FSetProperties.
Module Import SSP := Properties StringSet.

Set Implicit Arguments.

Section ExprComp.

  Variable vars : list string.

  Variable temp_size : nat.

  Definition vars_start := 4 * 2.
  Definition var_slot x := LvMem (Sp + (vars_start + variablePosition vars x)%nat)%loc.
  Definition temp_start := vars_start + 4 * length vars.
  Definition temp_slot n := LvMem (Sp + (temp_start + 4 * n)%nat)%loc.

  Definition is_state sp vs temps : HProp :=
    (locals vars vs 0 (sp ^+ $8) *
     array temps (sp ^+ $8 ^+ $ (4 * length vars)))%Sep.

  Definition new_pre : assert :=
    x ~> ExX, Ex vs, Ex temps,
    ![^[is_state x#Sp vs temps] * #0]x /\
    [| length temps = temp_size |].

  Require Import Bedrock.Platform.Cito.SemanticsExpr.
  Require Import Bedrock.Platform.Cito.DepthExpr.
  Require Import Bedrock.Platform.Cito.ListFacts5.

  Local Open Scope nat.

  Definition runs_to expr base x_pre x :=
    forall specs other vs temps,
      interp specs (![is_state x_pre#Sp vs temps * other ] x_pre)
      -> length temps = temp_size
      -> Regs x Sp = x_pre#Sp /\
      exists changed,
        interp specs (![is_state (Regs x Sp) vs (upd_sublist temps base changed) * other ] (fst x_pre, x)) /\
        length changed <= depth expr /\
        Regs x Rv = eval vs expr.

  Definition post expr base (pre : assert) :=
    st ~> Ex st_pre,
    pre (fst st, st_pre) /\
    [| runs_to expr base (fst st, st_pre) (snd st) |].

  Definition imply (pre new_pre: assert) := forall specs x, interp specs (pre x) -> interp specs (new_pre x).

  Require Import Bedrock.Platform.Cito.FreeVarsExpr.

  Definition syn_req expr base :=
    Subset (free_vars expr) (of_list vars) /\
    base + depth expr <= temp_size.

  Definition verifCond expr base pre := imply pre new_pre :: syn_req expr base :: nil.

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

  Fixpoint do_compile (expr : Expr) (base : nat) :=
    match expr with
      | Var str => Strline (Assign (LvReg Rv) (RvLval (var_slot str)) :: nil)
      | Const w => Strline (Assign (LvReg Rv) (RvImm w) :: nil)
      | Binop op a b => Seq (
        do_compile a base ::
        Strline(Assign (temp_slot base) (RvLval (LvReg Rv)) :: nil) ::
        do_compile b (S base) ::
        (Strline (IL.Binop (LvReg Rv) (RvLval (temp_slot base)) op (RvLval (LvReg Rv)) :: nil)) :: nil)
      | TestE te a b => Seq (do_compile a base ::
        Strline( Assign (temp_slot base) (RvLval (LvReg Rv)) :: nil ) ::
        do_compile b (S base) ::
        Structured.If_ imports_global (RvLval (temp_slot base)) te (RvLval (LvReg Rv))
        (Strline (Assign Rv (RvImm $1) :: nil))
        (Strline (Assign Rv (RvImm $0) :: nil))
        ::nil)
    end.

  Definition body := do_compile.

  Require Import Bedrock.Platform.Wrap.

  Hint Extern 1 (_ <= _) => omega.

  Opaque mult.
  Opaque evalInstrs.

  Lemma evalInstrs_read_var : forall sm x s,
    evalInstrs sm x (Assign Rv (var_slot s) :: nil)
    = evalInstrs sm x (Assign Rv (LvMem (Imm ((Regs x Sp ^+ natToW vars_start) ^+ natToW (variablePosition vars s)))) :: nil).
    Transparent evalInstrs.
    simpl.
    intros.
    replace (Regs x Sp ^+ natToW (vars_start + variablePosition vars s))
      with (Regs x Sp ^+ natToW vars_start ^+ natToW (variablePosition vars s)); auto.
    rewrite natToW_plus.
    words.
    Opaque evalInstrs.
  Qed.

  Require Import Bedrock.Platform.Cito.SetoidListFacts.

  Lemma In_to_set :
    forall x ls,
      StringSet.In x (SSP.of_list ls)
      -> List.In x ls.
    intros.
    eapply SSP.of_list_1 in H.
    eapply InA_eq_In_iff; eauto.
  Qed.
  Opaque evalInstrs.

  Lemma evalInstrs_write_temp : forall sm x base',
    evalInstrs sm x (Assign (temp_slot base') Rv :: nil)
    = evalInstrs sm x (Assign (LvMem (Imm (Regs x Sp ^+ $8 ^+ $ (4 * length vars) ^+ $4 ^* natToW base'))) Rv :: nil).
    Transparent evalInstrs.
    simpl.
    intros.
    replace (Regs x Sp ^+ natToW (temp_start + 4 * base'))
      with (Regs x Sp ^+ $ (8) ^+ $ (4 * length vars) ^+ $4 ^* natToW base'); auto.
    rewrite natToW_plus.
    unfold temp_start, vars_start.
    change (4 * 2) with 8.
    rewrite natToW_plus.
    unfold natToW.
    rewrite (Mult.mult_comm 4 base').
    change (natToWord 32 (base' * 4)) with (natToW (base' * 4)).
    rewrite (natToW_times4 base').
    unfold natToW.
    words.
    Opaque evalInstrs.
  Qed.
  Opaque evalInstrs.

  Lemma evalInstrs_binop_temp : forall sm x base' b,
    evalInstrs sm x (IL.Binop Rv (temp_slot base') b Rv :: nil)
    = evalInstrs sm x (IL.Binop Rv (LvMem (Imm (Regs x Sp ^+ $8 ^+ $ (4 * length vars) ^+ $4 ^* natToW base'))) b Rv :: nil).
    Transparent evalInstrs.
    simpl.
    intros.
    replace (Regs x Sp ^+ natToW (temp_start + 4 * base'))
      with (Regs x Sp ^+ $ (8) ^+ $ (4 * length vars) ^+ $4 ^* natToW base'); auto.
    rewrite natToW_plus.
    unfold temp_start, vars_start.
    change (4 * 2) with 8.
    rewrite natToW_plus.
    unfold natToW.
    rewrite (Mult.mult_comm 4 base').
    change (natToWord 32 (base' * 4)) with (natToW (base' * 4)).
    rewrite (natToW_times4 base').
    unfold natToW.
    words.
    Opaque evalInstrs.
  Qed.

  Lemma selN_updN_eq : forall a p v,
    p < length a
    -> selN (updN a p v) p = v.
    induction a; simpl; intuition.
    destruct p; simpl; intuition.
  Qed.

  Lemma sel_upd_eq : forall a p v,
    p < length a
    -> goodSize (length a)
    -> Array.sel (Array.upd a p v) p = v.
    unfold Array.sel, Array.upd; intros.
    apply selN_updN_eq; auto.
    rewrite wordToNat_natToWord_idempotent; auto.
    change (goodSize p).
    eapply goodSize_weaken; eauto.
  Qed.

  Lemma selN_updN_ne : forall a p v p',
    p <> p'
    -> selN (updN a p v) p' = selN a p'.
    induction a; simpl; intuition.
    destruct p, p'; simpl; intuition.
  Qed.

  Lemma sublist_irrel : forall base, goodSize base
    -> forall v base' a,
      base < base'
      -> Array.sel (upd_sublist a base' v) base = Array.sel a base.
    induction v; simpl; intuition.
    rewrite IHv; auto.
    rewrite sel_selN by auto.
    rewrite selN_updN_ne; try omega.
    unfold Array.sel.
    rewrite wordToNat_natToWord_idempotent; auto.
  Qed.

  Lemma upd_sublist_unchanged : forall p ws a base,
    p < base
    -> Array.selN (upd_sublist a base ws) p = Array.selN a p.
    induction ws; simpl; intuition.
    rewrite IHws by omega.
    apply selN_updN_ne; omega.
  Qed.

  Lemma array_extensional : forall a1 a2,
    length a1 = length a2
    -> (forall p, p < length a1 -> selN a1 p = selN a2 p)
    -> a1 = a2.
    induction a1; destruct a2; simpl; intuition.
    injection H; clear H; intros.
    apply IHa1 in H; clear IHa1; subst.
    f_equal.
    specialize (H0 0); simpl in H0.
    auto.
    intros.
    specialize (H0 (S p)); simpl in H0.
    apply H0; omega.
  Qed.

  Require Import Coq.Arith.Arith.

  Lemma get_changed' : forall limit n a' a base,
    length a - base = n
    -> length a' = length a
    -> base <= limit
    -> (forall p, p < base -> Array.selN a' p = Array.selN a p)
    -> (forall p, p >= limit -> Array.selN a' p = Array.selN a p)
    -> exists changed, a' = upd_sublist a base changed
      /\ length changed <= limit - base.
    induction n; simpl; intros.

    exists nil.
    simpl; split.
    apply array_extensional; auto.
    auto.
    destruct (eq_nat_dec limit base); subst.

    (* We've reached the point where [a'] and [a] always agree, so no more updating is required. *)
    exists nil; intuition.
    unfold upd_sublist.
    apply array_extensional; intros; auto.
    destruct (le_lt_dec base p); auto.

    (* The current element is still allowed to change.  Keep inducting. *)
    assert (length (updN a base (selN a' base)) - S base = n)
      by (rewrite updN_length; omega).
    eapply IHn in H4.
    Focus 2.
    instantiate (1 := a').
    rewrite updN_length; auto.
    2: omega.
    Focus 2.
    intros.
    destruct (eq_nat_dec p base); subst.
    symmetry; apply selN_updN_eq.
    rewrite updN_length in H.
    omega.
    rewrite selN_updN_ne; auto.

    destruct H4.
    exists (selN a' base :: x).
    intuition idtac.
    simpl; omega.

    intros.
    rewrite selN_updN_ne; auto.
    omega.
  Qed.

  Lemma get_changed : forall a' a base limit,
    length a' = length a
    -> base <= limit
    -> (forall p, p < base -> Array.selN a' p = Array.selN a p)
    -> (forall p, p >= limit -> Array.selN a' p = Array.selN a p)
    -> exists changed, a' = upd_sublist a base changed
      /\ length changed <= limit - base.
    intros; eapply get_changed'; eauto.
  Qed.

  Lemma upd_sublist_unchanged_high : forall p ws a base,
    p >= base + length ws
    -> Array.selN (upd_sublist a base ws) p = Array.selN a p.
    induction ws; simpl; intuition.
    rewrite IHws by omega.
    apply selN_updN_ne; omega.
  Qed.

  Lemma evalCond_temp : forall sm x base' t0,
    evalCond (temp_slot base') t0 Rv sm x
    = evalCond (LvMem (Imm (Regs x Sp ^+ $8 ^+ $ (4 * length vars) ^+ $4 ^* natToW base'))) t0 Rv sm x.
    unfold evalCond; simpl; intros.
    replace (Regs x Sp ^+ natToW (temp_start + 4 * base'))
      with (Regs x Sp ^+ $ (8) ^+ $ (4 * length vars) ^+ $4 ^* natToW base'); auto.
    rewrite natToW_plus.
    unfold temp_start, vars_start.
    change (4 * 2) with 8.
    rewrite natToW_plus.
    unfold natToW.
    rewrite (Mult.mult_comm 4 base').
    change (natToWord 32 (base' * 4)) with (natToW (base' * 4)).
    rewrite (natToW_times4 base').
    unfold natToW.
    words.
  Qed.

  Lemma postOk : forall specs sm expr base pre st,
    Subset (free_vars expr) (of_list vars)
    -> base + depth expr <= temp_size
    -> interp specs (Postcondition (do_compile expr base pre) (sm, st))
    -> exists st', interp specs (pre (sm, st')) /\ runs_to expr base (sm, st') st.
    induction expr; simpl; propxFo.

    do 2 esplit.
    eauto.
    hnf.
    intros.
    unfold is_state in H; simpl in H.

    Opaque mult.
    Opaque evalInstrs.

    hnf in H.
    assert (In s (singleton s)).
    apply StringFacts.singleton_iff; auto.
    apply H in H5.

    Opaque mult.
    Opaque evalInstrs.

    assert (List.In s vars) by eauto using In_to_set.
    rewrite evalInstrs_read_var in H3.
    unfold vars_start in H3.
    change (4 * 2) with 8 in *.
    clear_fancy.
    unfold is_state in H1; simpl in H1.
    evaluate auto_ext.
    simpl.
    intuition idtac.
    exists nil; simpl; intuition idtac.
    unfold is_state.
    rewrite H1.
    step auto_ext.
    auto.

    do 2 esplit; eauto.
    hnf; intros.
    simpl.
    clear_fancy.
    evaluate auto_ext.
    intuition idtac.
    exists nil; simpl; intuition.
    step auto_ext.

    apply IHexpr2 in H2; clear IHexpr2.
    Focus 2.
    hnf; intros.
    apply H.
    apply StringFacts.union_iff; auto.
    destruct H2; propxFo.
    apply IHexpr1 in H2; clear IHexpr1.
    Focus 2.
    hnf; intros.
    apply H.
    apply StringFacts.union_iff; auto.
    destruct H2; intuition.
    do 2 esplit; eauto.
    hnf; simpl; intros.
    unfold is_state in H1; simpl in H1.

    Opaque mult.
    Opaque evalInstrs.

    Opaque mult.
    Opaque evalInstrs.

    rewrite evalInstrs_write_temp in H6.
    assert (natToW base < natToW (length temps))%word.
    apply lt_goodSize.
    assert (max (depth expr1) (S (depth expr2)) > 0).
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))).
    omega.
    omega.
    apply goodSize_weaken with (length temps); eauto.
    eauto.
    apply H7 in H1; clear H7.
    generalize H8; intro Hs.
    apply H1 in Hs; clear H1.
    destruct Hs as [ ? [ ? [ ? [ ] ] ] ]; simpl in *.
    generalize dependent H5; generalize dependent H4; generalize dependent H3.
    clear_fancy.
    unfold is_state in H7; simpl in H7.
    assert (natToW base < natToW (length (upd_sublist temps base x4)))%word.
    rewrite length_upd_sublist; assumption.
    evaluate auto_ext.
    intros.
    hnf in H14.
    assert (interp specs0 (![is_state ((sm, x1)) # (Sp) vs
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1))* other] (sm, x1))).
    unfold is_state; simpl.
    clear_fancy; step auto_ext.
    replace (Regs x2 Sp) with (Regs x1 Sp) by words.
    step auto_ext.
    apply H15 in H16; clear H15.
    destruct H16 as [ ? [ ? [ ? [ ] ] ] ]; simpl in *.
    rewrite upd_length.
    rewrite length_upd_sublist.
    auto.
    rewrite evalInstrs_binop_temp in H14.
    clear_fancy.
    destruct b.
    assert (natToW base < natToW (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)))%word.
    rewrite length_upd_sublist; rewrite upd_length; assumption.
    clear H12; unfold is_state in H16.
    evaluate auto_ext.
    intuition idtac.
    congruence.

    Opaque mult.
    Opaque evalInstrs.

    Opaque mult.
    Opaque evalInstrs.

    Opaque mult.
    Opaque evalInstrs.

    Opaque mult.
    Opaque evalInstrs.

    rewrite sublist_irrel in H20.
    rewrite sel_upd_eq in H20.
    simpl.

    Opaque mult.
    Opaque evalInstrs.

    Opaque mult.
    Opaque evalInstrs.

    Opaque mult.
    Opaque evalInstrs.

    Opaque mult.
    Opaque evalInstrs.

    assert (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1))
      (S base) x5) = length temps).
    rewrite length_upd_sublist.
    rewrite upd_length.
    apply length_upd_sublist.
    eapply get_changed in H22.
    destruct H22.
    eexists; intuition idtac.
    unfold is_state.
    rewrite <- H23.
    step auto_ext.
    replace (Regs x0 Sp) with (Regs st Sp) by congruence.
    step auto_ext.
    Focus 2.
    instantiate (1 := base + max (depth expr1) (S (depth expr2))).
    omega.
    omega.
    intros.
    rewrite upd_sublist_unchanged by omega.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged; auto.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H23.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)).
    eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    omega.
    intros.

    Opaque mult.
    Opaque evalInstrs.

    rewrite upd_sublist_unchanged_high.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged_high.
    generalize (Max.le_max_l (depth expr1) (S (depth expr2))); omega.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H23.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    apply lt_goodSize'; auto.
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    omega.
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    repeat (rewrite length_upd_sublist || rewrite upd_length); omega.
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    repeat (rewrite length_upd_sublist || rewrite upd_length); omega.
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    repeat (rewrite length_upd_sublist || rewrite upd_length); omega.
    omega.


    assert (natToW base < natToW (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)))%word.
    rewrite length_upd_sublist; rewrite upd_length; assumption.
    clear H12; unfold is_state in H16.
    evaluate auto_ext.
    intuition idtac.
    congruence.
    rewrite sublist_irrel in H20.
    rewrite sel_upd_eq in H20.
    simpl.
    assert (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1))
      (S base) x5) = length temps).
    rewrite length_upd_sublist.
    rewrite upd_length.
    apply length_upd_sublist.
    eapply get_changed in H22.
    destruct H22.
    eexists; intuition idtac.
    unfold is_state.
    rewrite <- H23.
    step auto_ext.
    replace (Regs x0 Sp) with (Regs st Sp) by congruence.
    step auto_ext.
    Focus 2.
    instantiate (1 := base + max (depth expr1) (S (depth expr2))).
    omega.
    omega.
    intros.
    rewrite upd_sublist_unchanged by omega.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged; auto.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H23.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)).
    eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    omega.
    intros.
    rewrite upd_sublist_unchanged_high.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged_high.
    generalize (Max.le_max_l (depth expr1) (S (depth expr2))); omega.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H23.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    apply lt_goodSize'; auto.
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    omega.
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    repeat (rewrite length_upd_sublist || rewrite upd_length); omega.
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    repeat (rewrite length_upd_sublist || rewrite upd_length); omega.
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    repeat (rewrite length_upd_sublist || rewrite upd_length); omega.
    omega.


    assert (natToW base < natToW (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)))%word.
    rewrite length_upd_sublist; rewrite upd_length; assumption.
    clear H12; unfold is_state in H16.
    evaluate auto_ext.
    intuition idtac.
    congruence.
    rewrite sublist_irrel in H20.
    rewrite sel_upd_eq in H20.
    simpl.
    assert (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1))
      (S base) x5) = length temps).
    rewrite length_upd_sublist.
    rewrite upd_length.
    apply length_upd_sublist.
    eapply get_changed in H22.
    destruct H22.
    eexists; intuition idtac.
    unfold is_state.
    rewrite <- H23.
    step auto_ext.
    replace (Regs x0 Sp) with (Regs st Sp) by congruence.
    step auto_ext.
    Focus 2.
    instantiate (1 := base + max (depth expr1) (S (depth expr2))).
    omega.
    omega.
    intros.
    rewrite upd_sublist_unchanged by omega.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged; auto.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H23.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)).
    eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    omega.
    intros.
    rewrite upd_sublist_unchanged_high.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged_high.
    generalize (Max.le_max_l (depth expr1) (S (depth expr2))); omega.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H23.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    apply lt_goodSize'; auto.
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    omega.
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    repeat (rewrite length_upd_sublist || rewrite upd_length); omega.
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    repeat (rewrite length_upd_sublist || rewrite upd_length); omega.
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    repeat (rewrite length_upd_sublist || rewrite upd_length); omega.
    omega.

    assert (max (depth expr1) (S (depth expr2)) >= depth expr1) by apply Max.le_max_l.
    omega.

    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r.
    omega.


    apply IHexpr2 in H1; clear IHexpr2.
    Focus 2.
    do 2 intro.
    apply H.
    apply StringFacts.union_iff; auto.
    Focus 2.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r.
    omega.
    destruct H1; propxFo.
    apply IHexpr1 in H2; clear IHexpr1.
    Focus 2.
    do 2 intro.
    apply H.
    apply StringFacts.union_iff; auto.
    Focus 2.
    assert (max (depth expr1) (S (depth expr2)) >= depth expr1) by apply Max.le_max_l.
    omega.
    destruct H2; intuition idtac.
    do 2 esplit; eauto.
    hnf; simpl; intros.
    apply H8 in H1; clear H8.
    generalize H9; intro Hs.
    apply H1 in Hs; clear H1.
    simpl in Hs; destruct Hs as [ ? [ ? [ ? [ ] ] ] ].
    rewrite evalInstrs_write_temp in *.

    Opaque mult.
    Opaque evalInstrs.

    rewrite evalCond_temp in *.
    clear_fancy.
    generalize dependent H3; generalize dependent H4; generalize dependent H5.
    unfold is_state in H8.
    assert (natToW base < natToW (length (upd_sublist temps base x4)))%word.
    rewrite length_upd_sublist.
    apply lt_goodSize; auto.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    apply goodSize_weaken with (length (upd_sublist temps base x4)); eauto.
    rewrite length_upd_sublist; auto.
    apply goodSize_weaken with (length (upd_sublist temps base x4)); eauto.
    rewrite length_upd_sublist; auto.
    evaluate auto_ext.
    intros.
    assert (interp specs0 (![is_state ((sm, x1)) # (Sp) vs
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1))* other] (sm, x1))).
    unfold is_state; simpl.
    clear_fancy; step auto_ext.
    replace (Regs x2 Sp) with (Regs x1 Sp) by words.
    step auto_ext.
    clear H12; apply H6 in H16.
    rewrite upd_length in H16.
    rewrite length_upd_sublist in H16.
    generalize H9; intro Hs.
    apply H16 in Hs; clear H16.
    simpl in Hs; destruct Hs as [ ? [ ? [ ? [ ] ] ] ].
    unfold is_state in H16; simpl in H16.
    assert (natToW base < natToW (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1)) (S base) x5)))%word.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    apply lt_goodSize; auto.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1))
      (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1))
      (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    auto.
    generalize dependent H14.
    destruct t0; simpl.

    evaluate auto_ext.
    intros; evaluate auto_ext.
    intuition.
    assert (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1))
      (S base) x5) = length temps).
    rewrite length_upd_sublist.
    rewrite upd_length.
    apply length_upd_sublist.
    eapply get_changed in H24.
    destruct H24.
    eexists; intuition idtac.
    unfold is_state.
    rewrite <- H25.
    step auto_ext.
    replace (Regs x0 Sp) with (Regs st Sp) by congruence.
    step auto_ext.
    Focus 3.
    instantiate (1 := base + max (depth expr1) (S (depth expr2))).
    omega.
    omega.
    unfold Array.sel in H22.
    rewrite upd_sublist_unchanged in H22.
    unfold Array.upd in H22.
    rewrite selN_updN_eq in H22.
    generalize (weqb_true_iff (eval vs expr1) (eval vs expr2)).
    unfold weqb.
    destruct (Word.weqb (eval vs expr1) (eval vs expr2)); intuition (try discriminate).
    rewrite length_upd_sublist.
    rewrite wordToNat_natToWord_idempotent.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    rewrite wordToNat_natToWord_idempotent.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    intros.
    rewrite upd_sublist_unchanged by omega.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged; auto.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H25.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)).
    eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    omega.
    intros.
    rewrite upd_sublist_unchanged_high.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged_high.
    generalize (Max.le_max_l (depth expr1) (S (depth expr2))); omega.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H25.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.

    evaluate auto_ext.
    intros; evaluate auto_ext.
    intuition.
    assert (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1))
      (S base) x5) = length temps).
    rewrite length_upd_sublist.
    rewrite upd_length.
    apply length_upd_sublist.
    eapply get_changed in H24.
    destruct H24.
    eexists; intuition idtac.
    unfold is_state.
    rewrite <- H25.
    step auto_ext.
    replace (Regs x0 Sp) with (Regs st Sp) by congruence.
    step auto_ext.
    Focus 3.
    instantiate (1 := base + max (depth expr1) (S (depth expr2))).
    omega.
    omega.
    unfold Array.sel in H22.
    rewrite upd_sublist_unchanged in H22.
    unfold Array.upd in H22.
    rewrite selN_updN_eq in H22.
    unfold wneb.
    destruct (weq (eval vs expr1) (eval vs expr2)); auto.
    exfalso; eauto.
    rewrite length_upd_sublist.
    rewrite wordToNat_natToWord_idempotent.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    rewrite wordToNat_natToWord_idempotent.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    intros.
    rewrite upd_sublist_unchanged by omega.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged; auto.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H25.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)).
    eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    omega.
    intros.
    rewrite upd_sublist_unchanged_high.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged_high.
    generalize (Max.le_max_l (depth expr1) (S (depth expr2))); omega.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H25.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.

    evaluate auto_ext.
    intros; evaluate auto_ext.
    intuition.
    assert (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1))
      (S base) x5) = length temps).
    rewrite length_upd_sublist.
    rewrite upd_length.
    apply length_upd_sublist.
    eapply get_changed in H24.
    destruct H24.
    eexists; intuition idtac.
    unfold is_state.
    rewrite <- H25.
    step auto_ext.
    replace (Regs x0 Sp) with (Regs st Sp) by congruence.
    step auto_ext.
    Focus 3.
    instantiate (1 := base + max (depth expr1) (S (depth expr2))).
    omega.
    omega.
    unfold Array.sel in H22.
    rewrite upd_sublist_unchanged in H22.
    unfold Array.upd in H22.
    rewrite selN_updN_eq in H22.
    unfold wltb.
    destruct (wlt_dec (eval vs expr1) (eval vs expr2)); intuition (try discriminate).
    rewrite length_upd_sublist.
    rewrite wordToNat_natToWord_idempotent.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    rewrite wordToNat_natToWord_idempotent.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    intros.
    rewrite upd_sublist_unchanged by omega.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged; auto.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H25.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)).
    eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    omega.
    intros.
    rewrite upd_sublist_unchanged_high.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged_high.
    generalize (Max.le_max_l (depth expr1) (S (depth expr2))); omega.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H25.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.

    evaluate auto_ext.
    intros; evaluate auto_ext.
    intuition.
    assert (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1))
      (S base) x5) = length temps).
    rewrite length_upd_sublist.
    rewrite upd_length.
    apply length_upd_sublist.
    eapply get_changed in H24.
    destruct H24.
    eexists; intuition idtac.
    unfold is_state.
    rewrite <- H25.
    step auto_ext.
    replace (Regs x0 Sp) with (Regs st Sp) by congruence.
    step auto_ext.
    Focus 3.
    instantiate (1 := base + max (depth expr1) (S (depth expr2))).
    omega.
    omega.
    unfold Array.sel in H22.
    rewrite upd_sublist_unchanged in H22.
    unfold Array.upd in H22.
    rewrite selN_updN_eq in H22.
    unfold wleb.
    destruct (weq (eval vs expr1) (eval vs expr2)); intuition (try discriminate).
    destruct (wlt_dec (eval vs expr1) (eval vs expr2)); intuition (try discriminate).
    apply le_neq_lt in n; tauto.
    rewrite length_upd_sublist.
    rewrite wordToNat_natToWord_idempotent.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    rewrite wordToNat_natToWord_idempotent.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    intros.
    rewrite upd_sublist_unchanged by omega.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged; auto.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H25.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)).
    eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    omega.
    intros.
    rewrite upd_sublist_unchanged_high.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged_high.
    generalize (Max.le_max_l (depth expr1) (S (depth expr2))); omega.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H25.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.


    apply IHexpr2 in H1; clear IHexpr2.
    Focus 2.
    do 2 intro.
    apply H.
    apply StringFacts.union_iff; auto.
    Focus 2.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r.
    omega.
    destruct H1; propxFo.
    apply IHexpr1 in H2; clear IHexpr1.
    Focus 2.
    do 2 intro.
    apply H.
    apply StringFacts.union_iff; auto.
    Focus 2.
    assert (max (depth expr1) (S (depth expr2)) >= depth expr1) by apply Max.le_max_l.
    omega.
    destruct H2; intuition idtac.
    do 2 esplit; eauto.
    hnf; simpl; intros.
    apply H8 in H1; clear H8.
    generalize H9; intro Hs.
    apply H1 in Hs; clear H1.
    simpl in Hs; destruct Hs as [ ? [ ? [ ? [ ] ] ] ].
    rewrite evalInstrs_write_temp in *.
    rewrite evalCond_temp in *.
    clear_fancy.
    generalize dependent H3; generalize dependent H4; generalize dependent H5.
    unfold is_state in H8.
    assert (natToW base < natToW (length (upd_sublist temps base x4)))%word.
    rewrite length_upd_sublist.
    apply lt_goodSize; auto.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    apply goodSize_weaken with (length (upd_sublist temps base x4)); eauto.
    rewrite length_upd_sublist; auto.
    apply goodSize_weaken with (length (upd_sublist temps base x4)); eauto.
    rewrite length_upd_sublist; auto.
    evaluate auto_ext.
    intros.
    assert (interp specs0 (![is_state ((sm, x1)) # (Sp) vs
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1))* other] (sm, x1))).
    unfold is_state; simpl.
    clear_fancy; step auto_ext.
    replace (Regs x2 Sp) with (Regs x1 Sp) by words.
    step auto_ext.
    clear H12; apply H6 in H16.
    rewrite upd_length in H16.
    rewrite length_upd_sublist in H16.
    generalize H9; intro Hs.
    apply H16 in Hs; clear H16.
    simpl in Hs; destruct Hs as [ ? [ ? [ ? [ ] ] ] ].
    unfold is_state in H16; simpl in H16.
    assert (natToW base < natToW (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1)) (S base) x5)))%word.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    apply lt_goodSize; auto.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1))
      (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1))
      (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    auto.
    generalize dependent H14.
    destruct t0; simpl.

    evaluate auto_ext.
    intros; evaluate auto_ext.
    intuition.
    assert (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1))
      (S base) x5) = length temps).
    rewrite length_upd_sublist.
    rewrite upd_length.
    apply length_upd_sublist.
    eapply get_changed in H24.
    destruct H24.
    eexists; intuition idtac.
    unfold is_state.
    rewrite <- H25.
    step auto_ext.
    replace (Regs x0 Sp) with (Regs st Sp) by congruence.
    step auto_ext.
    Focus 3.
    instantiate (1 := base + max (depth expr1) (S (depth expr2))).
    omega.
    omega.
    unfold Array.sel in H22.
    rewrite upd_sublist_unchanged in H22.
    unfold Array.upd in H22.
    rewrite selN_updN_eq in H22.
    generalize (weqb_true_iff (eval vs expr1) (eval vs expr2)).
    unfold weqb.
    destruct (Word.weqb (eval vs expr1) (eval vs expr2)); intuition (try discriminate).
    rewrite length_upd_sublist.
    rewrite wordToNat_natToWord_idempotent.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    rewrite wordToNat_natToWord_idempotent.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    intros.
    rewrite upd_sublist_unchanged by omega.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged; auto.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H25.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)).
    eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    omega.
    intros.
    rewrite upd_sublist_unchanged_high.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged_high.
    generalize (Max.le_max_l (depth expr1) (S (depth expr2))); omega.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H25.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.

    evaluate auto_ext.
    intros; evaluate auto_ext.
    intuition.
    assert (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1))
      (S base) x5) = length temps).
    rewrite length_upd_sublist.
    rewrite upd_length.
    apply length_upd_sublist.
    eapply get_changed in H24.
    destruct H24.
    eexists; intuition idtac.
    unfold is_state.
    rewrite <- H25.
    step auto_ext.
    replace (Regs x0 Sp) with (Regs st Sp) by congruence.
    step auto_ext.
    Focus 3.
    instantiate (1 := base + max (depth expr1) (S (depth expr2))).
    omega.
    omega.
    unfold Array.sel in H22.
    rewrite upd_sublist_unchanged in H22.
    unfold Array.upd in H22.
    rewrite selN_updN_eq in H22.
    unfold wneb.
    destruct (weq (eval vs expr1) (eval vs expr2)); auto.
    exfalso; eauto.
    rewrite length_upd_sublist.
    rewrite wordToNat_natToWord_idempotent.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    rewrite wordToNat_natToWord_idempotent.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    intros.
    rewrite upd_sublist_unchanged by omega.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged; auto.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H25.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)).
    eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    omega.
    intros.
    rewrite upd_sublist_unchanged_high.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged_high.
    generalize (Max.le_max_l (depth expr1) (S (depth expr2))); omega.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H25.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.

    evaluate auto_ext.
    intros; evaluate auto_ext.
    intuition.
    assert (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1))
      (S base) x5) = length temps).
    rewrite length_upd_sublist.
    rewrite upd_length.
    apply length_upd_sublist.
    eapply get_changed in H24.
    destruct H24.
    eexists; intuition idtac.
    unfold is_state.
    rewrite <- H25.
    step auto_ext.
    replace (Regs x0 Sp) with (Regs st Sp) by congruence.
    step auto_ext.
    Focus 3.
    instantiate (1 := base + max (depth expr1) (S (depth expr2))).
    omega.
    omega.
    unfold Array.sel in H22.
    rewrite upd_sublist_unchanged in H22.
    unfold Array.upd in H22.
    rewrite selN_updN_eq in H22.
    unfold wltb.
    destruct (wlt_dec (eval vs expr1) (eval vs expr2)); intuition (try discriminate).
    rewrite length_upd_sublist.
    rewrite wordToNat_natToWord_idempotent.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    rewrite wordToNat_natToWord_idempotent.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    intros.
    rewrite upd_sublist_unchanged by omega.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged; auto.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H25.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)).
    eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    omega.
    intros.
    rewrite upd_sublist_unchanged_high.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged_high.
    generalize (Max.le_max_l (depth expr1) (S (depth expr2))); omega.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H25.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.

    evaluate auto_ext.
    intros; evaluate auto_ext.
    intuition.
    assert (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base (eval vs expr1))
      (S base) x5) = length temps).
    rewrite length_upd_sublist.
    rewrite upd_length.
    apply length_upd_sublist.
    eapply get_changed in H24.
    destruct H24.
    eexists; intuition idtac.
    unfold is_state.
    rewrite <- H25.
    step auto_ext.
    replace (Regs x0 Sp) with (Regs st Sp) by congruence.
    step auto_ext.
    Focus 3.
    instantiate (1 := base + max (depth expr1) (S (depth expr2))).
    omega.
    omega.
    unfold Array.sel in H22.
    rewrite upd_sublist_unchanged in H22.
    unfold Array.upd in H22.
    rewrite selN_updN_eq in H22.
    unfold wleb.
    destruct (weq (eval vs expr1) (eval vs expr2)); intuition (try discriminate).
    rewrite e in H22.
    exfalso; eapply wlt_not_refl; eauto.
    destruct (wlt_dec (eval vs expr1) (eval vs expr2)); intuition (try discriminate).
    apply lt_le in w.
    exfalso; apply w; auto.
    rewrite length_upd_sublist.
    rewrite wordToNat_natToWord_idempotent.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    rewrite wordToNat_natToWord_idempotent.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    intros.
    rewrite upd_sublist_unchanged by omega.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged; auto.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H25.
    omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)).
    eauto.
    rewrite length_upd_sublist.
    rewrite upd_length.
    rewrite length_upd_sublist.
    omega.
    intros.
    rewrite upd_sublist_unchanged_high.
    unfold Array.upd.
    rewrite selN_updN_ne.
    apply upd_sublist_unchanged_high.
    generalize (Max.le_max_l (depth expr1) (S (depth expr2))); omega.
    intro; subst.
    rewrite wordToNat_natToWord_idempotent in H25.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    change (goodSize base).
    apply goodSize_weaken with (length (upd_sublist
      (Array.upd (upd_sublist temps base x4) base
        (eval vs expr1)) (S base) x5)); eauto.
    generalize (Max.le_max_r (depth expr1) (S (depth expr2))); omega.
    (* Sorry for all that copying and pasting. ;-) *)
  Qed.
  Opaque evalInstrs.

  Lemma verifCondOk : forall expr base pre,
    imply pre new_pre
    -> Subset (free_vars expr) (of_list vars)
    -> base + depth expr <= temp_size
    -> vcs (VerifCond (body expr base pre)).
    induction expr; wrap0; simpl in *.

    apply H in H2; clear H; post.
    unfold is_state in H2.
    rewrite evalInstrs_read_var in *.
    unfold vars_start in *.
    change (4 * 2) with 8 in *.
    unfold natToW in H3.
    assert (List.In s vars).
    apply In_to_set.
    apply H0.
    apply StringFacts.singleton_iff; auto.
    clear_fancy.
    evaluate auto_ext.

    clear_fancy.
    clear H.
    evaluate auto_ext.

    apply IHexpr1; auto.
    do 2 intro.
    apply H0.
    apply StringFacts.union_iff; auto.
    assert (max (depth expr1) (S (depth expr2)) >= depth expr1) by apply Max.le_max_l; omega.

    apply postOk in H2.
    Focus 2.
    do 2 intro.
    apply H0.
    apply StringFacts.union_iff; auto.
    Focus 2.
    assert (max (depth expr1) (S (depth expr2)) >= depth expr1) by apply Max.le_max_l; omega.
    destruct H2 as [ ? [ ? ] ].
    apply H in H2; clear H.
    post.
    apply H4 in H2; intuition idtac.
    simpl in *.
    destruct H6; intuition idtac.
    unfold is_state in H6.
    rewrite evalInstrs_write_temp in *.
    assert (natToW base < natToW (length (upd_sublist x2 base x3)))%word.
    rewrite length_upd_sublist.
    apply lt_goodSize.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r; omega.
    apply goodSize_weaken with (length (upd_sublist x2 base x3)); eauto.
    rewrite length_upd_sublist.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r; omega.
    apply goodSize_weaken with (length (upd_sublist x2 base x3)); eauto.
    rewrite length_upd_sublist.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r; omega.
    clear IHexpr1 IHexpr2; clear_fancy.
    evaluate auto_ext.

    apply IHexpr2.
    Focus 2.
    do 2 intro.
    apply H0.
    apply StringFacts.union_iff; auto.
    Focus 2.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r; omega.
    hnf; propxFo.
    apply postOk in H3.
    Focus 2.
    do 2 intro.
    apply H0.
    apply StringFacts.union_iff; auto.
    Focus 2.
    assert (max (depth expr1) (S (depth expr2)) >= depth expr1) by apply Max.le_max_l; omega.
    destruct H3; intuition idtac.
    apply H in H3; clear H; post.
    apply H5 in H2; clear H5; intuition idtac; simpl in *.
    destruct H5; intuition idtac.
    clear IHexpr1 IHexpr2; clear_fancy.
    rewrite evalInstrs_write_temp in *.
    unfold is_state in H5.
    assert (natToW base < natToW (length (upd_sublist x4 base x5)))%word.
    rewrite length_upd_sublist.
    apply lt_goodSize.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r; omega.
    apply goodSize_weaken with (length (upd_sublist x4 base x5)); eauto.
    rewrite length_upd_sublist.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r; omega.
    apply goodSize_weaken with (length (upd_sublist x4 base x5)); eauto.
    rewrite length_upd_sublist.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r; omega.
    evaluate auto_ext.
    destruct x; simpl in *.
    descend.
    unfold is_state.
    step auto_ext.
    replace (Regs x0 Sp) with (Regs s0 Sp) by congruence.
    step auto_ext.
    rewrite upd_length.
    rewrite length_upd_sublist; assumption.

    apply postOk in H2.
    Focus 2.
    do 2 intro.
    apply H0.
    apply StringFacts.union_iff; auto.
    Focus 2.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r; omega.
    post.
    post.
    apply postOk in H4.
    Focus 2.
    do 2 intro.
    apply H0.
    apply StringFacts.union_iff; auto.
    Focus 2.
    assert (max (depth expr1) (S (depth expr2)) >= depth expr1) by apply Max.le_max_l; omega.
    destruct H4; intuition idtac.
    apply H in H4; clear H.
    clear IHexpr1 IHexpr2; clear_fancy.
    post.
    apply H7 in H2; clear H7.
    post.
    rewrite evalInstrs_write_temp in *.
    unfold is_state in H7.
    assert (natToW base < natToW (length (upd_sublist x4 base x5)))%word.
    rewrite length_upd_sublist.
    apply lt_goodSize.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r; omega.
    apply goodSize_weaken with (length (upd_sublist x4 base x5)); eauto.
    rewrite length_upd_sublist.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r; omega.
    apply goodSize_weaken with (length (upd_sublist x4 base x5)); eauto.
    rewrite length_upd_sublist.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r; omega.
    evaluate auto_ext.
    assert (interp specs (![is_state (Regs x Sp) x3
      (Array.upd (upd_sublist x4 base x5) base (eval x3 expr1))* (fun stn sm => x2 (stn, sm))] (stn, x))).
    unfold is_state.
    step auto_ext.
    replace (Regs x0 Sp) with (Regs x Sp) by congruence.
    step auto_ext.
    apply H5 in H13.
    rewrite upd_length in H13.
    rewrite length_upd_sublist in H13.
    post.
    rewrite evalInstrs_binop_temp in *.
    destruct b.

    assert (natToW base < natToW (length (upd_sublist
      (Array.upd (upd_sublist x4 base x5) base
        (eval x3 expr1)) (S base) x6)))%word.
    rewrite length_upd_sublist; rewrite upd_length; assumption.
    clear H12; unfold is_state in H15.
    evaluate auto_ext.

    assert (natToW base < natToW (length (upd_sublist
      (Array.upd (upd_sublist x4 base x5) base
        (eval x3 expr1)) (S base) x6)))%word.
    rewrite length_upd_sublist; rewrite upd_length; assumption.
    clear H12; unfold is_state in H15.
    evaluate auto_ext.

    assert (natToW base < natToW (length (upd_sublist
      (Array.upd (upd_sublist x4 base x5) base
        (eval x3 expr1)) (S base) x6)))%word.
    rewrite length_upd_sublist; rewrite upd_length; assumption.
    clear H12; unfold is_state in H15.
    evaluate auto_ext.

    Transparent evalInstrs.
    simpl in H3.
    discriminate.
    Opaque evalInstrs.

    apply IHexpr1; auto.
    hnf; intros.
    apply H0.
    apply StringFacts.union_iff; auto.
    assert (max (depth expr1) (S (depth expr2)) >= depth expr1) by apply Max.le_max_l; omega.

    apply postOk in H2.
    Focus 2.
    do 2 intro.
    apply H0.
    apply StringFacts.union_iff; auto.
    Focus 2.
    assert (max (depth expr1) (S (depth expr2)) >= depth expr1) by apply Max.le_max_l; omega.
    post.
    apply H in H4; clear H; post.
    rewrite evalInstrs_write_temp in *.
    unfold is_state in H2.
    assert (natToW base < natToW (length x2))%word.
    apply lt_goodSize.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r; omega.
    apply goodSize_weaken with (length x2); eauto.
    eauto.
    clear IHexpr1 IHexpr2; clear_fancy.
    evaluate auto_ext.
    assert (interp specs (![is_state (Regs x Sp) x1 x2 * (fun stn sm => x0 (stn, sm))] (stn, x))).
    unfold is_state.
    step auto_ext.
    apply H5 in H2.
    post.
    assert (natToW base < natToW (length (upd_sublist x2 base x3)))%word.
    rewrite length_upd_sublist; assumption.
    clear H8; unfold is_state in H7.
    evaluate auto_ext.

    apply IHexpr2; auto.
    Focus 2.
    do 2 intro.
    apply H0.
    apply StringFacts.union_iff; auto.
    Focus 2.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r; omega.
    hnf; post.
    apply postOk in H3.
    Focus 2.
    do 2 intro.
    apply H0.
    apply StringFacts.union_iff; auto.
    Focus 2.
    assert (max (depth expr1) (S (depth expr2)) >= depth expr1) by apply Max.le_max_l; omega.
    post.
    apply H in H3; clear H; post.
    apply H5 in H2; clear H5; post.
    rewrite evalInstrs_write_temp in *.
    unfold is_state in H5.
    assert (natToW base < natToW (length (upd_sublist x4 base x5)))%word.
    rewrite length_upd_sublist.
    apply lt_goodSize.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r; omega.
    apply goodSize_weaken with (length (upd_sublist x4 base x5)); eauto.
    rewrite length_upd_sublist; auto.
    apply goodSize_weaken with (length (upd_sublist x4 base x5)); eauto.
    rewrite length_upd_sublist; auto.
    clear IHexpr1 IHexpr2; clear_fancy.
    evaluate auto_ext.
    destruct x; simpl in *.
    descend.
    unfold is_state.
    step auto_ext.
    replace (Regs x0 Sp) with (Regs s0 Sp) by congruence.
    step auto_ext.
    rewrite upd_length.
    rewrite length_upd_sublist; auto.

    apply postOk in H2.
    Focus 2.
    do 2 intro.
    apply H0.
    apply StringFacts.union_iff; auto.
    Focus 2.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r; omega.
    post.
    post.
    apply postOk in H4.
    Focus 2.
    do 2 intro.
    apply H0.
    apply StringFacts.union_iff; auto.
    Focus 2.
    assert (max (depth expr1) (S (depth expr2)) >= depth expr1) by apply Max.le_max_l; omega.
    destruct H4; intuition idtac.
    apply H in H4; clear H.
    clear IHexpr1 IHexpr2; clear_fancy.
    post.
    apply H7 in H2; clear H7.
    post.
    rewrite evalInstrs_write_temp in *.
    unfold is_state in H7.
    assert (natToW base < natToW (length (upd_sublist x4 base x5)))%word.
    rewrite length_upd_sublist.
    apply lt_goodSize.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r; omega.
    apply goodSize_weaken with (length (upd_sublist x4 base x5)); eauto.
    rewrite length_upd_sublist.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r; omega.
    apply goodSize_weaken with (length (upd_sublist x4 base x5)); eauto.
    rewrite length_upd_sublist.
    assert (max (depth expr1) (S (depth expr2)) >= S (depth expr2)) by apply Max.le_max_r; omega.
    evaluate auto_ext.
    assert (interp specs (![is_state (Regs x Sp) x3
      (Array.upd (upd_sublist x4 base x5) base (eval x3 expr1))* (fun stn sm => x2 (stn, sm))] (stn, x))).
    unfold is_state.
    step auto_ext.
    replace (Regs x0 Sp) with (Regs x Sp) by congruence.
    step auto_ext.
    apply H5 in H13.
    rewrite upd_length in H13.
    rewrite length_upd_sublist in H13.
    post.
    rewrite evalCond_temp in *.
    destruct t0.

    assert (natToW base < natToW (length (upd_sublist
      (Array.upd (upd_sublist x4 base x5) base
        (eval x3 expr1)) (S base) x6)))%word.
    rewrite length_upd_sublist; rewrite upd_length; assumption.
    clear H12; unfold is_state in H15.
    evaluate auto_ext.

    assert (natToW base < natToW (length (upd_sublist
      (Array.upd (upd_sublist x4 base x5) base
        (eval x3 expr1)) (S base) x6)))%word.
    rewrite length_upd_sublist; rewrite upd_length; assumption.
    clear H12; unfold is_state in H15.
    evaluate auto_ext.

    assert (natToW base < natToW (length (upd_sublist
      (Array.upd (upd_sublist x4 base x5) base
        (eval x3 expr1)) (S base) x6)))%word.
    rewrite length_upd_sublist; rewrite upd_length; assumption.
    clear H12; unfold is_state in H15.
    evaluate auto_ext.

    assert (natToW base < natToW (length (upd_sublist
      (Array.upd (upd_sublist x4 base x5) base
        (eval x3 expr1)) (S base) x6)))%word.
    rewrite length_upd_sublist; rewrite upd_length; assumption.
    clear H12; unfold is_state in H15.
    evaluate auto_ext.

    Transparent evalInstrs.
    discriminate.
    discriminate.
    discriminate.
    discriminate.
    Opaque evalInstrs.
  Qed.

  Definition compile (expr : Expr) (base : nat) : cmd imports modName.
    refine (Wrap imports imports_global modName (body expr base) (post expr base) (verifCond expr base) _ _).

    Opaque mult.

    Opaque mult.
    Opaque evalInstrs.

    abstract (unfold verifCond, syn_req; wrap0;
      match goal with
        | [ H : interp _ (Postcondition _ ?x) |- _ ] =>
          destruct x; eapply postOk in H; auto; destruct H; intuition; descend; eauto
      end).

    unfold verifCond, syn_req; wrap0.

    Opaque mult.
    Opaque evalInstrs.

    abstract (apply verifCondOk; auto).
  Defined.

End ExprComp.
