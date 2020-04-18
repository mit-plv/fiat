Require Import Coq.omega.Omega.
Require Import Coq.Bool.Bool.
Require Import Bedrock.DepList Coq.Lists.List.
Require Import Bedrock.Expr Bedrock.SepExpr Bedrock.SymEval.
Require Import Bedrock.Word Bedrock.Memory Bedrock.IL Bedrock.SepIL Bedrock.SymIL Bedrock.ILEnv.
Require Import Bedrock.EqdepClass.
Require Import Bedrock.Env Bedrock.Prover.
Require Import Bedrock.PropX Bedrock.PropXTac Bedrock.Nomega Coq.NArith.NArith.

Set Implicit Arguments.

Definition array (ws : list W) (p : W) : HProp := ptsto32m _ p O ws.

Fixpoint div4 (n : nat) : option nat :=
  match n with
    | O => Some O
    | S (S (S (S n'))) => match div4 n' with
                            | None => None
                            | Some n'' => Some (S n'')
                          end
    | _ => None
  end.

Fixpoint selN (ws : list W) (n : nat) : W :=
  match ws with
    | nil => wzero _
    | w :: ws' => match n with
                    | O => w
                    | S n' => selN ws' n'
                  end
  end.

Definition sel (ws : list W) (a : W) : W :=
  selN ws (wordToNat a).

Fixpoint updN (ws : list W) (n : nat) (v : W) : list W :=
  match ws with
    | nil => nil
    | w :: ws' => match n with
                    | O => v :: ws'
                    | S n' => w :: updN ws' n' v
                  end
  end.

Definition upd (ws : list W) (a v : W) : list W :=
  updN ws (wordToNat a) v.

Definition bedrock_type_listW : type :=
  {| Expr.Impl := list W
   ; Expr.Eqb := (fun _ _ => false)
   ; Expr.Eqb_correct := @ILEnv.all_false_compare _ |}.

Definition types_r : Env.Repr Expr.type :=
  Eval cbv beta iota zeta delta [ Env.listOptToRepr ] in
    let lst :=
      Some ILEnv.bedrock_type_W ::
      Some ILEnv.bedrock_type_setting_X_state ::
      None ::
(*      None :: *)
      None ::
      Some ILEnv.bedrock_type_nat ::
      Some bedrock_type_listW :: nil
    in Env.listOptToRepr lst EmptySet_type.

Local Notation "'pcT'" := (tvType 0).
Local Notation "'stT'" := (tvType 1).
Local Notation "'wordT'" := (tvType 0).
Local Notation "'natT'" := (tvType 4).
Local Notation "'listWT'" := (tvType 5).

Local Notation "'wplusF'" := 0.
Local Notation "'wmultF'" := 2.
Local Notation "'wltF'" := 4.
Local Notation "'natToWF'" := 5.
Local Notation "'lengthF'" := 6.
Local Notation "'selF'" := 7.
Local Notation "'updF'" := 8.

Section parametric.
  Variable types' : list type.
  Definition types := repr types_r types'.
  Variable Prover : ProverT types.

  Definition natToW_r : signature types.
    refine {| Domain := natT :: nil; Range := wordT |}.
    exact natToW.
  Defined.

  Definition wlength_r : signature types.
    refine {| Domain := listWT :: nil; Range := natT |}.
    exact (@length _).
  Defined.

  Definition sel_r : signature types.
    refine {| Domain := listWT :: wordT :: nil; Range := wordT |}.
    exact sel.
  Defined.

  Definition upd_r : signature types.
    refine {| Domain := listWT :: wordT :: wordT :: nil; Range := listWT |}.
    exact upd.
  Defined.

  Definition funcs_r : Env.Repr (signature types) :=
    Eval cbv beta iota zeta delta [ Env.listOptToRepr ] in
      let lst :=
        Some (ILEnv.wplus_r types) ::
        None ::
        Some (ILEnv.wmult_r types) ::
(*        None :: *)
        None ::
        Some (ILEnv.wlt_r types) ::
        Some (ILEnv.natToW_r types) ::
        Some wlength_r ::
        Some sel_r ::
        Some upd_r ::
        nil
      in Env.listOptToRepr lst (Default_signature _).

  Definition deref (e : expr types) : option (expr types * expr types) :=
    match e with
      | Func wplusF (base :: offset :: nil) =>
        match offset with
          | Func wmultF (Func natToWF (Const t k :: nil) :: offset :: nil) =>
            match t return tvarD types t -> _ with
              | natT => fun k => match k with
                                   | 4 => Some (base, offset)
                                   | _ => None
                                 end
              | _ => fun _ => None
            end k
          | Func natToWF (Const t k :: nil) =>
            match t return tvarD types t -> _ with
              | natT => fun k => match div4 k with
                                   | None => None
                                   | Some k' => Some (base, Func natToWF (Const (types := types) (t := natT) k'
                                     :: nil))
                                 end
              | _ => fun _ => None
            end k
          | _ => None
        end
      | _ => None
    end.

  Definition sym_read (summ : Prover.(Facts)) (args : list (expr types)) (p : expr types)
    : option (expr types) :=
    match args with
      | ws :: p' :: nil =>
        match deref p with
          | None => None
          | Some (base, offset) =>
            if Prover.(Prove) summ (Equal wordT p' base)
              && Prover.(Prove) summ (Func wltF (offset :: Func natToWF (Func lengthF (ws :: nil)
                :: nil) :: nil))
              then Some (Func selF (ws :: offset :: nil))
              else None
        end
      | _ => None
    end.

  Definition sym_write (summ : Prover.(Facts)) (args : list (expr types)) (p v : expr types)
    : option (list (expr types)) :=
    match args with
      | ws :: p' :: nil =>
        match deref p with
          | None => None
          | Some (base, offset) =>
            if Prover.(Prove) summ (Equal wordT p' base)
              && Prover.(Prove) summ (Func wltF (offset :: Func natToWF (Func lengthF (ws :: nil)
                :: nil) :: nil))
              then Some (Func updF (ws :: offset :: v :: nil) :: p' :: nil)
              else None
        end
      | _ => None
    end.
End parametric.

Definition MemEval types' : @MEVAL.PredEval.MemEvalPred (types types').
  apply MEVAL.PredEval.Build_MemEvalPred.
  apply sym_read.
  apply sym_write.
  exact (fun _ _ _ _ => None).
  exact (fun _ _ _ _ _ => None).
Defined.

Ltac destr' E := destruct E. (*case_eq E; intros;
  try match goal with
        | [ H : _ = _ |- _ ] => rewrite H in *
      end.*)

Ltac destr simp E :=
  match E with
    | context[match _ with None => _ | _ => _ end] => fail 1
    | div4 _ => fail 1
    | _ => destr' E; discriminate || tauto
    | _ => destr' E; try (discriminate || tauto); [simp]
  end.

Ltac destr2 simp E :=
  match E with
    | context[match _ with None => _ | _ => _ end] => fail 1
    | div4 _ => fail 1
    | _ => destr' E; try (discriminate || tauto); [simp]
    | _ => destr' E; try (discriminate || tauto); [ | ]; simp
  end.

Ltac stripSuffix E :=
  match E with
    | ?E = _ => stripSuffix E
    | ?E _ => stripSuffix E
    | ?E _ _ => stripSuffix E
    | _ => E
  end.

Ltac doMatch simp P :=
  match P with
    | match ?E with 0 => _ | _ => _ end => destr2 simp E
    | match ?E with nil => _ | _ => _ end => destr simp E
    | match ?E with Const _ _ => _ | _ => _ end => destr2 simp E
    | match ?E with tvProp => _ | _ => _ end => destr simp E
    | match ?E with None => _ | _ => _ end => destr simp E
    | match ?E with left _ => _ | _ => _ end => destr2 simp E
  end.

Ltac deconstruct' simp := match goal with
                            | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst; simp
                            | [ H : ?P |- _ ] =>
                              let P := stripSuffix P in
                                doMatch simp P
                                || match P with
                                     | match ?P with None => _ | _ => _ end =>
                                       let P := stripSuffix P in
                                         doMatch simp P
                                   end
                          end.

Ltac deconstruct := repeat deconstruct' ltac:(simpl in *).

Section correctness.
  Variable types' : list type.
  Definition types0 := types types'.

  Definition ssig : SEP.predicate types0 pcT stT.
    refine (SEP.PSig _ _ _ (listWT :: wordT :: nil) _).
    exact array.
  Defined.

  Definition ssig_r : Env.Repr (SEP.predicate types0 pcT stT) :=
    Eval cbv beta iota zeta delta [ Env.listOptToRepr ] in
      let lst :=
        None :: Some ssig :: nil
      in Env.listOptToRepr lst (SEP.Default_predicate _ _ _).

  Variable funcs' : functions types0.
  Definition funcs := Env.repr (funcs_r _) funcs'.

  Variable Prover : ProverT types0.
  Variable Prover_correct : ProverT_correct Prover funcs.

  Lemma div4_correct' : forall n0 n m, (n < n0)%nat
    -> div4 n = Some m
    -> n = 4 * m.
    induction n0; simpl; intuition.
    destruct n; simpl in *.
    injection H0; omega.
    repeat destr ltac:(simpl in *) n.
    specialize (IHn0 n).
    destruct (div4 n).
    injection H0.
    rewrite (IHn0 n1); auto; omega.
    discriminate.
  Qed.

  Lemma div4_correct : forall n m, div4 n = Some m
    -> n = 4 * m.
    intros; eapply div4_correct'; eauto.
  Qed.

  Lemma deref_correct : forall uvars vars e w base offset,
    exprD funcs uvars vars e wordT = Some w
    -> deref e = Some (base, offset)
    -> exists wb, exists wo,
      exprD funcs uvars vars base wordT = Some wb
      /\ exprD funcs uvars vars offset wordT = Some wo
      /\ w = wb ^+ $4 ^* wo.
    destruct e; simpl; intuition; try discriminate.
    repeat (deconstruct' ltac:(simpl in *); []).
    case_eq (exprD funcs uvars vars e wordT); intros;
      match goal with
        | [ H : _ = _ |- _ ] => rewrite H in *
      end; try discriminate.
    deconstruct; eauto.
    match goal with
      | [ _ : context[div4 ?N] |- _ ] => specialize (div4_correct N); destruct (div4 N)
    end; try discriminate.
    deconstruct.
    specialize (H2 _ (refl_equal _)); subst.
    repeat (esplit || eassumption).
    replace (n + (n + (n + (n + 0)))) with (n * 4) by omega.
    rewrite natToW_times4.
    W_eq.
  Qed.

  Fixpoint ptsto32m' sos (a : W) (offset : nat) (vs : list W) : hpropB sos :=
    match vs with
      | nil => Emp
      | v :: vs' => (a ^+ $ (offset)) =*> v * ptsto32m' sos a (4 + offset) vs'
    end%Sep.

  Theorem ptsto32m'_in : forall a cs stn vs offset m,
    interp cs (ptsto32m _ a offset vs stn m)
    -> interp cs (ptsto32m' _ a offset vs stn m).
    induction vs.

    auto.

    unfold ptsto32m, ptsto32m'.
    fold ptsto32m; fold ptsto32m'.
    destruct vs; destruct offset; intros.

    replace (a ^+ $0) with a by W_eq.
    simpl.
    propxFo.
    exists m.
    exists smem_emp; intuition.
    apply split_comm; apply split_a_semp_a.
    reflexivity.

    unfold ptsto32m'.
    apply simplify_bwd.
    exists m.
    exists smem_emp; intuition.
    split.
    apply split_comm; apply split_a_semp_a.
    split.
    apply simplify_fwd; assumption.
    split.
    constructor.
    reflexivity.

    replace (a ^+ $0) with a by W_eq.
    apply simplify_fwd in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    apply simplify_bwd in H0.
    apply simplify_bwd in H1.
    apply simplify_bwd.
    exists x.
    exists x0.
    split; auto.
    split.
    apply simplify_fwd; assumption.
    apply simplify_fwd; auto.

    apply simplify_fwd in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    apply simplify_bwd in H0.
    apply simplify_bwd in H1.
    apply simplify_bwd.
    exists x.
    exists x0.
    split; auto.
    split.
    apply simplify_fwd; assumption.
    apply simplify_fwd; auto.
  Qed.

  Lemma smem_read_correct'' : forall cs base stn ws offset i m,
    interp cs (ptsto32m' _ base (offset * 4) ws stn m)
    -> (i < length ws)%nat
    -> smem_get_word (implode stn) (base ^+ $ ((offset + i) * 4)) m = Some (selN ws i).
    induction ws.

    simpl length.
    intros.
    elimtype False.
    nomega.

    simpl length.
    unfold ptsto32m'.
    fold ptsto32m'.
    intros.
    destruct i; simpl selN.
    replace (offset + 0) with offset by omega.
    apply simplify_fwd in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H1.
    destruct H1.
    eapply split_smem_get_word; eauto.

    apply simplify_fwd in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H1.
    apply simplify_bwd in H2.
    replace (4 + offset * 4) with (S offset * 4) in H2 by omega.
    eapply (IHws _ i) in H2.
    rewrite <- H2.
    erewrite split_smem_get_word.
    eauto.
    eapply split_comm; eauto.
    left.
    rewrite <- H2.
    do 3 f_equal.
    omega.
    omega.
  Qed.

  Lemma smem_get_disjoint : forall a w1 w2 dom m1 m2,
    disjoint' dom m1 m2
    -> smem_get' dom a m1 = Some w1
    -> smem_get' dom a m2 = Some w2
    -> False.
    induction dom; simpl; intuition.
    discriminate.
    destruct (H.addr_dec a0 a); subst; try congruence.
    eauto.
    destruct (H.addr_dec a0 a); subst; try congruence.
    eauto.
  Qed.

  Lemma smem_get_word_disjoint : forall a m1 m2 w1 w2 addrs,
    disjoint m1 m2
    -> smem_get_word addrs a m1 = Some w1
    -> smem_get_word addrs a m2 = Some w2
    -> False.
    unfold smem_get_word; intros.
    destruct (H.footprint_w a) as [ [ [ ] ] ].
    case_eq (smem_get a0 m1); [ intros ? Heq | intros Heq ]; rewrite Heq in *; try discriminate.
    case_eq (smem_get a0 m2); [ intros ? Heq' | intros Heq' ]; rewrite Heq' in *; try discriminate.
    eapply smem_get_disjoint; eauto.
  Qed.

  Lemma array_bound' : forall cs base stn ws m i,
    (0 < i < length ws)%nat
    -> base ^+ $ (i * 4) = base
    -> interp cs (ptsto32m' _ base 0 ws stn m)
    -> False.
    destruct ws; simpl length; intros.

    elimtype False; omega.

    simpl in H1.
    propxFo.
    destruct i; try omega.
    generalize (@smem_read_correct'' cs base stn ws 1 i x0).
    simpl plus.
    rewrite H0.
    rewrite wplus_comm in H4.
    rewrite wplus_unit in H4.
    intuition.
    assert (i < length ws)%nat by omega; intuition.
    destruct H1.
    eapply smem_get_word_disjoint; eauto.
  Qed.

  Lemma pow2_pos : forall n, (pow2 n > 0)%nat.
    induction n; simpl; omega.
  Qed.

  Lemma pow2_monotone : forall n m,
    (n < m)%nat
    -> (pow2 n < pow2 m)%nat.
    induction 1; simpl; intuition.
    specialize (pow2_pos n).
    omega.
  Qed.

  Lemma pow2_mult : forall m n,
    pow2 n * pow2 m = pow2 (n + m).
    induction n; simpl; intuition.
    repeat rewrite <- IHn.
    repeat rewrite <- plus_n_O.
    apply Mult.mult_plus_distr_r.
  Qed.
  Require Import Coq.Arith.Arith.

  Lemma array_bound : forall cs ws base stn m,
    interp cs (array ws base stn m)
    -> (length ws < pow2 32)%nat.
    intros.
    destruct (lt_dec (length ws) (pow2 32)); auto.
    elimtype False.
    apply ptsto32m'_in in H.
    apply (@array_bound' _ _ _ _ _ (pow2 30)) in H; auto.
    split.
    unfold pow2; omega.
    specialize (@pow2_monotone 30 32).
    omega.
    change (pow2 30 * 4) with (pow2 30 * pow2 2).
    rewrite pow2_mult.
    simpl plus.
    clear.
    rewrite wplus_alt.
    unfold wplusN, wordBinN.
    rewrite natToWord_pow2.
    rewrite roundTrip_0.
    rewrite plus_0_r.
    apply natToWord_wordToNat.
  Qed.

  Lemma smem_read_correct' : forall cs base stn ws i m,
    interp cs (array ws base stn m)
    -> i < $ (length ws)
    -> smem_get_word (implode stn) (base ^+ $4 ^* i) m = Some (sel ws i).
    unfold sel; intros; rewrite <- (@smem_read_correct'' cs base stn ws 0 (wordToNat i) m).
    f_equal.
    simpl plus.
    rewrite natToW_times4.
    unfold natToW.
    rewrite natToWord_wordToNat.
    W_eq.

    apply ptsto32m'_in; auto.

    red in H0.
    apply Nlt_out in H0.
    repeat rewrite wordToN_nat in *.
    repeat rewrite Nat2N.id in *.
    rewrite wordToNat_natToWord_idempotent in H0; auto.
    apply array_bound in H.
    apply Nlt_in.
    rewrite Nat2N.id.
    rewrite Npow2_nat.
    assumption.
  Qed.

  Lemma sym_read_correct : forall args uvars vars cs summ pe p ve m stn,
    sym_read Prover summ args pe = Some ve ->
    Valid Prover_correct uvars vars summ ->
    exprD funcs uvars vars pe wordT = Some p ->
    match
      applyD (exprD funcs uvars vars) (SEP.SDomain ssig) args _ (SEP.SDenotation ssig)
      with
      | None => False
      | Some p => ST.satisfies cs p stn m
    end ->
    match exprD funcs uvars vars ve wordT with
      | Some v =>
        ST.HT.smem_get_word (IL.implode stn) p m = Some v
      | _ => False
    end.
  Proof.
    simpl; intuition.
    do 3 (destruct args; simpl in *; intuition; try discriminate).
    generalize (deref_correct uvars vars pe); destr ltac:(simpl in *) (deref pe); intro Hderef.
    destruct p0.

    repeat match goal with
             | [ H : Valid _ _ _ _, _ : context[Prove Prover ?summ ?goal] |- _ ] =>
               match goal with
                 | [ _ : context[ValidProp _ _ _ goal] |- _ ] => fail 1
                 | _ => specialize (Prove_correct Prover_correct summ H (goal := goal)); intro
               end
           end; unfold ValidProp in *; simpl in *.

    match goal with
      | [ _ : (if ?E then _ else _) = Some _ |- _ ] => case_eq E; intro Heq; rewrite Heq in *
    end; try discriminate.
    unfold types0 in *; simpl in *.
    unfold Provable in *; simpl in *.
    deconstruct.
    repeat match goal with
             | [ H : _ |- _ ] => apply andb_prop in H; intuition
           end.
    rewrite H1 in *.
    specialize (Hderef _ _ _ (refl_equal _) (refl_equal _)); destruct Hderef as [ ? [ ] ]; intuition.
    subst.
    simpl in *.
    rewrite H4 in *.
    rewrite H7 in *.
    specialize (H6 (ex_intro _ _ (refl_equal _))).
    specialize (H3 (ex_intro _ _ (refl_equal _))); subst.
    red in H2.

    eapply smem_read_correct'; eauto.
  Qed.

  Theorem ptsto32m'_out : forall a cs stn vs offset m,
    interp cs (ptsto32m' _ a offset vs stn m)
    -> interp cs (ptsto32m _ a offset vs stn m).
    induction vs.

    auto.

    unfold ptsto32m, ptsto32m'.
    fold ptsto32m; fold ptsto32m'.
    destruct vs; destruct offset; intros.

    replace (a ^+ $0) with a in * by W_eq.
    simpl.
    propxFo.
    rewrite <- H1.
    f_equal.
    eapply split_semp.
    apply split_comm; eauto.
    auto.

    apply split_comm in H3.
    generalize (split_semp _ _ _ H3 H8); intro; subst.
    auto.

    apply simplify_fwd in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    apply simplify_bwd in H0.
    replace m with x; auto.
    symmetry; eapply split_semp.
    apply split_comm; eauto.
    simpl in H1; tauto.

    replace (a ^+ $0) with a in * by W_eq.
    apply simplify_fwd in H.
    apply simplify_bwd.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    exists x; exists x0; split.
    auto.
    split; auto.
    apply simplify_fwd.
    apply simplify_bwd in H1.
    auto.

    apply simplify_fwd in H.
    apply simplify_bwd.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    exists x; exists x0; split.
    auto.
    split; auto.
    apply simplify_fwd.
    apply simplify_bwd in H1.
    auto.
  Qed.

  Lemma smem_write_correct'' : forall cs base stn v ws i m offset,
    (i < length ws)%nat
    -> interp cs (ptsto32m' _ base (offset * 4) ws stn m)
    -> exists m', smem_set_word (explode stn) (base ^+ $4 ^* $ (offset + i)) v m = Some m'
      /\ ST.satisfies cs (ptsto32m' _ base (offset * 4) (updN ws i v)) stn m'.
    induction ws; simpl length; intros.

    inversion H.

    unfold ptsto32m' in *.
    fold ptsto32m' in *.
    destruct i; simpl updN.
    rewrite wmult_comm.
    rewrite <- natToW_times4.
    replace (offset + 0) with offset by omega.
    unfold ptsto32m'.
    fold ptsto32m'.
    apply simplify_fwd in H0.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H1.
    hnf in H1.
    unfold natToW.
    destruct H1.
    specialize (smem_set_get_valid_word _ (explode stn) _ _ v _ H1).
    match goal with
      | [ |- ?E <> None -> _ ] => case_eq E; intuition
    end.
    exists (HT.join s x0); split.
    destruct H0; subst.
    eapply split_set_word in H4; intuition eauto.

    apply simplify_bwd.
    exists s; exists x0.
    split.
    apply disjoint_split_join.
    eapply split_set_word in H4; intuition eauto.
    destruct H0; auto.
    split; auto.
    hnf.
    split.
    eapply smem_set_get_word_eq.
    2: eauto.
    apply implode_explode.

    intros.
    unfold smem_set_word in H4.
    unfold H.footprint_w in H4.
    destruct (explode stn v) as [ [ [ ] ] ].
    repeat match type of H4 with
             | match ?E with None => _ | _ => _ end = Some _ =>
               let Heq := fresh "Heq" in case_eq E;
                 [ intros ? Heq | intro Heq ];
                 rewrite Heq in *; try discriminate
           end.
    intuition idtac.
    repeat erewrite smem_set_get_neq by eauto.
    auto.

    apply simplify_fwd in H0.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H1.
    apply simplify_bwd in H2.
    replace (4 + offset * 4) with (S offset * 4) in H2 by omega.
    apply (IHws i) in H2; clear IHws; try omega.
    destruct H2; intuition.
    exists (HT.join x x1); split; auto.
    replace (offset + S i) with (S offset + i) by omega.
    destruct H0; subst.
    eapply split_set_word in H3.
    2: apply disjoint_comm; eauto.
    rewrite disjoint_join by auto.
    rewrite (disjoint_join x x1) by (apply disjoint_comm; tauto).
    tauto.

    unfold ptsto32m'.
    fold ptsto32m'.
    apply simplify_bwd.
    exists x; exists x1.
    split.
    apply disjoint_split_join.
    destruct H0; auto.
    eapply split_set_word in H3.
    2: apply disjoint_comm; eauto.
    apply disjoint_comm; tauto.
    split; auto.
  Qed.

  Lemma smem_write_correct' : forall i ws cs base stn m v,
    i < natToW (length ws)
    -> interp cs (array ws base stn m)
    -> exists m', smem_set_word (explode stn) (base ^+ $4 ^* i) v m = Some m'
      /\ ST.satisfies cs (array (upd ws i v) base) stn m'.
    intros.
    destruct (@smem_write_correct'' cs base stn v ws (wordToNat i) m 0).

    red in H.
    apply Nlt_out in H.
    repeat rewrite wordToN_nat in *.
    repeat rewrite Nat2N.id in *.
    rewrite wordToNat_natToWord_idempotent in H; auto.
    apply array_bound in H0.
    apply Nlt_in.
    rewrite Nat2N.id.
    rewrite Npow2_nat.
    assumption.

    apply ptsto32m'_in; auto.

    intuition.
    simpl plus in *.
    simpl mult in *.
    rewrite natToWord_wordToNat in H2.
    exists x; split; auto.
    apply ptsto32m'_out; auto.
  Qed.

  Lemma sym_write_correct : forall args uvars vars cs summ pe p ve v m stn args',
    sym_write Prover summ args pe ve = Some args' ->
    Valid Prover_correct uvars vars summ ->
    exprD funcs uvars vars pe wordT = Some p ->
    exprD funcs uvars vars ve wordT = Some v ->
    match
      applyD (@exprD _ funcs uvars vars) (SEP.SDomain ssig) args _ (SEP.SDenotation ssig)
      with
      | None => False
      | Some p => ST.satisfies cs p stn m
    end ->
    match
      applyD (@exprD _ funcs uvars vars) (SEP.SDomain ssig) args' _ (SEP.SDenotation ssig)
      with
      | None => False
      | Some pr =>
        match ST.HT.smem_set_word (IL.explode stn) p v m with
          | None => False
          | Some sm' => ST.satisfies cs pr stn sm'
        end
    end.
  Proof.
    simpl; intuition.
    do 3 (destruct args; simpl in *; intuition; try discriminate).
    generalize (deref_correct uvars vars pe); destr ltac:(simpl in *) (deref pe); intro Hderef.
    destruct p0.

    repeat match goal with
             | [ H : Valid _ _ _ _, _ : context[Prove Prover ?summ ?goal] |- _ ] =>
               match goal with
                 | [ _ : context[ValidProp _ _ _ goal] |- _ ] => fail 1
                 | _ => specialize (Prove_correct Prover_correct summ H (goal := goal)); intro
               end
           end; unfold ValidProp in *; simpl in *.

    match goal with
      | [ _ : (if ?E then _ else _) = Some _ |- _ ] => case_eq E; intro Heq; rewrite Heq in *
    end; try discriminate.
    unfold types0 in *; simpl in *.
    unfold Provable in *; simpl in *.
    deconstruct.
    repeat match goal with
             | [ H : _ |- _ ] => apply andb_prop in H; intuition
           end.
    rewrite H1 in *.
    rewrite H2 in *.
    specialize (Hderef _ _ _ (refl_equal _) (refl_equal _)); destruct Hderef as [ ? [ ] ]; intuition.
    subst.
    simpl in *.
    rewrite H8 in *.
    rewrite H5 in *.
    specialize (H7 (ex_intro _ _ (refl_equal _))).
    specialize (H4 (ex_intro _ _ (refl_equal _))); subst.
    red in H3.

    eapply smem_write_correct' in H3; eauto.
    destruct H3; intuition.
    rewrite H7; assumption.
  Qed.
End correctness.

Definition MemEvaluator types' : MEVAL.MemEvaluator (types types') (tvType 0) (tvType 1) :=
  Eval cbv beta iota zeta delta [ MEVAL.PredEval.MemEvalPred_to_MemEvaluator ] in
    @MEVAL.PredEval.MemEvalPred_to_MemEvaluator _ (tvType 0) (tvType 1) (MemEval types') 1.

Theorem MemEvaluator_correct types' funcs' preds'
  : @MEVAL.MemEvaluator_correct (Env.repr types_r types') (tvType 0) (tvType 1)
  (MemEvaluator (Env.repr types_r types')) (funcs funcs') (Env.repr (ssig_r _) preds')
  (IL.settings * IL.state) (tvType 0) (tvType 0)
  (@IL_mem_satisfies (types types')) (@IL_ReadWord (types types')) (@IL_WriteWord (types types'))
  (@IL_ReadByte (types types')) (@IL_WriteByte (types types')).
Proof.
  intros. eapply (@MemPredEval_To_MemEvaluator_correct (types types')); try reflexivity;
  intros; unfold MemEval in *; simpl in *; try discriminate.
  { generalize (@sym_read_correct types' funcs' P PE). simpl in *. intro.
    eapply H3 in H; eauto. }
  { generalize (@sym_write_correct types' funcs' P PE). simpl in *. intro.
    eapply H4 in H; eauto. }
Qed.

Definition pack : MEVAL.MemEvaluatorPackage types_r (tvType 0) (tvType 1) (tvType 0) (tvType 0)
  IL_mem_satisfies IL_ReadWord IL_WriteWord IL_ReadByte IL_WriteByte :=

  @MEVAL.Build_MemEvaluatorPackage types_r (tvType 0) (tvType 1) (tvType 0) (tvType 0)
  IL_mem_satisfies IL_ReadWord IL_WriteWord IL_ReadByte IL_WriteByte
  types_r
  funcs_r
  (fun ts => Env.listOptToRepr (None :: Some (ssig ts) :: nil)
    (SEP.Default_predicate (Env.repr types_r ts)
      (tvType 0) (tvType 1)))
  (fun ts => MemEvaluator _)
  (fun ts fs ps => MemEvaluator_correct _ _).
