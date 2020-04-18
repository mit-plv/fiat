Require Import Coq.omega.Omega.
Require Import Coq.Bool.Bool.
Require Import Bedrock.DepList Coq.Lists.List.
Require Import Bedrock.Expr Bedrock.SepExpr Bedrock.SymEval.
Require Import Bedrock.Word Bedrock.Memory Bedrock.IL Bedrock.SepIL Bedrock.SymIL Bedrock.ILEnv.
Require Import Bedrock.EqdepClass.
Require Import Bedrock.Env Bedrock.Prover.
Require Import Bedrock.PropX Bedrock.PropXTac Bedrock.Nomega Coq.NArith.NArith.
Require Import Bedrock.sep.Array.

Set Implicit Arguments.

Fixpoint array8 (bs : list B) (p : W) : HProp :=
  match bs with
    | nil => Emp
    | b :: bs' => p =8> b * array8 bs' (p ^+ $1)
  end%Sep.

Fixpoint selN (bs : list B) (n : nat) : B :=
  match bs with
    | nil => wzero _
    | b :: bs' => match n with
                    | O => b
                    | S n' => selN bs' n'
                  end
  end.

Definition sel (bs : list B) (a : W) : B :=
  selN bs (wordToNat a).

Fixpoint updN (bs : list B) (n : nat) (v : B) : list B :=
  match bs with
    | nil => nil
    | b :: bs' => match n with
                    | O => v :: bs'
                    | S n' => b :: updN bs' n' v
                  end
  end.

Definition upd (bs : list B) (a : W) (v : B) : list B :=
  updN bs (wordToNat a) v.

Definition bedrock_type_B : type :=
  {| Expr.Impl := B
   ; Expr.Eqb := (fun _ _ => false)
   ; Expr.Eqb_correct := @ILEnv.all_false_compare _ |}.

Definition bedrock_type_listB : type :=
  {| Expr.Impl := list B
   ; Expr.Eqb := (fun _ _ => false)
   ; Expr.Eqb_correct := @ILEnv.all_false_compare _ |}.

Definition types_r : Env.Repr Expr.type :=
  Eval cbv beta iota zeta delta [ Env.listOptToRepr ] in
    let lst :=
      Some ILEnv.bedrock_type_W ::
      Some ILEnv.bedrock_type_setting_X_state ::
      None ::
      None ::
      Some ILEnv.bedrock_type_nat ::
      None ::
      None ::
      None ::
      None ::
      Some bedrock_type_B ::
      Some bedrock_type_listB :: nil
    in Env.listOptToRepr lst EmptySet_type.

Local Notation pcT := (tvType 0).
Local Notation stT := (tvType 1).
Local Notation wordT := (tvType 0).
Local Notation natT := (tvType 4).
Local Notation byteT := (tvType 9).
Local Notation listBT := (tvType 10).

Local Notation wplusF := 0.
Local Notation wltF := 4.
Local Notation natToWF := 5.
Local Notation lengthF := 15.
Local Notation selF := 16.
Local Notation updF := 17.
Local Notation btowF := 18.
Local Notation wtobF := 19.

Section parametric.
  Variable types' : list type.
  Definition types := repr types_r types'.
  Variable Prover : ProverT types.

  Definition natToW_r : signature types.
    refine {| Domain := natT :: nil; Range := wordT |}.
    exact natToW.
  Defined.

  Definition blength_r : signature types.
    refine {| Domain := listBT :: nil; Range := natT |}.
    exact (@length _).
  Defined.

  Definition sel_r : signature types.
    refine {| Domain := listBT :: wordT :: nil; Range := byteT |}.
    exact sel.
  Defined.

  Definition upd_r : signature types.
    refine {| Domain := listBT :: wordT :: byteT :: nil; Range := listBT |}.
    exact upd.
  Defined.

  Definition BtoW_r : signature types.
    refine {| Domain := byteT :: nil; Range := wordT |}.
    exact BtoW.
  Defined.

  Definition WtoB_r : signature types.
    refine {| Domain := wordT :: nil; Range := byteT |}.
    exact WtoB.
  Defined.

  Definition funcs_r : Env.Repr (signature types) :=
    Eval cbv beta iota zeta delta [ Env.listOptToRepr ] in
      let lst :=
        Some (ILEnv.wplus_r types) ::
        None ::
        None ::
        None ::
        Some (ILEnv.wlt_r types) ::
        Some (ILEnv.natToW_r types) ::
        None ::
        None ::
        None ::
        None ::
        None ::
        None ::
        None ::
        None ::
        None ::
        Some blength_r ::
        Some sel_r ::
        Some upd_r ::
        Some BtoW_r ::
        Some WtoB_r ::
        nil
      in Env.listOptToRepr lst (Default_signature _).

  Definition deref (e : expr types) : option (expr types * expr types) :=
    match e with
      | Func wplusF (base :: offset :: nil) => Some (base, offset)
      | _ => None
    end.

  Definition sym_read (summ : Prover.(Facts)) (args : list (expr types)) (p : expr types)
    : option (expr types) :=
    match args with
      | bs :: p' :: nil =>
        match deref p with
          | None => None
          | Some (base, offset) =>
            if Prover.(Prove) summ (Equal wordT p' base)
              && Prover.(Prove) summ (Func wltF (offset :: Func natToWF (Func lengthF (bs :: nil)
                :: nil) :: nil))
              then Some (Func btowF (Func selF (bs :: offset :: nil) :: nil))
              else None
        end
      | _ => None
    end.

  Definition sym_write (summ : Prover.(Facts)) (args : list (expr types)) (p v : expr types)
    : option (list (expr types)) :=
    match args with
      | bs :: p' :: nil =>
        match deref p with
          | None => None
          | Some (base, offset) =>
            if Prover.(Prove) summ (Equal wordT p' base)
              && Prover.(Prove) summ (Func wltF (offset :: Func natToWF (Func lengthF (bs :: nil)
                :: nil) :: nil))
              then Some (Func updF (bs :: offset :: Func wtobF (v :: nil) :: nil) :: p' :: nil)
              else None
        end
      | _ => None
    end.
End parametric.

Definition MemEval types' : @MEVAL.PredEval.MemEvalPred (types types').
  apply MEVAL.PredEval.Build_MemEvalPred.
  exact (fun _ _ _ _ => None).
  exact (fun _ _ _ _ _ => None).
  apply sym_read.
  apply sym_write.
Defined.

Section correctness.
  Variable types' : list type.
  Definition types0 := types types'.

  Definition ssig : SEP.predicate types0 pcT stT.
    refine (SEP.PSig _ _ _ (listBT :: wordT :: nil) _).
    exact array8.
  Defined.

  Definition ssig_r : Env.Repr (SEP.predicate types0 pcT stT) :=
    Eval cbv beta iota zeta delta [ Env.listOptToRepr ] in
      let lst :=
        None :: None :: None :: Some ssig :: nil
      in Env.listOptToRepr lst (SEP.Default_predicate _ _ _).

  Variable funcs' : functions types0.
  Definition funcs := Env.repr (funcs_r _) funcs'.

  Variable Prover : ProverT types0.
  Variable Prover_correct : ProverT_correct Prover funcs.

  Lemma deref_correct : forall uvars vars e w base offset,
    exprD funcs uvars vars e wordT = Some w
    -> deref e = Some (base, offset)
    -> exists wb, exists wo,
      exprD funcs uvars vars base wordT = Some wb
      /\ exprD funcs uvars vars offset wordT = Some wo
      /\ w = wb ^+ wo.
    destruct e; simpl; intuition; try discriminate.
    repeat (deconstruct' ltac:(simpl in *); []).
    eauto.
  Qed.

  Lemma sym_read_correct'' : forall specs stn bs sm p i,
    (i < length bs)%nat
    -> interp specs (array8 bs p stn sm)
    -> smem_get (p ^+ $ (i)) sm = Some (selN bs i).
    induction bs.

    simpl length; inversion 1.

    simpl length.
    unfold array8; fold array8.
    intros.
    apply simplify_fwd in H0.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H1.
    simpl in H0.

    destruct i; simpl selN.
    replace (p ^+ $ (0)) with p by W_eq.
    simpl in H1; intuition.
    eapply split_smem_get; eauto.

    rewrite natToW_S.
    rewrite wplus_assoc.
    eapply split_smem_get; eauto.
    right.
    apply IHbs; try omega.
    propxFo.
  Qed.

  Lemma array8_bound' : forall cs base stn bs m i,
    (0 < i < length bs)%nat
    -> base ^+ $ (i) = base
    -> interp cs (array8 bs base stn m)
    -> False.
    destruct bs; simpl length; intros.

    elimtype False; omega.

    simpl in H1.
    propxFo.
    destruct i; try omega.
    eapply sym_read_correct'' in H5.
    2: instantiate (1 := i); omega.
    match goal with
      | [ H : smem_get ?E _ = Some (selN _ _), H' : ?E' = base |- _ ] =>
        replace E with E' in H by (rewrite natToW_S; unfold natToW; W_eq)
    end.
    rewrite H0 in H5.
    destruct H1.
    eapply smem_get_disjoint; eauto.
  Qed.
  Require Import Coq.Arith.Arith.

  Lemma natToWord_pow2_alt : forall sz tht,
    tht = sz
    -> natToWord sz (pow2 tht) = $ (0).
    intros; subst; apply natToWord_pow2.
  Qed.

  Lemma array_boundAlt : forall tht cs bs base stn m,
    interp cs (array8 bs base stn m)
    -> tht = 32
    -> (length bs <= pow2 tht)%nat.
    intros.
    destruct (le_lt_dec (length bs) (pow2 tht)); auto.
    eapply array8_bound' in H; try tauto.
    instantiate (1 := pow2 tht); intuition.
    apply pow2_pos.
    rewrite wplus_alt.
    unfold wplusN, wordBinN.

    rewrite natToWord_pow2_alt by assumption.
    rewrite roundTrip_0.
    rewrite plus_0_r.
    apply natToWord_wordToNat.
  Qed.

  Lemma array8_bound : forall cs bs base stn m,
    interp cs (array8 bs base stn m)
    -> (length bs <= pow2 32)%nat.
    intros; eapply array_boundAlt; eauto.
  Qed.

  Lemma bounded : forall sz n m,
    (m <= pow2 sz)%nat
    -> (n < wordToNat (natToWord sz m))%nat
    -> (n < m)%nat.
    intros; destruct (eq_nat_dec m (pow2 sz)); subst.
    rewrite natToWord_pow2 in H0.
    rewrite roundTrip_0 in H0.
    nomega.
    rewrite wordToNat_natToWord_idempotent in H0; auto.
    pre_nomega.
    rewrite Npow2_nat.
    omega.
  Qed.

  Lemma sym_read_correct' : forall specs stn bs sm p i,
    i < natToW (length bs)
    -> interp specs (array8 bs p stn sm)
    -> smem_get (p ^+ i) sm = Some (sel bs i).
    intros.
    eapply sym_read_correct'' in H0.
    Focus 2.
    instantiate (1 := wordToNat i).
    red in H.
    apply Nlt_out in H.
    unfold natToW in *.
    repeat rewrite wordToN_nat in H.
    autorewrite with N in *.

    eapply bounded; eauto.
    eapply array8_bound; eauto.
    rewrite natToWord_wordToNat in H0; auto.
  Qed.

  Lemma sym_read_correct : forall P (PE : ProverT_correct P funcs),
    forall args uvars vars cs facts pe p ve stn st,
      sym_read P facts args pe = Some ve ->
      Valid PE uvars vars facts ->
      exprD funcs uvars vars pe wordT = Some p ->
      match
        applyD (exprD funcs uvars vars) (SEP.SDomain ssig) args _ (SEP.SDenotation ssig)
        with
        | None => False
        | Some p => ST.satisfies cs p stn st
      end ->
      match ST.HT.smem_get p st with
        | Some b => exprD funcs uvars vars ve wordT = Some (BtoW b)
        | _ => False
      end.
  Proof.
    simpl; intuition.
    do 3 (destruct args; simpl in *; intuition; try discriminate).
    generalize (deref_correct uvars vars pe); destr ltac:(simpl in *) (deref pe); intro Hderef.
    destruct p0.

    repeat match goal with
             | [ H : Valid _ _ _ _, _ : context[Prove P ?summ ?goal] |- _ ] =>
               match goal with
                 | [ _ : context[ValidProp _ _ _ goal] |- _ ] => fail 1
                 | _ => specialize (Prove_correct PE summ H (goal := goal)); intro
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
    specialize (Hderef _ _ _ eq_refl eq_refl); destruct Hderef as [ ? [ ] ]; intuition.
    subst.
    rewrite H4 in *.
    rewrite H7 in *.
    specialize (H6 (ex_intro _ _ (refl_equal _))).
    specialize (H3 (ex_intro _ _ (refl_equal _))); subst.
    red in H2.

    eapply sym_read_correct' in H2; eauto.
    rewrite H2; reflexivity.
  Qed.

  Lemma sym_write_correct'' : forall specs stn v bs p i st,
    (i < length bs)%nat
    -> interp specs (array8 bs p stn st)
    -> exists st', smem_set (p ^+ $ (i)) v st = Some st'
      /\ ST.satisfies specs (array8 (updN bs i v) p) stn st'.
    induction bs.

    inversion 1.

    simpl length.
    unfold array8; fold array8.
    intros.
    propxFo.
    destruct i.
    assert (Ho : smem_get p st = Some a) by (eapply split_smem_get; eauto).
    eapply smem_set_get_valid in Ho.
    generalize Ho; instantiate (1 := v); intro Ho'; clear Ho'.
    case_eq (smem_set p v st); intros; try congruence.
    do 2 esplit.
    replace (p ^+ $ (0)) with p by W_eq.
    eauto.
    simpl.
    propxFo.
    assert (smem_set p v x <> None) by (eapply smem_set_get_valid; eauto).
    case_eq (smem_set p v x); intros; try congruence.
    exists s0; exists x0; intuition.
    unfold split in *; intuition subst.
    eapply smem_set_disjoint; eauto.
    eapply split_set in H6; eauto.
    destruct H6.
    congruence.
    eapply smem_set_get_eq; eauto.
    erewrite smem_set_get_neq; eauto.

    eapply IHbs in H3.
    2: instantiate (1 := i); omega.
    destruct H3; intuition.
    rewrite natToW_S.
    rewrite wplus_assoc.
    exists (HT.join x x1).
    eapply split_set in H3.
    2: destruct H1; apply disjoint_comm; eauto.
    destruct H3.
    rewrite disjoint_join by (apply disjoint_comm; auto).
    destruct H1; subst.
    intuition.
    rewrite disjoint_join by auto.
    auto.
    propxFo.
    do 2 eexists; intuition.
    apply split_comm; apply disjoint_split_join; auto.
    auto.
    auto.
  Qed.

  Lemma sym_write_correct' : forall i bs p specs stn st v,
    i < natToW (length bs)
    -> interp specs (array8 bs p stn st)
    -> exists st', smem_set (p ^+ i) v st = Some st'
      /\ ST.satisfies specs (array8 (upd bs i v) p) stn st'.
    intros.
    eapply sym_write_correct'' in H0.
    Focus 2.
    instantiate (1 := wordToNat i).
    red in H.
    apply Nlt_out in H.
    unfold natToW in *.
    repeat rewrite wordToN_nat in H.
    autorewrite with N in *.
    eapply bounded; eauto.
    eapply array8_bound; eauto.
    rewrite natToWord_wordToNat in H0; eauto.
  Qed.

  Lemma sym_write_correct : forall P (PE : ProverT_correct P funcs),
    forall args uvars vars cs facts pe p ve v stn st args',
      sym_write P facts args pe ve = Some args' ->
      Valid PE uvars vars facts ->
      exprD funcs uvars vars pe wordT = Some p ->
      exprD funcs uvars vars ve wordT = Some v ->
      match
        applyD (@exprD _ funcs uvars vars) (SEP.SDomain ssig) args _ (SEP.SDenotation ssig)
        with
        | None => False
        | Some p => ST.satisfies cs p stn st
      end ->
      match
        applyD (@exprD _ funcs uvars vars) (SEP.SDomain ssig) args' _ (SEP.SDenotation ssig)
        with
        | None => False
        | Some pr =>
          match ST.HT.smem_set p (WtoB v) st with
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
             | [ H : Valid _ _ _ _, _ : context[Prove P ?summ ?goal] |- _ ] =>
               match goal with
                 | [ _ : context[ValidProp _ _ _ goal] |- _ ] => fail 1
                 | _ => specialize (Prove_correct PE summ H (goal := goal)); intro
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

    eapply sym_write_correct' in H3; eauto.
    destruct H3; intuition.
    rewrite H7; assumption.
  Qed.
End correctness.

Definition MemEvaluator types' : MEVAL.MemEvaluator (types types') (tvType 0) (tvType 1) :=
  Eval cbv beta iota zeta delta [ MEVAL.PredEval.MemEvalPred_to_MemEvaluator ] in
    @MEVAL.PredEval.MemEvalPred_to_MemEvaluator _ (tvType 0) (tvType 1) (MemEval types') 3.

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
  (fun ts => Env.listOptToRepr (None :: None :: None :: Some (ssig ts) :: nil)
    (SEP.Default_predicate (Env.repr types_r ts)
      (tvType 0) (tvType 1)))
  (fun ts => MemEvaluator _)
  (fun ts fs ps => MemEvaluator_correct _ _).
