Require Import Bedrock.DepList Coq.Lists.List.
Require Import Bedrock.Expr Bedrock.SepExpr Bedrock.SymEval.
Require Import Bedrock.Memory Bedrock.SepIL Bedrock.SymIL.
Require Import Bedrock.Prover.
Require Import Bedrock.Reflection.

Set Implicit Arguments.
Set Strict Implicit.

Module BedrockPtsToEvaluator.

  Section hide_notation.
    Local Notation "'pcT'" := (tvType 0).
    Local Notation "'stT'" := (tvType 1).
    Local Notation "'wordT'" := (tvType 0).
    Local Notation "'ptrT'" := (tvType 0).

    Definition ptsto32_types_r : Env.Repr Expr.type :=
      Eval cbv beta iota zeta delta [ Env.listToRepr ] in
      let lst :=
        ILEnv.bedrock_type_W ::
        ILEnv.bedrock_type_setting_X_state :: nil
      in Env.listToRepr lst EmptySet_type.

    Section parametric.
      Variable types : list type.
      Variable Prover : ProverT types.

      Definition psummary := Facts Prover.

      Definition expr_equal (sum : psummary) (tv : tvar) (a b : expr types) : bool :=
        if Expr.expr_seq_dec a b
        then true
        else Prove Prover sum (Equal tv a b).

      Definition sym_read_word_ptsto32 (summ : psummary) (args : list (expr types)) (p : expr types)
        : option (expr types) :=
        match args with
          | p' :: v' :: nil =>
            if expr_equal summ ptrT p p' then Some v' else None
          | _ => None
        end.
      Definition sym_write_word_ptsto32 (summ : psummary) (args : list (expr types)) (p v : expr types)
        : option (list (expr types)) :=
        match args with
          | p' :: v' :: nil =>
            if expr_equal summ ptrT p p' then Some (p :: v :: nil) else None
          | _ => None
        end.
  End parametric.

  Definition MemEval_ptsto32 types : @MEVAL.PredEval.MemEvalPred types.
    apply MEVAL.PredEval.Build_MemEvalPred.
    apply sym_read_word_ptsto32.
    apply sym_write_word_ptsto32.
    exact (fun _ _ _ _ => None).
    exact (fun _ _ _ _ _ => None).
  Defined.

  Section correctness.
    Variable types' : list type.
    Definition types := Env.repr ptsto32_types_r types'.

    Local Notation "'pcT'" := (tvType 0).
    Local Notation "'stT'" := (tvType 1).
    Local Notation "'wordT'" := (tvType 0).
    Local Notation "'ptrT'" := (tvType 0).

    Definition ptsto32_ssig : SEP.predicate types pcT stT.
    refine (SEP.PSig _ _ _ (ptrT :: wordT :: nil) _).
    refine (ptsto32 _).
    Defined.

    Definition ptsto32_ssig_r : Env.Repr (SEP.predicate types pcT stT) :=
      Eval cbv beta iota zeta delta [ Env.listToRepr ] in
      let lst :=
        ptsto32_ssig :: nil
      in Env.listToRepr lst (SEP.Default_predicate _ _ _).

    Variable funcs : functions types.
    Variable Prover : ProverT types.
    Variable Prover_correct : ProverT_correct Prover funcs.

    Theorem expr_equal_correct :
      forall (sum : Facts Prover) (tv : tvar) (a b : expr types),
        expr_equal Prover sum tv a b = true ->
        forall uvars vars l r,
          exprD funcs uvars vars a tv = Some l ->
          exprD funcs uvars vars b tv = Some r ->
          Valid Prover_correct uvars vars sum ->
          l = r.
    Proof.
      unfold expr_equal. intros. revert H; consider (expr_seq_dec a b); intros; subst; auto.
      rewrite H1 in H0; inversion H0; auto.
      generalize (Prove_correct Prover_correct). intro XX; eapply XX in H; eauto; clear XX.
      unfold Provable, ValidProp in *. simpl in *.
      rewrite H0 in H. rewrite H1 in H. apply H. eauto.
    Qed.

    Ltac expose :=
      repeat (
        match goal with
          | [ H : match applyD _ _ ?A _ _ with
                    | Some _ => _
                    | None => False
                  end |- _ ] =>
          destruct A; simpl in H; try (exfalso; assumption)
          | [ H : context [ match exprD ?A ?B ?C ?D ?E with
                              | None => _
                              | Some _ => _
                            end ] |- _ ] =>
          revert H; case_eq (exprD A B C D E); simpl; intros;
            try (exfalso; assumption)
          | [ H : context [ match expr_equal ?A ?B ?C ?D with
                              | true => _
                              | false => _
                            end ] |- _ ] =>
          revert H; case_eq (expr_equal A B C D); intros;
            try (exfalso; congruence)
(*
          | [ H : expr_equal ?A ?B ?C ?D = true
            , H' : AllProvable _ _ _ ?A |- _ ] =>
          generalize (@expr_equal_correct _ _ _ _ H _ _ H'); clear H; intros
*)
          | [ H : Some _ = Some _ |- _ ] =>
            inversion H; clear H; subst
          | [ H : exprD _ _ _ _ _ = Some _ |- _ ] =>
            rewrite H in *
        end; simpl in * ).

    Lemma sym_read_word_ptsto32_correct : forall args uvars vars cs summ pe p ve m stn,
      sym_read_word_ptsto32 Prover summ args pe = Some ve ->
      Valid Prover_correct uvars vars summ ->
      exprD funcs uvars vars pe ptrT = Some p ->
      match
        applyD (exprD funcs uvars vars) (SEP.SDomain ptsto32_ssig) args _ (SEP.SDenotation ptsto32_ssig)
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
      simpl; intros.
      unfold sym_read_word_ptsto32 in H.
      repeat (destruct args; try congruence).
      revert H.
      case_eq (expr_equal Prover summ ptrT pe e); try congruence.
      intros.
      inversion H3; clear H3; subst.
      simpl in *.
      revert H2; consider (exprD funcs uvars vars e ptrT); intros; try contradiction.
      revert H3; consider (exprD funcs uvars vars ve ptrT); intros; try contradiction.
      eapply expr_equal_correct in H; eauto.
      unfold ST.satisfies in *. subst. PropXTac.propxFo.
    Qed.
    Require Import Bedrock.Nomega.

    Lemma sym_write_word_ptsto32_correct : forall args uvars vars cs summ pe p ve v m stn args',
      sym_write_word_ptsto32 Prover summ args pe ve = Some args' ->
      Valid Prover_correct uvars vars summ ->
      exprD funcs uvars vars pe ptrT = Some p ->
      exprD funcs uvars vars ve wordT = Some v ->
      match
        applyD (@exprD _ funcs uvars vars) (SEP.SDomain ptsto32_ssig) args _ (SEP.SDenotation ptsto32_ssig)
        with
        | None => False
        | Some p => ST.satisfies cs p stn m
      end ->
      match
        applyD (@exprD _ funcs uvars vars) (SEP.SDomain ptsto32_ssig) args' _ (SEP.SDenotation ptsto32_ssig)
        with
        | None => False
        | Some pr =>
          match ST.HT.smem_set_word (IL.explode stn) p v m with
            | None => False
            | Some sm' => ST.satisfies cs pr stn sm'
          end
      end.
    Proof.
      simpl; intros; expose.
      revert H; consider (expr_equal Prover summ ptrT pe e); intros; try congruence.
      inversion H6; clear H6; subst. simpl.
      rewrite H1. rewrite H2.

      consider (smem_set_word (IL.explode stn) p v m); intros; unfold ptsto32 in *.
      unfold ST.satisfies in *.
      PropXTac.propxFo.
      eapply smem_set_get_word_eq; eauto.
      eapply IL.implode_explode.
      unfold smem_set_word in H6.
      unfold H.footprint_w in H6.
      destruct (IL.explode stn v) as [ [ [ ] ] ].
      repeat match type of H6 with
               | match ?E with None => _ | _ => _ end = Some _ =>
                 let Heq := fresh "Heq" in case_eq E;
                   [ intros ? Heq | intro Heq ];
                   rewrite Heq in *; try discriminate
             end.
      repeat erewrite smem_set_get_neq by eauto.
      eapply expr_equal_correct in H; [ | eauto | eauto | eauto ].
      subst.
      auto.

      eapply expr_equal_correct in H; eauto. subst.
      unfold ST.satisfies in H5. PropXTac.propxFo.
      eapply smem_set_get_valid_word; eauto.
    Qed.
  End correctness.

  Definition MemEvaluator_ptsto32 types' : MEVAL.MemEvaluator types' (tvType 0) (tvType 1) :=
    Eval cbv beta iota zeta delta [ MEVAL.PredEval.MemEvalPred_to_MemEvaluator ] in
    @MEVAL.PredEval.MemEvalPred_to_MemEvaluator _ (tvType 0) (tvType 1) (MemEval_ptsto32 types') 0.

  Theorem MemEvaluator_ptsto32_correct types' funcs' preds'
    : @MEVAL.MemEvaluator_correct (Env.repr ptsto32_types_r types') (tvType 0) (tvType 1)
    (MemEvaluator_ptsto32 (Env.repr ptsto32_types_r types')) funcs' (Env.repr (ptsto32_ssig_r _) preds')
    (IL.settings * IL.state) (tvType 0) (tvType 0) (@IL_mem_satisfies types')
    (@IL_ReadWord types') (@IL_WriteWord types') (@IL_ReadByte types') (@IL_WriteByte types').
  Proof.
    intros. eapply MemPredEval_To_MemEvaluator_correct; try reflexivity;
    intros; unfold MemEval_ptsto32 in *; simpl in *; try discriminate.
    { generalize (@sym_read_word_ptsto32_correct types' funcs' P PE). simpl in *. intro.
      eapply H3 in H; eauto. }
    { generalize (@sym_write_word_ptsto32_correct types' funcs' P PE). simpl in *. intro.
      eapply H4 in H; eauto. }
  Qed.

  End hide_notation.

  Definition ptsto32_pack : MEVAL.MemEvaluatorPackage ptsto32_types_r (tvType 0) (tvType 1) (tvType 0) (tvType 0)
    IL_mem_satisfies IL_ReadWord IL_WriteWord IL_ReadByte IL_WriteByte :=

    @MEVAL.Build_MemEvaluatorPackage ptsto32_types_r (tvType 0) (tvType 1) (tvType 0) (tvType 0)
      IL_mem_satisfies IL_ReadWord IL_WriteWord IL_ReadByte IL_WriteByte
      (Env.nil_Repr EmptySet_type)
      (fun ts => Env.nil_Repr (Default_signature (Env.repr ptsto32_types_r ts)))
      (fun ts => Env.listToRepr (ptsto32_ssig ts :: nil)
        (SEP.Default_predicate (Env.repr ptsto32_types_r ts)
          (tvType 0) (tvType 1)))
      (fun ts => MemEvaluator_ptsto32 _)
      (fun ts fs ps => MemEvaluator_ptsto32_correct _ _).

End BedrockPtsToEvaluator.
