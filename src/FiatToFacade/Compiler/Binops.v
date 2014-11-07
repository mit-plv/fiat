Require Import FiatToFacade.Compiler.Prerequisites.

Unset Implicit Arguments.

Lemma compile_binop_simple :
  forall {av env},
  forall op vret tw1 tw2,
  forall w1 w2,
  forall init_knowledge init_scas init_adts post_w1_adts final_adts,
    tw1 <> tw2 ->
    ~ StringMap.In tw1 init_scas ->
    ~ StringMap.In tw2 init_scas ->
    ~ StringMap.In vret final_adts ->
    refine (@Prog av env init_knowledge
                  init_scas ([vret >sca> IL.evalBinop op w1 w2] :: init_scas)
                  init_adts final_adts)
           (pw1  <- (@Prog av env init_knowledge
                           init_scas ([tw1 >sca> w1] :: init_scas)
                           init_adts post_w1_adts);
            pw2  <- (@Prog av env init_knowledge
                           ([tw1 >sca> w1] :: init_scas)
                           ([tw2 >sca> w2] :: [tw1 >sca> w1] :: init_scas)
                           post_w1_adts final_adts);
            ret (pw1; pw2; Assign vret (Binop op tw1 tw2))%facade)%comp.
Proof.
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  (* Safe *)

  repeat (safe_seq; intros).
  specialize_states.
  scas_adts_mapsto.

  (*TODO: Prettier way of doing this? *)
  assert (forall k : StringMap.key,
            List.In k (AllVariables (Binop op (Var tw1) (Var tw2))) ->
            exists v : W, (st'0) [k >> SCA av v])
    as temp
    by (unfold AllVariables; simpl; intros; intuition; eexists; subst; eassumption).
  destruct (eval_expr_some_sca (Binop op (Var tw1) (Var tw2)) st'0 temp).

  econstructor; try eassumption.
  eapply not_in_adts_not_mapsto_adt; eauto.

  (* RunsTo *)
  
  intros;
    repeat inversion_facade;
    specialize_states;
    scas_adts_mapsto;
    unfold eval, eval_binop_m in *;
    repeat (subst_find; simpl in *);
    autoinj.

  split;
    rewrite_Eq_in_goal;
    [ repeat remove_not_in;
      apply SomeSCAs_chomp
    | apply add_adts_pop_sca ];
    assumption.
Qed.  

Lemma compile_test_simple :
  forall {av env},
  forall op vret tw1 tw2,
  forall w1 w2,
  forall init_knowledge init_scas init_adts post_w1_adts final_adts,
    tw1 <> tw2 ->
    ~ StringMap.In tw1 init_scas ->
    ~ StringMap.In tw2 init_scas ->
    ~ StringMap.In vret final_adts ->
    refine (@Prog av env init_knowledge
                  init_scas ([vret >sca> BoolToW (IL.evalTest op w1 w2)] :: init_scas)
                  init_adts final_adts)
           (pw1  <- (@Prog av env init_knowledge
                           init_scas ([tw1 >sca> w1] :: init_scas)
                           init_adts post_w1_adts);
            pw2  <- (@Prog av env init_knowledge
                           ([tw1 >sca> w1] :: init_scas)
                           ([tw2 >sca> w2] :: [tw1 >sca> w1] :: init_scas)
                           post_w1_adts final_adts);
            ret (pw1; pw2; Assign vret (TestE op tw1 tw2))%facade)%comp.
Proof.
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  (* Safe *)

  repeat (safe_seq; intros).
  specialize_states.
  scas_adts_mapsto.

  (*TODO: Prettier way of doing this? *)
  assert (forall k : StringMap.key,
            List.In k (AllVariables (TestE op (Var tw1) (Var tw2))) ->
            exists v : W, (st'0) [k >> SCA av v])
    as temp
    by (unfold AllVariables; simpl; intros; intuition; eexists; subst; eassumption).
  destruct (eval_expr_some_sca (TestE op (Var tw1) (Var tw2)) st'0 temp).

  econstructor; try eassumption.
  eapply not_in_adts_not_mapsto_adt; eauto.

  (* RunsTo *)
  
  intros;
    repeat inversion_facade;
    specialize_states;
    scas_adts_mapsto;
    unfold eval, eval_binop_m in *;
    repeat (subst_find; simpl in *);
    autoinj.

  split;
    rewrite_Eq_in_goal;
    [ repeat remove_not_in;
      apply SomeSCAs_chomp
    | apply add_adts_pop_sca ];
    assumption.
Qed.  

Lemma compile_binop :
  forall {av env},
  forall op vret tw1 tw2,
  forall w1 w2,
  forall init_knowledge init_scas inter_scas final_scas init_adts post_w1_adts final_adts,
    tw1 <> tw2 ->
    ~ StringMap.In vret final_adts ->
    refine (@Prog av env init_knowledge
                  init_scas ([vret >sca> (IL.evalBinop op) w1 w2] :: [tw2 >sca> w2] :: [tw1 >sca> w1] :: final_scas)
                  init_adts final_adts)
           (pw1  <- (@Prog av env init_knowledge
                           init_scas ([tw1 >sca> w1] :: inter_scas)
                           init_adts post_w1_adts);
            pw2  <- (@Prog av env init_knowledge
                           ([tw1 >sca> w1] :: inter_scas)
                           ([tw2 >sca> w2] :: [tw1 >sca> w1] :: final_scas)
                           post_w1_adts final_adts);
            ret (pw1; pw2; Assign vret (Binop op tw1 tw2))%facade)%comp.
Proof. (* Same proof as compile_binop *)
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  (* Safe *)

  repeat (safe_seq; intros).
  specialize_states.
  scas_adts_mapsto.

  (*TODO: Prettier way of doing this? *)
  assert (forall k : StringMap.key,
            List.In k (AllVariables (Binop op (Var tw1) (Var tw2))) ->
            exists v : W, (st'0) [k >> SCA av v])
    as temp
    by (unfold AllVariables; simpl; intros; intuition; eexists; subst; eassumption).
  destruct (eval_expr_some_sca (Binop op (Var tw1) (Var tw2)) st'0 temp).

  econstructor; try eassumption.
  eapply not_in_adts_not_mapsto_adt; eauto.

  (* RunsTo *)
  
  intros;
    repeat inversion_facade;
    specialize_states;
    scas_adts_mapsto;
    unfold eval, eval_binop_m in *;
    repeat (subst_find; simpl in *);
    autoinj.

  split;
    rewrite_Eq_in_goal;
  eauto using SomeSCAs_chomp, add_adts_pop_sca.
Qed.

Lemma compile_test :
  forall {av env},
  forall op vret tw1 tw2,
  forall w1 w2,
  forall init_knowledge init_scas inter_scas final_scas init_adts post_w1_adts final_adts,
    tw1 <> tw2 ->
    ~ StringMap.In vret final_adts ->
    refine (@Prog av env init_knowledge
                  init_scas ([vret >sca> BoolToW ((IL.evalTest op) w1 w2)] :: [tw2 >sca> w2] :: [tw1 >sca> w1] :: final_scas)
                  init_adts final_adts)
           (pw1  <- (@Prog av env init_knowledge
                           init_scas ([tw1 >sca> w1] :: inter_scas)
                           init_adts post_w1_adts);
            pw2  <- (@Prog av env init_knowledge
                           ([tw1 >sca> w1] :: inter_scas)
                           ([tw2 >sca> w2] :: [tw1 >sca> w1] :: final_scas)
                           post_w1_adts final_adts);
            ret (pw1; pw2; Assign vret (TestE op tw1 tw2))%facade)%comp.
Proof. (* Same proof as compile_binop *)
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  (* Safe *)

  repeat (safe_seq; intros).
  specialize_states.
  scas_adts_mapsto.

  (*TODO: Prettier way of doing this? *)
  assert (forall k : StringMap.key,
            List.In k (AllVariables (TestE op (Var tw1) (Var tw2))) ->
            exists v : W, (st'0) [k >> SCA av v])
    as temp
    by (unfold AllVariables; simpl; intros; intuition; eexists; subst; eassumption).
  destruct (eval_expr_some_sca (TestE op (Var tw1) (Var tw2)) st'0 temp).

  econstructor; try eassumption.
  eapply not_in_adts_not_mapsto_adt; eauto.

  (* RunsTo *)
  
  intros;
    repeat inversion_facade;
    specialize_states;
    scas_adts_mapsto;
    unfold eval, eval_binop_m in *;
    repeat (subst_find; simpl in *);
    autoinj.

  split;
    rewrite_Eq_in_goal;
  eauto using SomeSCAs_chomp, add_adts_pop_sca.
Qed.

Lemma prepare_test :
  forall av env vret tw1 tw2 w1 w2 knowledge scas init_adts final_adts f,
    refine (@Prog av env knowledge
                  scas ([vret >sca> BoolToW (f w1 w2)]::scas)
                  init_adts final_adts)
           (p <- (@Prog av env knowledge
                        scas ([vret >sca> BoolToW (f w1 w2)]
                                :: [tw2 >sca> w2] :: [tw1 >sca> w1] :: scas)
                        init_adts final_adts);
            cleanup <- (@Prog av env knowledge
                              ([vret >sca> BoolToW (f w1 w2)]
                                 :: [tw2 >sca> w2] :: [tw1 >sca> w1] :: scas)
                              ([vret >sca> BoolToW (f w1 w2)]::scas)
                              final_adts final_adts);
            ret (p; cleanup)%facade)%comp.
Proof.
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  + constructor; split; intros; specialize_states; eassumption.
  + intros; inversion_facade; specialize_states; intuition.
Qed.

Lemma prepare_binop :
  forall av env vret tw1 tw2 w1 w2 knowledge scas init_adts final_adts f,
    refine (@Prog av env knowledge
                  scas ([vret >sca> (f w1 w2)]::scas)
                  init_adts final_adts)
           (p <- (@Prog av env knowledge
                        scas ([vret >sca> (f w1 w2)]
                                :: [tw2 >sca> w2] :: [tw1 >sca> w1] :: scas)
                        init_adts final_adts);
            cleanup <- (@Prog av env knowledge
                              ([vret >sca> (f w1 w2)]
                                 :: [tw2 >sca> w2] :: [tw1 >sca> w1] :: scas)
                              ([vret >sca> (f w1 w2)]::scas)
                              final_adts final_adts);
            ret (p; cleanup)%facade)%comp.
Proof.
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  + constructor; split; intros; specialize_states; eassumption.
  + intros; inversion_facade; specialize_states; intuition.
Qed.
