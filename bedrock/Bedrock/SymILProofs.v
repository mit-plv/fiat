Require Import Coq.omega.Omega.
(** This file implements symbolic evaluation for the
 ** language defined in IL.v
 **)
Require Import Bedrock.IL Bedrock.SepIL.
Require Import Bedrock.Word Bedrock.Memory.
Require Import Bedrock.DepList Bedrock.EqdepClass.
Require Import Bedrock.PropX.
Require Import Bedrock.SepExpr Bedrock.SymEval.
Require Import Bedrock.Expr.
Require Import Bedrock.Prover.
Require Import Bedrock.Env Bedrock.TypedPackage.
Import List.

Require Bedrock.Structured Bedrock.SymEval.
Require Import Bedrock.ILEnv Bedrock.SymIL.

Set Implicit Arguments.
Set Strict Implicit.

(** The Symolic Evaluation Interfaces *)
Module MEVAL := SymIL.MEVAL.

Module SymIL_Correct.
  Section typed.
    Variable ts : list type.
    Let types := repr bedrock_types_r ts.

    Notation pcT := (tvType 0).
    Notation tvWord := (tvType 0).
    Notation stT := (tvType 1).
    Notation tvState := (tvType 2).
    Notation tvTest := (tvType 3).
    Notation tvReg := (tvType 4).

    Variable fs : functions types.
    Let funcs := repr (bedrock_funcs_r ts) fs.
    Variable preds : SEP.predicates types pcT stT.

    Variable Prover : ProverT types.
    Variable PC : ProverT_correct Prover funcs.

    Variable meval : MEVAL.MemEvaluator types pcT stT.
    Variable meval_correct : MEVAL.MemEvaluator_correct meval funcs preds tvWord tvWord
      (@IL_mem_satisfies ts) (@IL_ReadWord ts) (@IL_WriteWord ts) (@IL_ReadByte ts) (@IL_WriteByte ts).

    Variable facts : Facts Prover.
    Variable meta_env : env types.
    Variable vars_env : env types.

    Lemma stateD_interp : forall cs stn_st ss sh,
      stateD funcs preds meta_env vars_env cs stn_st ss ->
      SymMem ss = Some sh ->
      interp cs (![ MEVAL.SEP.sexprD funcs preds meta_env vars_env (SH.sheapD sh)] stn_st).
    Proof.
      clear. destruct stn_st; destruct ss; destruct SymRegs; destruct p; simpl; intros.
      rewrite H0 in *. intuition.
    Qed.

    Hint Resolve stateD_interp : sym_eval_hints.

    Ltac t_correct :=
      simpl; intros;
        unfold IL_stn_st, IL_mem_satisfies, IL_ReadWord, IL_WriteWord in *;
          repeat (simpl in *;
            match goal with
              | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
              | [ H : prod _ _ |- _ ] => destruct H
              | [ H : match ?X with
                        | Some _ => _
                        | None => _
                      end |- _ ] =>
                revert H; case_eq X; intros; try contradiction
              | [ H : match ?X with
                        | Some _ => _
                        | None => _
                      end = _ |- _ ] =>
                revert H; case_eq X; intros; try congruence
              | [ H : _ = _ |- _ ] => rewrite H
              | [ H : @existsEach _ _ _ |- _ ] => apply existsEach_sem in H
              | [ H : exists x, _ |- _ ] => destruct H
              | [ H : _ /\ _ |- _ ] => destruct H
              | [ |- exists x, Some _ = Some _ /\ _ ] =>
                eexists; split; [ reflexivity | ]
            end); subst; eauto with sym_eval_hints.

    Lemma sym_evalLoc_correct : forall loc ss res res' stn_st locD cs,
      stateD funcs preds meta_env vars_env cs stn_st ss ->
      sym_locD fs meta_env vars_env loc = Some locD ->
      evalLoc (snd stn_st) locD = res' ->
      sym_evalLoc loc ss = res ->
      exprD funcs meta_env vars_env res tvWord = Some res'.
    Proof.
      destruct loc; unfold stateD; destruct ss; destruct SymRegs; destruct p; intros; destruct stn_st; simpl in *;
        t_correct; try solve [ eauto
                             | destruct r; simpl in *;
                               repeat match goal with
                                        | [ H : _ = _ |- _ ] => rewrite H
                                        | [ |- _ ] => subst funcs
                                      end; eauto ].
    Qed.

    Hypothesis Valid_facts : Valid PC meta_env vars_env facts.

    Lemma sym_evalRval_correct : forall rv ss res stn_st rvD cs,
      stateD funcs preds meta_env vars_env cs stn_st ss ->
      sym_rvalueD funcs meta_env vars_env rv = Some rvD ->
      sym_evalRval Prover meval facts rv ss = Some res ->
      exists val,
        evalRvalue (fst stn_st) (snd stn_st) rvD = Some val /\
        exprD funcs meta_env vars_env res tvWord = Some val.
    Proof.
      Opaque stateD sym_locD.
      destruct rv; t_correct.
      { destruct s; t_correct.
        { erewrite <- (@sym_evalLoc_correct (SymReg _ r)). f_equal. eauto. simpl.
          Transparent sym_locD. simpl. reflexivity. Opaque sym_locD. reflexivity. reflexivity. }
        { eapply (MEVAL.ReadCorrect meval_correct) with (cs := cs) in H2; eauto with sym_eval_hints.
          2: eapply sym_evalLoc_correct; (instantiate; eauto with sym_eval_hints). 2: eauto.
          t_correct. }
        { eapply (MEVAL.ReadByteCorrect meval_correct) with (cs := cs) in H2; eauto with sym_eval_hints.
          2: eapply sym_evalLoc_correct; (instantiate; eauto with sym_eval_hints). 2: eauto.
          t_correct. } }
      { congruence. }
    Qed.

    Lemma sym_evalLval_correct : forall lv stn_st lvD cs val ss ss' valD,
      stateD funcs preds meta_env vars_env cs stn_st ss ->
      sym_lvalueD funcs meta_env vars_env lv = Some lvD ->
      sym_evalLval Prover meval facts lv val ss = Some ss' ->
      exprD funcs meta_env vars_env val tvWord = Some valD ->
      exists st',
        evalLvalue (fst stn_st) (snd stn_st) lvD valD = Some st' /\
        stateD funcs preds meta_env vars_env cs (fst stn_st, st') ss'.
    Proof.
      destruct lv; t_correct.
      { Transparent stateD. unfold stateD in *. t_correct. Opaque stateD.
        case_eq (sym_setReg r val (SymRegs ss)); intros.
        destruct ss; destruct SymRegs; destruct p. t_correct.
        unfold sym_setReg in H0. destruct r; inversion H0; subst; t_correct; unfold rupd; simpl; intuition;
        try solve [ repeat rewrite sepFormula_eq in *; unfold sepFormula_def in *; simpl in *; auto ].
        destruct r; inversion H0; subst; t_correct; unfold rupd; simpl; intuition. }
      { eapply (@sym_evalLoc_correct s) in H0; eauto.
        simpl.
        match goal with
          | [ H : MEVAL.swrite_word _ _ _ _ _ _ = _ |- _ ] =>
            eapply (MEVAL.WriteCorrect meval_correct) with (cs := cs) (stn_m := (s0,s1)) in H; eauto with sym_eval_hints
        end.
        simpl in *.
        destruct (WriteWord s0 (Mem s1) (evalLoc s1 l) valD); try contradiction. t_correct.
        Transparent stateD. destruct ss; destruct SymRegs; destruct p. simpl in *. Opaque stateD. intuition. subst.
        generalize SH.sheapD_pures. unfold SEP.ST.satisfies. intro XXX.
        rewrite sepFormula_eq in H3. unfold sepFormula_def in H3. simpl in *.
        specialize (@XXX _ _ _ funcs preds meta_env vars_env cs _ _ _ H3).
        apply AllProvable_app' in H6. apply AllProvable_app; intuition auto. }
      { eapply (@sym_evalLoc_correct s) in H0; eauto.
        simpl.
        match goal with
          | [ H : MEVAL.swrite_byte _ _ _ _ _ _ = _ |- _ ] =>
            eapply (MEVAL.WriteByteCorrect meval_correct) with (cs := cs) (stn_m := (s0,s1)) in H; eauto with sym_eval_hints
        end.
        simpl in *.
        destruct (WriteByte (Mem s1) (evalLoc s1 l) (WtoB valD)); try contradiction. t_correct.
        Transparent stateD. destruct ss; destruct SymRegs; destruct p. simpl in *. Opaque stateD. intuition. subst.
        generalize SH.sheapD_pures. unfold SEP.ST.satisfies. intro XXX.
        rewrite sepFormula_eq in H3. unfold sepFormula_def in H3. simpl in *.
        specialize (@XXX _ _ _ funcs preds meta_env vars_env cs _ _ _ H3).
        apply AllProvable_app' in H6. apply AllProvable_app; intuition auto. }
    Qed.


    Ltac think := instantiate; simpl;
      repeat match goal with
               | [ H : _ = _ |- _ ] => rewrite H
             end; eauto.

    Lemma sym_evalInstr_correct' : forall instr stn_st instrD cs ss ss',
      stateD funcs preds meta_env vars_env cs stn_st ss ->
      sym_instrD funcs meta_env vars_env instr = Some instrD ->
      sym_evalInstr Prover meval facts instr ss = Some ss' ->
      exists st',
        evalInstr (fst stn_st) (snd stn_st) instrD = Some st' /\
        stateD funcs preds meta_env vars_env cs (fst stn_st, st') ss'.
    Proof.
      destruct instr; t_correct; simpl;
        repeat match goal with
                 | [ H : exists x, _ |- _ ] => destruct H
                 | [ H : _ /\ _ |- _ ] => destruct H
                 | [ H : sym_rvalueD _ _ _ _ = _ |- _ ] =>
                   (eapply sym_evalRval_correct in H; think); [ simpl in * ]
                 | [ H : sym_lvalueD _ _ _ _ = _ |- _ ] =>
                   (eapply sym_evalLval_correct in H; think); [ simpl in * ]
                 | [ H : _ = _ |- _ ] => rewrite H
                 | [ |- _ ] => progress (simpl in * )
                 | [ b : binop |- _ ] =>
                   destruct b; unfold fPlus, fMinus, fMult in *; simpl in *
               end; t_correct.
    Qed.

    Lemma sym_assertTest_correct' : forall cs r rD t l lD ss stn_st,
      stateD funcs preds meta_env vars_env cs stn_st ss ->
      sym_rvalueD funcs meta_env vars_env r = Some rD ->
      sym_rvalueD funcs meta_env vars_env l = Some lD ->
      match Structured.evalCond rD t lD (fst stn_st) (snd stn_st) with
        | None =>
          forall res,
            match sym_assertTest Prover meval facts r t l ss res with
              | Some _ => False
              | None => True
            end
        | Some res' =>
          match sym_assertTest Prover meval facts r t l ss res' with
            | Some b =>
              Provable funcs meta_env vars_env b
            | None => True
          end
      end.
    Proof.
      unfold sym_assertTest, Structured.evalCond; destruct stn_st; simpl in *;
        repeat match goal with
                 | [ H : exists x, _ |- _ ] => destruct H
                 | [ H : _ /\ _ |- _ ] => destruct H
                 | [ H : sym_rvalueD _ _ _ _ = _ |- _ ] =>
                   (eapply sym_evalRval_correct in H; think); [ simpl in * ]
                 | [ H : sym_lvalueD _ _ _ _ = _ |- _ ] =>
                   (eapply sym_evalLval_correct in H; think); [ simpl in * ]
                 | [ H : _ = _ |- _ ] => rewrite H
                 | [ |- _ ] => progress (simpl in * )
                 | [ |- context [ evalRvalue ?A ?B ?C ] ] =>
                   case_eq (evalRvalue A B C); intros
                 | [ |- context [ evalTest ?A ?B ?C ] ] =>
                   case_eq (evalTest A B C); intros
                 | [ b : binop |- _ ] =>
                   destruct b; unfold fPlus, fMinus, fMult in *; simpl in *
               end; t_correct; simpl in *;
      try destruct res;
       repeat match goal with
        | [ |- context [ sym_evalRval ?A ?B ?C ?D ?E ] ] =>
          case_eq (sym_evalRval A B C D E); intros
               end; auto;
        unfold Provable; destruct t;
        repeat match goal with
                 | [ |- match match ?X with
                                | Some _ => match ?Y with _ => _ end
                                | _ => _
                              end with _ => _ end ] =>
                   (case_eq X; trivial; case_eq Y; trivial); []

                 | [ H : exists x, _ |- _ ] => destruct H
                 | [ H : _ /\ _ |- _ ] => destruct H
                 | [ H : sym_rvalueD _ _ _ _ = _ |- _ ] =>
                   (eapply sym_evalRval_correct in H; think); [ simpl in * ]
                 | [ H : sym_lvalueD _ _ _ _ = _ |- _ ] =>
                   (eapply sym_evalLval_correct in H; think); [ simpl in * ]
                 | [ H : _ = _ |- _ ] => rewrite H
                 | [ |- _ ] => progress (simpl in * )
                 | [ |- context [ evalRvalue ?A ?B ?C ] ] =>
                   case_eq (evalRvalue A B C); intros
                 | [ |- context [ evalTest ?A ?B ?C ] ] =>
                   Reflection.consider (evalTest A B C); intros
                 | [ b : binop |- _ ] =>
                   destruct b; unfold fPlus, fMinus, fMult in *; simpl in *
                 | [ |- _ ] => progress t_correct
               end; unfold IL.weqb, IL.wneb, wltb, wleb in *; simpl in *;
        repeat match goal with
                 | [ H : (if ?X then _ else _) = _ |- _ ] =>
                   revert H; Reflection.consider X; try congruence
                 | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                 | [ H : ?X = _ , H' : ?X = _ |- _ ] => rewrite H in H'
                 | [ |- context [ wlt_dec ?X ?Y ] ] =>
                   destruct (wlt_dec X Y); try congruence
               end; try congruence; eauto 10 using eq_le, lt_le, le_neq_lt.
      eapply weqb_true_iff; auto.
      intro. apply weqb_true_iff in H1. congruence.
    Qed.

  End typed.


  Section typed2.
    Variable ts : list type.
    Let types := repr bedrock_types_r ts.

    Notation pcT := (tvType 0).
    Notation tvWord := (tvType 0).
    Notation stT := (tvType 1).
    Notation tvState := (tvType 2).
    Notation tvTest := (tvType 3).
    Notation tvReg := (tvType 4).

    Variable fs : functions types.
    Let funcs := repr (bedrock_funcs_r ts) fs.
    Variable preds : SEP.predicates types pcT stT.

    Variable Prover : ProverT types.
    Variable PC : ProverT_correct Prover funcs.

    Variable meval : MEVAL.MemEvaluator types pcT stT.
    Variable meval_correct : MEVAL.MemEvaluator_correct meval funcs preds tvWord tvWord
      (@IL_mem_satisfies ts) (@IL_ReadWord ts) (@IL_WriteWord ts) (@IL_ReadByte ts) (@IL_WriteByte ts).

    Ltac t_correct :=
      simpl; intros;
        unfold IL_stn_st, IL_mem_satisfies, IL_ReadWord, IL_WriteWord in *;
          repeat (simpl in *;
            match goal with
              | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
              | [ H : prod _ _ |- _ ] => destruct H
              | [ H : match ?X with
                        | Some _ => _
                        | None => _
                      end |- _ ] =>
              revert H; case_eq X; intros; try contradiction
              | [ H : match ?X with
                        | Some _ => _
                        | None => _
                      end = _ |- _ ] =>
              revert H; case_eq X; intros; try congruence
              | [ H : _ = _ |- _ ] => rewrite H
              | [ H : reg |- _ ] => destruct H
            end; intuition); subst.

    Lemma sym_evalInstrs_correct : forall (facts : Facts Prover) (meta_env var_env : env types),
      Valid PC meta_env var_env facts  ->
      forall is stn_st isD cs ss,
        stateD funcs preds meta_env var_env cs stn_st ss ->
        sym_instrsD funcs meta_env var_env is = Some isD ->
        match evalInstrs (fst stn_st) (snd stn_st) isD with
          | Some st' =>
            match sym_evalInstrs Prover meval facts is ss with
              | inl ss' => stateD funcs preds meta_env var_env cs (fst stn_st, st') ss'
              | inr (ss', is') =>
                match sym_instrsD funcs meta_env var_env is' with
                  | None => False
                  | Some is'D =>
                    exists st'', stateD funcs preds meta_env var_env cs (fst stn_st, st'') ss' /\
                      evalInstrs (fst stn_st) st'' is'D = Some st'
                end
            end
          | None =>
            match sym_evalInstrs Prover meval facts is ss with
              | inl ss' => False
              | inr (ss', is') =>
                match sym_instrsD funcs meta_env var_env is' with
                  | None => False
                  | Some is'D =>
                    exists st'', stateD funcs preds meta_env var_env cs (fst stn_st, st'') ss' /\
                      evalInstrs (fst stn_st) st'' is'D = None
                end
            end
        end.
    Proof.
      Opaque stateD.
      induction is; simpl; intros;
        repeat match goal with
                 | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
               end; simpl; destruct stn_st; simpl in *; eauto.
      t_correct. simpl in *.
      case_eq (evalInstr s s0 i); intros.
      case_eq (sym_evalInstr Prover meval facts a ss); intros.

      destruct (@sym_evalInstr_correct' ts fs preds Prover PC meval meval_correct facts meta_env var_env
        H a (s,s0) i cs ss s2 H0 H1 H4). simpl in *. intuition.
      rewrite H6 in H3. inversion H3; clear H3; subst.
      specialize (IHis (s, s1)). simpl in *. eapply IHis; eauto.

      simpl. rewrite H1. rewrite H2. simpl.
      case_eq (evalInstrs s s1 l); intros; exists s0; simpl; rewrite H3; eauto.

      case_eq (sym_evalInstr Prover meval facts a ss); intros.
      Focus 2. simpl. rewrite H1. rewrite H2. exists s0; simpl; rewrite H3; intuition.



      edestruct (@sym_evalInstr_correct' ts fs preds Prover PC meval meval_correct facts meta_env var_env
        H a (s,s0) i cs ss); eauto.
      simpl in *. destruct H5. rewrite H3 in H5. congruence.
      Transparent stateD.
    Qed.

    Variable learnHook : MEVAL.LearnHook types (SymState types pcT stT).
    Variable learn_correct : @MEVAL.LearnHook_correct _ _ pcT stT learnHook (@stateD _ funcs preds) funcs preds.

    Ltac shatter_state ss :=
      destruct ss as [ ? [ [ ? ? ] ? ] ].

    Lemma skip_to_nil : forall T U (F : T -> U) vars env X,
      map F env = skipn (length vars) X ->
      map F nil = skipn (length (vars ++ env)) X.
    Proof.
      clear. induction vars; simpl; intros; subst.
      induction env; eauto.
      destruct X; auto.
    Qed.
    Lemma AllProvable_cons : forall U G P Ps,
      Provable funcs U G P ->
      AllProvable funcs U G Ps ->
      AllProvable funcs U G (P :: Ps).
    Proof. simpl; intuition. Qed.
    Lemma AllProvable_nil : forall U G,
      AllProvable funcs U G nil.
    Proof. simpl; intuition. Qed.
    Hint Resolve AllProvable_cons AllProvable_nil : env_resolution.
    Hint Resolve Learn_correct : env_resolution.
    Hint Resolve skip_to_nil : env_resolution.

    Lemma skip_prove_nil : forall T U (F : T -> U) vars env X Y,
      map F env = skipn (length vars) X ->
      map F Y = skipn (length (vars ++ env)) X ->
      Y = nil.
    Proof.
      clear. intros. destruct Y; auto.
      eapply skip_to_nil in H. rewrite <- H in H0. simpl in *; congruence.
    Qed.
    Hint Resolve skip_prove_nil : env_resolution.
    Lemma stateD_addToPures : forall U G cs ss stn_st P,
      stateD funcs preds U G cs stn_st ss ->
      Provable funcs U G P ->
      stateD funcs preds U G cs stn_st
      {| SymMem := SymMem ss
        ; SymRegs := SymRegs ss
        ; SymPures := P :: SymPures ss |}.
    Proof.
      Transparent stateD.
      clear. intros; shatter_state ss; destruct stn_st; simpl in *. intuition.
      destruct SymMem; intuition.
      Opaque stateD.
    Qed.
    Hint Resolve stateD_addToPures : stateD_solver.

    Ltac qstateD_solver :=
      eapply existsEach_sem; intros; eexists; split; [ solve [ eauto with env_resolution ] | ];
      let e := fresh in
      eapply forallEach_sem; intro e; intro;
      eauto with stateD_solver.

    Opaque repr stateD.
    Ltac split_congruence :=
      repeat match goal with
               | [ H : prod _ _ |- _ ] => destruct H
             end; congruence.

    Lemma stateD_weaken_vars : forall uvars vars cs stn_st ss' env,
      stateD funcs preds uvars vars cs stn_st ss' ->
      stateD funcs preds uvars (vars ++ env) cs stn_st ss'.
    Proof.
      Transparent stateD.
      clear. intros. destruct stn_st; shatter_state ss'; simpl in *.
      repeat match goal with
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ H : context [ match exprD ?A ?B ?C ?D ?E with _ => _ end ] |- _ ] =>
                 revert H; case_eq (exprD A B C D E); intros; try contradiction
             end; subst.
      rewrite <- app_nil_r with (l := uvars). repeat erewrite exprD_weaken by eassumption.
      intuition. destruct SymMem; auto. erewrite SH.SE_FACTS.sexprD_weaken in H0. eassumption.
      eapply AllProvable_weaken; eauto.
    Qed.
    Lemma stateD_weaken_uvars : forall uvars vars cs stn_st ss' env,
      stateD funcs preds uvars vars cs stn_st ss' ->
      stateD funcs preds (uvars ++ env) vars cs stn_st ss'.
    Proof.
      Transparent stateD.
      clear. intros. destruct stn_st; shatter_state ss'; simpl in *.
      repeat match goal with
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ H : context [ match exprD ?A ?B ?C ?D ?E with _ => _ end ] |- _ ] =>
                 revert H; case_eq (exprD A B C D E); intros; try contradiction
             end; subst.
      rewrite <- app_nil_r with (l := vars). repeat erewrite exprD_weaken by eassumption.
      intuition. destruct SymMem; auto. erewrite SH.SE_FACTS.sexprD_weaken in H0. eassumption.
      eapply AllProvable_weaken; eauto.
    Qed.
    Hint Resolve stateD_weaken_vars stateD_weaken_uvars : stateD_solver.
    Require Bedrock.ListFacts.
    Require Import Bedrock.Tactics Bedrock.Reflection.
    Hint Resolve ListFacts.not_sure ListFacts.map_skipn_all_map_is_nil ListFacts.map_skipn_all_map : env_resolution.

    Lemma sym_locD_weaken : forall ts X A C Y Z,
      sym_locD (types' := ts) X A C Y = Some Z ->
      forall B D,
        sym_locD X (A ++ B) (C ++ D) Y = Some Z.
    Proof.
      clear. destruct Y; simpl; intros; think; auto;
      erewrite exprD_weaken; eauto.
    Qed.

    Lemma sym_lvalueD_weaken : forall ts X A C Y Z,
      sym_lvalueD (types' := ts) X A C Y = Some Z ->
      forall B D,
        sym_lvalueD X (A ++ B) (C ++ D) Y = Some Z.
    Proof.
      clear. destruct Y; simpl; intros; think; auto.
      erewrite sym_locD_weaken; eauto.
      erewrite sym_locD_weaken; eauto.
    Qed.
    Lemma sym_rvalueD_weaken : forall ts X A C Y Z,
      sym_rvalueD (types' := ts) X A C Y = Some Z ->
      forall B D,
        sym_rvalueD X (A ++ B) (C ++ D) Y = Some Z.
    Proof.
      clear. destruct Y; simpl; intros; think; auto.
      erewrite sym_lvalueD_weaken; eauto.
      erewrite exprD_weaken; eauto.
    Qed.

    Lemma sym_instrD_weaken : forall ts X A C Y Z,
      sym_instrD (types' := ts) X A C Y = Some Z ->
      forall B D,
      sym_instrD X (A ++ B) (C ++ D) Y = Some Z.
    Proof.
      clear; destruct Y; simpl; intros; think; auto;
        repeat ((erewrite sym_lvalueD_weaken by eauto) ||
                (erewrite sym_rvalueD_weaken by eauto)); auto.
    Qed.

    Lemma sym_instrsD_weaken : forall ts X A C Y Z,
      sym_instrsD (types' := ts) X A C Y = Some Z ->
      forall B D,
      sym_instrsD X (A ++ B) (C ++ D) Y = Some Z.
    Proof.
      clear. induction Y; simpl; intros; think; auto.
      erewrite sym_instrD_weaken; eauto.
    Qed.

    Lemma istreamD_weaken : forall ts X A C Y Z P L,
      istreamD (types' := ts) X A C Y Z P L ->
      forall B D,
      istreamD X (A ++ B) (C ++ D) Y Z P L.
    Proof.
      clear. induction Y; simpl; intros; think; auto.
      repeat match goal with
               | [ H : match ?X with _ => _ end |- _ ] =>
                 consider X; intros
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ |- _ ] =>
                 (erewrite sym_instrsD_weaken by eauto) ||
                 (erewrite sym_rvalueD_weaken by eauto) ||
                 (erewrite sym_lvalueD_weaken by eauto)
             end; intuition.
    Qed.

    Lemma env_nil_by_length_eq : forall ts L X Y,
      typeof_env (types := ts) L = X ->
      length Y = length X ->
      typeof_env (types := ts) nil = skipn (length L) Y.
    Proof.
      clear. intros. subst.
      erewrite ListFacts.skipn_length_gt; auto. unfold typeof_env in *. rewrite map_length in H0. omega.
    Qed.
    Hint Resolve env_nil_by_length_eq : env_resolution.

    Lemma all2_tvar_seq_dec_true : forall a b,
      Folds.all2 Expr.tvar_seqb a b = true -> a = b.
    Proof.
      clear; induction a; destruct b; simpl; intros; try congruence.
      consider (tvar_seqb a t). intros. erewrite IHa; auto.
    Qed.

    Lemma sym_evalStream_quant_append : forall path facts qs uvars vars ss res,
      sym_evalStream Prover meval learnHook facts path qs uvars vars ss = res ->
      match res with
        | Safe qs' _
        | SafeUntil qs' _ _ => exists qs'', qs' = appendQ qs'' qs
(*        | Unsafe qs'  *)
      end.
    Proof.
      clear.
      induction path; simpl; intros.
      { inversion H. subst. exists QBase.
        clear. simpl; auto. }
      { destruct a. destruct p. consider (sym_evalInstrs Prover meval facts l ss); intros; try congruence.
        eapply IHpath; eauto. destruct p. subst. exists QBase. auto.
        destruct s. destruct o. consider (sym_assertTest Prover meval facts s t s0 ss b); intros.
        repeat match goal with
                 | [ H : match ?X with (_,_) => _ end = _ |- _ ] => destruct X; try congruence
               end.
        eapply IHpath in H0. destruct res; auto; destruct H0; rewrite <- appendQ_assoc in H0; eauto.
        subst; auto. exists QBase; auto.
        repeat match goal with
                 | [ H : match ?X with _ => _ end = _ |- _ ] => destruct X; try congruence
               end; subst;
        try eapply IHpath; eauto.
        exists QBase; auto.
        exists QBase; auto. }
    Qed.

    Hint Extern 1 (@eq (list tvar) _ _) =>
      simpl; repeat (rewrite app_nil_r in * || rewrite typeof_env_app in * || rewrite app_ass ||
        (f_equal; []) || (f_equal; [ solve [ reflexivity | assumption ] | ] || reflexivity || assumption)) : env_resolution.

    Definition NO_MORE_COND : Prop := True.

    Ltac sym_eval_prover IHpath :=
      repeat match goal with
               | [ H : Valid _ (?A ++ ?b) (?C ++ ?d) _
                 , H' : sym_instrsD ?X ?A ?C ?Y = ?Z |- _ ] =>
                 apply sym_instrsD_weaken with (B := b) (D := d) in H'
               | [ H : Valid _ (?A ++ ?b) (?C ++ ?d) _
                 , H' : istreamD ?X ?A ?C ?Y ?Z ?P ?L |- _ ] =>
                 apply istreamD_weaken with (B := b) (D := d) in H'
               | [ H : (_,_) = (_,_) |- _ ] => inversion H; clear H; subst
               | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
               | [ H : Safe _ _ = Safe _ _ |- _ ] => inversion H; clear H; subst
               | [ H : SafeUntil _ _ _ = SafeUntil _ _ _ |- _ ] => inversion H; clear H; subst
               | [ H : inl _ = inl _ |- _ ] => inversion H; clear H; subst
               | [ H : inr _ = inr _ |- _ ] => inversion H; clear H; subst
               | [ H : SymAssertCond _ _ _ _ = SymAssertCond _ _ _ _ |- _ ] => inversion H; clear H; subst
               | [ H : sum (prod _ _) _ |- _ ] => destruct H as [ [ ? ? ] | ? ]
               | [ H : ?X = _ , H' : ?X = _ |- _ ] => rewrite H in H'
               | [ H : option state |- _ ] => destruct H
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ H : ?X = _ , H' : context [ match ?X with _ => _ end ] |- _ ] =>
                 rewrite H in H'
               | [ H : match ?X with _ => _ end |- _ ] =>
                 (revert H; case_eq X; intros; try contradiction); []
               | [ |- _ ] => progress (repeat rewrite app_nil_r in * )
               | [ |- _ ] => solve [ congruence | eauto with stateD_solver ]
               | [ H : ?X -> _ , H' : ?X |- _ ] =>
                 match type of X with
                   | Prop =>
                     specialize (H H')
                 end
               | [ H   : sym_evalInstrs _ _ ?F ?is ?S = _
                 , H'  : evalInstrs ?stn ?st _ = _
                 , H'' : sym_instrsD _ ?U ?G _ = Some ?isD
                 , Hst : stateD _ _ _ _ _ _ _
                 |- _ ] =>
               ( eapply sym_evalInstrs_correct with (stn_st := (stn,st)) (facts := F) (ss := S) in H'' ; eauto ;
                 simpl in H'' ) ; [ clear Hst ]
               | [ H : Structured.evalCond ?l ?A ?r ?B ?C = _
                 , Hst : stateD _ _ ?U ?G ?cs _ _
                 , H' : sym_rvalueD _ _ _ _ = Some ?l
                 , H'' : sym_rvalueD _ _ _ _ = Some ?r |- _ ] =>
               match goal with
                 | [ H : NO_MORE_COND |- _ ] => fail 1
                 | _ =>
                   (generalize Hst; eapply sym_assertTest_correct' with (meta_env := U) (vars_env := G) (t := A) (rD := l) (lD := r) (stn_st := (B,C)) in Hst; eauto using sym_rvalueD_weaken) ; [ intro; simpl in Hst ; assert NO_MORE_COND by (exact I) ]
               end
               | [ H : learnHook _ ?U' ?G' ?SS ?f ?F = (?A, ?B)
                 , H' : stateD _ _ ?U ?G _ _ _
                 , LC : MEVAL.LearnHook_correct _ _ _ _
                 , PC : ProverT_correct _ _ |- _ ] =>
                 (cutrewrite (U' = typeof_env U) in H; [ | rewrite typeof_env_app; f_equal; auto ] ;
                  cutrewrite (G' = typeof_env G) in H; [ | rewrite typeof_env_app; f_equal; auto ] ;
                  eapply (@MEVAL.hook_sound _ _ _ _ _ _ _ _ LC _ PC U G) with
                    (new_facts := F) (ss := SS) (ss' := A) (quant := B) in H ;
                  eauto using Learn_correct, AllProvable_cons, AllProvable_nil with stateD_solver) ; [ clear H' ]
               | [ H : quantD _ _ _ _ |- quantD _ _ _ _ ] =>
                 eapply quantD_impl; [ eapply H | clear H ; simpl; intros ]
               | [ |- quantD _ _ (appendQ _ ?X) _ ] =>
                 apply quantD_app
               | [ H : appendQ _ _ = appendQ _ _ |- _ ] => apply appendQ_proper in H; subst

               | [ H : appendQ ?A ?B = appendQ _ (appendQ _ ?B) |- _ ] =>
                 rewrite <- appendQ_assoc in H; apply appendQ_proper in H; subst
               | [ H : context [ Safe (appendQ (appendQ ?A ?B) ?C) _ ] |- _ ] =>
                 rewrite appendQ_assoc with (a := A) (b := B) (c := C) in H
               | [ H : context [ SafeUntil (appendQ (appendQ ?A ?B) ?C) _ _ ] |- _ ] =>
                 rewrite appendQ_assoc with (a := A) (b := B) (c := C) in H

               | [ H : sym_evalStream _ _ _ _ _ (appendQ _ ?X) _ _ _ = Safe (appendQ ?Y ?X) _ |- _ ] =>
                 match Y with
                   | appendQ _ _ => fail 1
                   | _ => destruct (sym_evalStream_quant_append _ _ _ _ _ _ H); subst
                 end
               | [ H : sym_evalStream _ _ _ _ _ (appendQ _ (appendQ _ ?X)) _ _ _ = Safe (appendQ ?Y ?X) _ |- _ ] =>
                 match Y with
                   | appendQ _ _ => fail 1
                   | _ => rewrite <- appendQ_assoc in H; destruct (sym_evalStream_quant_append _ _ _ _ _ _ H); subst
                 end
               | [ H : sym_evalStream _ _ _ _ _ (appendQ _ ?X) _ _ _ = SafeUntil (appendQ ?Y ?X) _ _ |- _ ] =>
                 match Y with
                   | appendQ _ _ => fail 1
                   | _ => destruct (sym_evalStream_quant_append _ _ _ _ _ _ H); subst
                 end
               | [ H : sym_evalStream _ _ _ _ _ (appendQ _ (appendQ _ ?X)) _ _ _ = SafeUntil (appendQ ?Y ?X) _ _ |- _ ] =>
                 match Y with
                   | appendQ _ _ => fail 1
                   | _ => rewrite <- appendQ_assoc in H; destruct (sym_evalStream_quant_append _ _ _ _ _ _ H); subst
                 end
               | [ H : EqNat.beq_nat ?X ?Y = true |- _ ] =>
                 symmetry in H; apply EqNat.beq_nat_eq in H
               | [ H : Folds.all2 _ _ _ = true |- _ ] =>
                 eapply all2_tvar_seq_dec_true in H
               | [ H : sym_evalStream _ _ _ _ _ ?QS _ _ _ = _
                 , H' : stateD _ _ ?Uall ?Gall _ (_, ?st) _
                 , H'' : istreamD _ _ _ _ _ ?st _
                 |- _ ] =>
               let t := change (QS) with (appendQ QBase QS) in H at 1 ;
                 eapply IHpath with (env_q := QS) (qs := QBase) (meta_env := Uall) (vars_env := Gall) in H;
                   simpl; subst; intuition (eauto using istreamD_weaken, Valid_weaken with env_resolution) in
               solve [ t ] || (t; [])
               | [ H : forall res : bool, match sym_assertTest _ _ _ _ _ _ _ res with _ => _ end |- _ ] =>
                 specialize (H true); unfold sym_assertTest in H
               | [ H : match ?X with | IL.Eq => _ | _ => _ end = None |- _ ] =>
                 destruct X; congruence
               | [ H : exists x : state, _ |- exists y : state, _ ] =>
                 let s := fresh "st" in
                 solve [ destruct H as [ s ? ] ; exists s ; intuition ]
               | [ H : match ?X with _ => _ end |- _ ] =>
                 (revert H; case_eq X; intros; try contradiction)
               | [ H : match ?X with _ => _ end = _ |- _ ] =>
                 (revert H; case_eq X; intros; try split_congruence)
               | [ H : sym_rvalueD _ _ _ _ = _ |- context [ sym_rvalueD _ _ _ _ ] ] =>
                   erewrite sym_rvalueD_weaken by eauto
               | [ H : option bool |- _ ] => destruct H
             end.

    Lemma evalStream_correct_Safe : forall sound_or_safe cs stn path facts ss qs qs' ss' uvars vars env_q,
      sym_evalStream Prover meval learnHook facts path (appendQ qs env_q) uvars vars ss = Safe (appendQ qs' env_q) ss' ->
      forall meta_env vars_env,
        typeof_env meta_env ++ gatherAll qs = uvars ->
        typeof_env vars_env ++ gatherEx qs = vars ->
        forall st,
          istreamD funcs meta_env vars_env path stn st sound_or_safe ->
        quantD vars_env meta_env qs (fun vars_env meta_env =>
          stateD funcs preds meta_env vars_env cs (stn,st) ss /\
          Valid PC meta_env vars_env facts) ->
        quantD vars_env meta_env qs' (fun vars_env meta_env =>
          match sound_or_safe with
            | None => False
            | Some (st') =>
              stateD funcs preds meta_env vars_env cs (stn, st') ss'
          end).
    Proof.
      Opaque stateD.
      induction path; simpl; intros; sym_eval_prover IHpath; try contradiction.
    Qed.

    Lemma evalStream_correct_SafeUntil : forall sound_or_safe cs stn path facts ss qs qs' ss' is' uvars vars env_q,
      sym_evalStream Prover meval learnHook facts path (appendQ qs env_q) uvars vars ss = SafeUntil (appendQ qs' env_q) ss' is' ->
      forall meta_env vars_env,
        typeof_env meta_env ++ gatherAll qs = uvars ->
        typeof_env vars_env ++ gatherEx qs = vars ->
        forall st,
          istreamD funcs meta_env vars_env path stn st sound_or_safe ->
        quantD vars_env meta_env qs (fun vars_env meta_env =>
          stateD funcs preds meta_env vars_env cs (stn,st) ss /\
          Valid PC meta_env vars_env facts) ->
        quantD vars_env meta_env qs' (fun vars_env meta_env =>
          exists st' : state,
          stateD funcs preds meta_env vars_env cs (stn, st') ss' /\
          istreamD funcs meta_env vars_env is' stn st' sound_or_safe).
    Proof.
      induction path; simpl; intros; sym_eval_prover IHpath; try contradiction.
    Qed.

    Lemma appendQ_QBase_r : forall a, appendQ a QBase = a.
    Proof. clear. induction a; simpl; intros; think; auto. Qed.
(*
    Theorem evalStream_correct : forall sound_or_safe cs stn path facts ss qs env_q uvars vars res,
      sym_evalStream Prover meval learnHook facts path (appendQ qs env_q) uvars vars ss = res ->
      forall meta_env vars_env,
        typeof_env meta_env ++ gatherAll qs = uvars ->
        typeof_env vars_env ++ gatherEx qs = vars ->
        forall st,
          istreamD funcs meta_env vars_env path stn st sound_or_safe ->
        quantD vars_env meta_env qs (fun vars_env meta_env =>
          stateD funcs preds meta_env vars_env cs (stn,st) ss /\
          Valid PC meta_env vars_env facts) ->
        match res with
          | Safe qs' ss' =>
            quantD vars_env meta_env qs' (fun vars_env meta_env =>
              match sound_or_safe with
                | None => False
                | Some (st') => stateD funcs preds meta_env vars_env cs (stn, st') ss'
              end)
          | SafeUntil qs' ss' is' =>
            quantD vars_env meta_env qs' (fun vars_env meta_env =>
              exists st' : state,
                stateD funcs preds meta_env vars_env cs (stn, st') ss' /\
                istreamD funcs meta_env vars_env is' stn st' sound_or_safe)
        end.
    Proof.
      destruct res; intros.
      { destruct (sym_evalStream_quant_append _ _ _ _ _ _ H).
        generalize (@evalStream_correct_Safe sound_or_safe cs stn path facts ss qs (appendQ x qs) s uvars vars env_q). subst.
        rewrite appendQ_assoc.
        intro. eapply H0 in H; eauto. }
      { destruct (sym_evalStream_quant_append _ _ _ _ _ _ H).
        generalize (@evalStream_correct_SafeUntil sound_or_safe cs stn path facts ss qs (appendQ x qs) s i uvars vars QBase);
          subst.
        repeat rewrite appendQ_QBase_r. intro. eapply H0 in H; eauto. }
    Qed.
*)
  End typed2.

End SymIL_Correct.
