Require Import Coq.omega.Omega.
Require Import Coq.Lists.List Bedrock.DepList Bedrock.Word Bedrock.Memory.
Require Import Bedrock.Heaps Bedrock.SepTheoryX.
Require Import Bedrock.Expr Bedrock.SepHeap.
Require Import Bedrock.Prover.
Require Import Bedrock.PropX.
Require Import Bedrock.Env.

Set Implicit Arguments.
Set Strict Implicit.

Section over_types.
  Variable types : list type.

  Inductive Quant : Type :=
  | QAll  : variables -> Quant -> Quant
  | QEx   : variables -> Quant -> Quant
  | QBase : Quant.

  (** NOTE: the top-most quantifier should be the deepest quantifier **)
  (** NOTE: for forward reasoning we want to invert the quantifiers, i.e. All should become uvar and ex should become var *)
  Fixpoint quantD (ex_env all_env : env types) (qs : Quant) (k : env types -> env types -> Prop) : Prop :=
    match qs with
      | QBase => k ex_env all_env
      | QAll vs qs => quantD ex_env all_env qs (fun ex_env all_env => forallEach vs (fun all_ext => k ex_env (all_env ++ all_ext)))
      | QEx vs qs => quantD ex_env all_env qs (fun ex_env all_env => existsEach vs (fun ex_ext => k (ex_env ++ ex_ext) all_env))
    end.

  Fixpoint appendQ (q1 q2 : Quant) : Quant :=
    match q1 with
      | QBase => q2
      | QAll vs q1 => QAll vs (appendQ q1 q2)
      | QEx vs q1 => QEx vs (appendQ q1 q2)
    end.

  Theorem quantD_app : forall qs' qs meta_env vars_env k,
    quantD meta_env vars_env (appendQ qs qs') k <->
    quantD meta_env vars_env qs' (fun meta_env vars_env => quantD meta_env vars_env qs k).
  Proof.
    clear; induction qs; simpl; intros; try rewrite IHqs; try reflexivity.
  Qed.

  Fixpoint gatherEx (qs : Quant) : variables :=
    match qs with
      | QBase => nil
      | QAll _ qs => gatherEx qs
      | QEx vs qs => gatherEx qs ++ vs
    end.

  Fixpoint gatherAll (qs : Quant) : variables :=
    match qs with
      | QBase => nil
      | QAll vs qs => gatherAll qs ++ vs
      | QEx _ qs => gatherAll qs
    end.

  Theorem quantD_impl : forall qs meta_env vars_env (k k' : _ -> _ -> Prop),
    quantD meta_env vars_env qs k ->
    (forall a b,
      typeof_env a = gatherEx qs ->
      typeof_env b = gatherAll qs ->
      k (meta_env ++ a) (vars_env ++ b) ->
      k' (meta_env ++ a) (vars_env ++ b)) ->
    quantD meta_env vars_env qs k'.
  Proof.
    clear. induction qs; simpl; intros; try (eapply IHqs; [ eauto | ]); simpl in *; intros; instantiate; simpl in *;
    repeat match goal with
             | [ |- existsEach _ _ ] => eapply existsEach_sem
             | [ |- forallEach _ _ ] => eapply forallEach_sem; intros
             | [ H : existsEach _ _ |- _ ] =>
               eapply existsEach_sem in H; destruct H
             | [ H : forallEach _ _ |- _ ] =>
               eapply forallEach_sem in H; [ | solve [ eauto ] ]
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ |- exists x, _ /\ _ ] =>
               eexists; split; [ solve [ eauto ] | ]
             | [ |- _ ] => rewrite app_ass in *
           end.
    { eapply H0; eauto. subst. rewrite <- H2. unfold typeof_env. rewrite map_app. auto. }
    { eapply H0; eauto. subst. rewrite <- H1. unfold typeof_env. rewrite map_app. auto. }
    { specialize (H0 nil nil). repeat rewrite app_nil_r in *. auto. }
  Qed.

  Require Import Bedrock.Tactics.

  Theorem gatherEx_appendQ : forall q1 q2,
    gatherEx (appendQ q1 q2) = gatherEx q2 ++ gatherEx q1.
  Proof.
    induction q1; simpl; intros; think; repeat (rewrite app_nil_r || rewrite app_ass); auto.
  Qed.

  Theorem gatherAll_appendQ : forall q1 q2,
    gatherAll (appendQ q1 q2) = gatherAll q2 ++ gatherAll q1.
  Proof.
    induction q1; simpl; intros; think; repeat (rewrite app_nil_r || rewrite app_ass); auto.
  Qed.

  Definition qex (ls : list tvar) (q : Quant) : Quant :=
    match ls with
      | nil => q
      | _ => QEx ls q
    end.

  Definition qall (ls : list tvar) (q : Quant) : Quant :=
    match ls with
      | nil => q
      | _ => QAll ls q
    end.

  Lemma quantD_qex_QEx : forall U G a b P,
    quantD U G (QEx a b) P <-> quantD U G (qex a b) P.
  Proof. clear.
    destruct a; simpl in *; split; intros; auto.
    { eapply quantD_impl; eauto; intros. simpl in *. rewrite app_nil_r in *. auto. }
    { eapply quantD_impl; eauto; intros. simpl in *. rewrite app_nil_r in *. auto. }
  Qed.

  Lemma quantD_qall_QAll : forall U G a b P,
    quantD U G (QAll a b) P <-> quantD U G (qall a b) P.
  Proof. clear.
    destruct a; simpl in *; split; intros; auto.
    { eapply quantD_impl; eauto; intros. simpl in *. rewrite app_nil_r in *. auto. }
    { eapply quantD_impl; eauto; intros. simpl in *. rewrite app_nil_r in *. auto. }
  Qed.

  Lemma appendQ_assoc : forall a b c,
    appendQ (appendQ a b) c = appendQ a (appendQ b c).
  Proof.
    clear. induction a; simpl; intros; try f_equal; eauto.
  Qed.

  Lemma appendQ_QAll : forall a b v,
    appendQ a (QAll v b) = appendQ (appendQ a (QAll v QBase)) b.
  Proof. clear.
    induction a; simpl; intros; try rewrite IHa; eauto.
  Qed.
  Lemma appendQ_QEx : forall a b v,
    appendQ a (QEx v b) = appendQ (appendQ a (QEx v QBase)) b.
  Proof. clear.
    induction a; simpl; intros; try rewrite IHa; eauto.
  Qed.

  Lemma QAll_inj_False : forall a b,
    QAll a b = b -> False.
  Proof. clear.
    induction b; simpl; intros; try congruence; auto.
  Qed.

  Lemma QEx_inj_False : forall a b,
    QEx a b = b -> False.
  Proof. clear.
    induction b; simpl; intros; try congruence; auto.
  Qed.

  Fixpoint qsize (q : Quant) : nat :=
    match q with
      | QBase => 0
      | QAll _ q
      | QEx _ q => S (qsize q)
    end.

  Lemma qsize_appendQ : forall a b,
    qsize (appendQ a b) = qsize a + qsize b.
  Proof.
    clear; induction a; simpl in *; auto.
  Qed.

  Ltac apply_eq f H :=
    match type of H with
      | ?X = ?Y =>
        assert (f X = f Y); [ f_equal; apply H | ]
    end.

  Lemma appendQ_proper : forall a b c,
    appendQ a b = appendQ c b ->
    a = c.
  Proof.
    clear. induction a; destruct c; simpl; intros; try congruence;
    repeat match goal with
             | [ H : QAll _ _ = QAll _ _ |- _ ] => inversion H; clear H; subst
             | [ H : QEx _ _ = QEx _ _ |- _ ] => inversion H; clear H; subst
           end; try solve [ f_equal; eauto ]; exfalso.
    { apply_eq qsize H. simpl in *; rewrite qsize_appendQ in H0. omega. }
    { apply_eq qsize H. simpl in *; rewrite qsize_appendQ in H0. omega. }
    { apply_eq qsize H. simpl in *; rewrite qsize_appendQ in H0. omega. }
    { apply_eq qsize H. simpl in *; rewrite qsize_appendQ in H0. omega. }
  Qed.

End over_types.


Module SymbolicEvaluator (SH : SepHeap).
  Module SEP := SH.SE.
  Module ST := SEP.ST.

  (** Learn hook
   ** - This is the bit of code that gets run with new pure facts are
   **   learned during symbolic evaluation
   **)
  Section LearnHook.
    Variable types_ : list type.
    Variable SymState : Type.

    Definition LearnHook : Type :=
      forall P : ProverT types_, variables -> variables -> SymState -> Facts P -> list (expr types_) -> SymState * Quant.

    Variables pcT stT : tvar.

    Record LearnHook_correct (L : LearnHook)
      (stateD : env types_ -> env types_ ->
        codeSpec (tvarD types_ pcT) (tvarD types_ stT) -> tvarD types_ stT -> SymState -> Prop)
      (funcs : functions types_)
      (preds : SEP.predicates types_ pcT stT) : Prop :=
    { hook_sound : forall P (PC : ProverT_correct P funcs),
      forall uvars vars cs stn_st ss ss' pp new_facts quant,
        stateD uvars vars cs stn_st ss ->
        Valid PC uvars vars pp ->
        AllProvable funcs uvars vars new_facts ->
        L P (typeof_env uvars) (typeof_env vars) ss pp new_facts = (ss', quant) ->
        quantD vars uvars quant (fun vars uvars => stateD uvars vars cs stn_st ss')
    }.
  End LearnHook.

  Module LearnHookDefault.
    Definition LearnHook_default (types : list type) (State : Type) :
      LearnHook types State :=
      fun _ _ _ x _ _ => (x, QBase).

    Definition LearnHook_default_correct types pcT stT State stateD funcs preds :
      @LearnHook_correct types pcT stT State (@LearnHook_default _ _) stateD funcs preds.
    Proof.
      unfold LearnHook_default; econstructor; intros; subst; auto.
      inversion H2. subst; simpl. auto.
    Qed.
  End LearnHookDefault.

  (** Memory Evaluator
   ** - This is the bit of code that gets run when we try to read
   **   or write to memory.
   **)
  Section MemEvaluator.
    Variable types : list type.
    Variables pcT stT : tvar.

    Record MemEvaluator : Type :=
    { sread_word : forall (P : ProverT types), Facts P ->
      expr types -> SH.SHeap types pcT stT -> option (expr types)
    ; swrite_word : forall (P : ProverT types), Facts P ->
      expr types -> expr types -> SH.SHeap types pcT stT -> option (SH.SHeap types pcT stT)

    ; sread_byte : forall (P : ProverT types), Facts P ->
      expr types -> SH.SHeap types pcT stT -> option (expr types)
    ; swrite_byte : forall (P : ProverT types), Facts P ->
      expr types -> expr types -> SH.SHeap types pcT stT -> option (SH.SHeap types pcT stT)
    }.

    Variable eval : MemEvaluator.

    Variable funcs : functions types.
    Variable preds : SEP.predicates types pcT stT.

    Variable stn_st : Type.

    Variables ptrT valT : tvar.

    Hypothesis mem_satisfies : PropX.codeSpec (tvarD types pcT) (tvarD types stT) -> ST.hprop (tvarD types pcT) (tvarD types stT) nil -> stn_st -> Prop.
    Hypothesis ReadWord : stn_st -> tvarD types ptrT -> option (tvarD types valT).
    Hypothesis WriteWord : stn_st -> tvarD types ptrT -> tvarD types valT -> option stn_st.
    Hypothesis ReadByte : stn_st -> tvarD types ptrT -> option (tvarD types valT).
    Hypothesis WriteByte : stn_st -> tvarD types ptrT -> tvarD types valT -> option stn_st.

    Record MemEvaluator_correct : Type :=
    { ReadCorrect :
      forall (P : ProverT types) (PE : ProverT_correct P funcs),
        forall facts pe ve SH,
          sread_word eval P facts pe SH = Some ve ->
          forall uvars vars cs p stn_m,
            Valid PE uvars vars facts ->
            exprD funcs uvars vars pe ptrT = Some p ->
            mem_satisfies cs (SEP.sexprD funcs preds uvars vars (SH.sheapD SH)) stn_m ->
            match exprD funcs uvars vars ve valT with
              | Some v =>
                ReadWord stn_m p = Some v
              | _ => False
            end
    ; WriteCorrect :
      forall (P : ProverT types) (PE : ProverT_correct P funcs),
        forall uvars vars cs facts pe ve SH SH',
          swrite_word eval P facts pe ve SH = Some SH' ->
          Valid PE uvars vars facts ->
          forall p v,
            exprD funcs uvars vars pe ptrT = Some p ->
            exprD funcs uvars vars ve valT = Some v ->
            forall stn_m,
            mem_satisfies cs (SEP.sexprD funcs preds uvars vars (SH.sheapD SH)) stn_m ->
            match WriteWord stn_m p v with
              | None => False
              | Some stn_m' =>
                mem_satisfies cs (SEP.sexprD funcs preds uvars vars (SH.sheapD SH')) stn_m'
            end

    ; ReadByteCorrect :
      forall (P : ProverT types) (PE : ProverT_correct P funcs),
        forall facts pe ve SH,
          sread_byte eval P facts pe SH = Some ve ->
          forall uvars vars cs p stn_m,
            Valid PE uvars vars facts ->
            exprD funcs uvars vars pe ptrT = Some p ->
            mem_satisfies cs (SEP.sexprD funcs preds uvars vars (SH.sheapD SH)) stn_m ->
            match exprD funcs uvars vars ve valT with
              | Some v =>
                ReadByte stn_m p = Some v
              | _ => False
            end
    ; WriteByteCorrect :
      forall (P : ProverT types) (PE : ProverT_correct P funcs),
        forall uvars vars cs facts pe ve SH SH',
          swrite_byte eval P facts pe ve SH = Some SH' ->
          Valid PE uvars vars facts ->
          forall p v,
            exprD funcs uvars vars pe ptrT = Some p ->
            exprD funcs uvars vars ve valT = Some v ->
            forall stn_m,
            mem_satisfies cs (SEP.sexprD funcs preds uvars vars (SH.sheapD SH)) stn_m ->
            match WriteByte stn_m p v with
              | None => False
              | Some stn_m' =>
                mem_satisfies cs (SEP.sexprD funcs preds uvars vars (SH.sheapD SH')) stn_m'
            end
    }.
  End MemEvaluator.

  Record MemEvaluatorPackage (tr : Repr type) (pc st ptr val : tvar)
    (sat : forall ts, codeSpec (tvarD (repr tr ts) pc) (tvarD (repr tr ts) st) ->
      ST.hprop (tvarD (repr tr ts) pc) (tvarD (repr tr ts) st) nil -> tvarD (repr tr ts) st -> Prop)
    (read  : forall ts, tvarD (repr tr ts) st -> tvarD (repr tr ts) ptr -> option (tvarD (repr tr ts) val))
    (write : forall ts, tvarD (repr tr ts) st -> tvarD (repr tr ts) ptr -> tvarD (repr tr ts) val -> option (tvarD (repr tr ts) st))
    (readByte  : forall ts, tvarD (repr tr ts) st -> tvarD (repr tr ts) ptr -> option (tvarD (repr tr ts) val))
    (writeByte : forall ts, tvarD (repr tr ts) st -> tvarD (repr tr ts) ptr -> tvarD (repr tr ts) val -> option (tvarD (repr tr ts) st))
    : Type :=
  { MemEvalTypes : Repr type
  ; MemEvalFuncs : forall ts, Repr (signature (repr tr (repr MemEvalTypes ts)))
  ; MemEvalPreds : forall ts, Repr (SEP.predicate (repr tr (repr MemEvalTypes ts)) pc st)
  ; MemEval : forall ts, MemEvaluator (repr tr (repr MemEvalTypes ts)) pc st
  ; MemEval_correct : forall ts fs ps,
    @MemEvaluator_correct (repr tr (repr MemEvalTypes ts)) pc st (MemEval ts)
      (repr (MemEvalFuncs ts) fs) (repr (MemEvalPreds ts) ps)
      (tvarD (repr tr (repr MemEvalTypes ts)) st) ptr val
      (sat (repr MemEvalTypes ts)) (read (repr MemEvalTypes ts)) (write (repr MemEvalTypes ts))
      (readByte (repr MemEvalTypes ts)) (writeByte (repr MemEvalTypes ts))
  }.

  Module Default.
    Section with_prover.
      Variable types : list type.
      Variables pcT stT : tvar.
      Variable prover : ProverT types.

      Definition smemeval_read_word_default (_ : Facts prover) (_ : expr types)
        (_ : SH.SHeap types pcT stT) : option (expr types) :=
        None.

      Definition smemeval_write_word_default (_ : Facts prover)
        (_ : expr types) (_ : expr types) (_ : SH.SHeap types pcT stT)
        : option (SH.SHeap types pcT stT) :=
        None.
    End with_prover.

    Definition MemEvaluator_default types pcT stT : MemEvaluator types pcT stT.
      constructor.
      apply smemeval_read_word_default.
      apply smemeval_write_word_default.
      apply smemeval_read_word_default.
      apply smemeval_write_word_default.
    Defined.

    Theorem MemEvaluator_default_correct types' (pcT stT : tvar) funcs preds X Y Z A B C D E :
      @MemEvaluator_correct types' pcT stT (MemEvaluator_default types' pcT stT) funcs preds X Y Z A B C D E.
      econstructor.
      simpl; unfold smemeval_read_word_default, smemeval_write_word_default; simpl; congruence.
      simpl; unfold smemeval_read_word_default, smemeval_write_word_default; simpl; congruence.
      simpl; unfold smemeval_read_word_default, smemeval_write_word_default; simpl; congruence.
      simpl; unfold smemeval_read_word_default, smemeval_write_word_default; simpl; congruence.
    Qed.

    Ltac unfolder H :=
      cbv delta
        [ smemeval_read_word_default
          smemeval_write_word_default
          MemEvaluator_default
        ] in H.

    Definition package tr pcT stT ptr val X Y Z A B : @MemEvaluatorPackage tr pcT stT ptr val X Y Z A B :=
      {| MemEvalTypes := nil_Repr EmptySet_type
       ; MemEvalFuncs := fun ts => nil_Repr (Default_signature _)
       ; MemEvalPreds := fun ts => nil_Repr (SEP.Default_predicate _ pcT stT)
       ; MemEval := fun ts => MemEvaluator_default _ _ _
       ; MemEval_correct := fun ts fs ps => MemEvaluator_default_correct _ _ _ _ _ _ _ _ _
       |}.

  End Default.

  (** Evaluators for single predicates
   ** - this abstracts the common case when we are considering
   **   a single predicate in isolation
   ** - TODO: I do not know how to make symbolic memory work with
   **   this definition. I want to use the predicates in SepTheoryX
   **   but there is no generic reading function & I can't specialize
   **   until I know what [valT] refers to.
   **)
  Module PredEval.
    Module SF := SepExpr.SepExprFacts SEP.

    Section typed.
      Variable types : list type.

      Record MemEvalPred : Type :=
      { pred_read_word  :
        forall (P : ProverT types) (facts : Facts P) (args : exprs types) (p : expr types),
          option (expr types)
      ; pred_write_word :
        forall (P : ProverT types) (facts : Facts P) (args : exprs types) (p v : expr types),
          option (exprs types)

      ; pred_read_byte  :
        forall (P : ProverT types) (facts : Facts P) (args : exprs types) (p : expr types),
          option (expr types)
      ; pred_write_byte :
        forall (P : ProverT types) (facts : Facts P) (args : exprs types) (p v : expr types),
          option (exprs types)
      }.

      Variables pcT stT : tvar.

      Variable stn_st : Type.
      Variables ptrT valT : tvar.

      Hypothesis mem_satisfies : PropX.codeSpec (tvarD types pcT) (tvarD types stT) -> ST.hprop (tvarD types pcT) (tvarD types stT) nil -> stn_st -> Prop.
      Hypothesis ReadWord : stn_st -> tvarD types ptrT -> option (tvarD types valT).
      Hypothesis WriteWord : stn_st -> tvarD types ptrT -> tvarD types valT -> option stn_st.
      Hypothesis ReadByte : stn_st -> tvarD types ptrT -> option (tvarD types valT).
      Hypothesis WriteByte : stn_st -> tvarD types ptrT -> tvarD types valT -> option stn_st.

      Variable me : MemEvalPred.

      Record MemEvalPred_correct (Predicate : SEP.predicate types pcT stT)
        (funcs : functions types) : Prop :=
      { sym_read_word_correct : forall P (PE : ProverT_correct P funcs),
        forall args uvars vars cs facts pe p ve stn_st Q,
          pred_read_word me P facts args pe = Some ve ->
          Valid PE uvars vars facts ->
          exprD funcs uvars vars pe ptrT = Some p ->
          match
            applyD (exprD funcs uvars vars) (SEP.SDomain Predicate) args _ (SEP.SDenotation Predicate)
            with
            | None => False
            | Some p => mem_satisfies cs (ST.star p Q) stn_st
          end ->
          match exprD funcs uvars vars ve valT with
            | Some v =>
              ReadWord stn_st p = Some v
            | _ => False
          end
       ; sym_write_word_correct : forall P (PE : ProverT_correct P funcs),
         forall args uvars vars cs facts pe p ve v stn_st args' Q,
           pred_write_word me P facts args pe ve = Some args' ->
           Valid PE uvars vars facts ->
           exprD funcs uvars vars pe ptrT = Some p ->
           exprD funcs uvars vars ve valT = Some v ->
           match
             applyD (@exprD _ funcs uvars vars) (SEP.SDomain Predicate) args _ (SEP.SDenotation Predicate)
             with
             | None => False
             | Some p => mem_satisfies cs (ST.star p Q) stn_st
           end ->
           match
             applyD (@exprD _ funcs uvars vars) (SEP.SDomain Predicate) args' _ (SEP.SDenotation Predicate)
             with
             | None => False
             | Some pr =>
               match WriteWord stn_st p v with
                 | None => False
                 | Some sm' => mem_satisfies cs (ST.star pr Q) sm'
               end
           end

       ; sym_read_byte_correct : forall P (PE : ProverT_correct P funcs),
        forall args uvars vars cs facts pe p ve stn_st Q,
          pred_read_byte me P facts args pe = Some ve ->
          Valid PE uvars vars facts ->
          exprD funcs uvars vars pe ptrT = Some p ->
          match
            applyD (exprD funcs uvars vars) (SEP.SDomain Predicate) args _ (SEP.SDenotation Predicate)
            with
            | None => False
            | Some p => mem_satisfies cs (ST.star p Q) stn_st
          end ->
          match exprD funcs uvars vars ve valT with
            | Some v =>
              ReadByte stn_st p = Some v
            | _ => False
          end
       ; sym_write_byte_correct : forall P (PE : ProverT_correct P funcs),
         forall args uvars vars cs facts pe p ve v stn_st args' Q,
           pred_write_byte me P facts args pe ve = Some args' ->
           Valid PE uvars vars facts ->
           exprD funcs uvars vars pe ptrT = Some p ->
           exprD funcs uvars vars ve valT = Some v ->
           match
             applyD (@exprD _ funcs uvars vars) (SEP.SDomain Predicate) args _ (SEP.SDenotation Predicate)
             with
             | None => False
             | Some p => mem_satisfies cs (ST.star p Q) stn_st
           end ->
           match
             applyD (@exprD _ funcs uvars vars) (SEP.SDomain Predicate) args' _ (SEP.SDenotation Predicate)
             with
             | None => False
             | Some pr =>
               match WriteByte stn_st p v with
                 | None => False
                 | Some sm' => mem_satisfies cs (ST.star pr Q) sm'
               end
           end
      }.
    End typed.

    Section search_read_write.
      Variable types : list type.
      Variable T : Type.
      Variable F : exprs types -> option T.
      Variable F_upd : exprs types -> option (exprs types).

      Fixpoint fold_args (es : list (exprs types)) : option T :=
        match es with
          | nil => None
          | a :: b =>
            match F a with
              | None => fold_args b
              | Some r => Some r
            end
        end.

      Theorem fold_args_correct : forall es v,
        fold_args es = Some v ->
        exists k, In k es /\ F k = Some v.
      Proof.
        clear. induction es.
        simpl; congruence.
        simpl. case_eq (F a); intros.
        inversion H0. subst. eauto.
        eapply IHes in H0. destruct H0.
        exists x. tauto.
      Qed.


      Fixpoint fold_args_update (es : list (exprs types)) : option (list (exprs types)) :=
        match es with
          | nil => None
          | a :: b =>
            match F_upd a with
              | None => match fold_args_update b with
                          | None => None
                          | Some b => Some (a :: b)
                        end
              | Some r => Some (r :: b)
            end
        end.

      Theorem fold_args_update_correct : forall es es',
        fold_args_update es = Some es' ->
        exists pre, exists post, exists k, exists k',
          es = pre ++ k :: post /\
          F_upd k = Some k' /\
          es' = pre ++ k' :: post.
      Proof.
        clear. induction es.
        simpl; congruence.
        simpl. case_eq (F_upd a); intros.
        inversion H0. subst. do 4 eexists; intuition eauto.
        instantiate (2 := nil). reflexivity. reflexivity.

        generalize dependent H0.
        case_eq (fold_args_update es); intros.
        inversion H1; subst. eapply IHes in H0.
        do 4 destruct H0. exists (a :: x). exists x0.
        eexists; eexists; intuition; subst; eauto. reflexivity.

        congruence.
      Qed.

    End search_read_write.

    Section To_MemEvaluator.
      Variable types : list type.
      Variables pcT stT : tvar.

      Variable mep : MemEvalPred types.
      Variable predIndex : nat.

      Definition MemEvalPred_to_MemEvaluator : MemEvaluator types pcT stT :=
        {| sread_word := fun (P : ProverT types) (F : Facts P) (p : expr types) (h : SH.SHeap types pcT stT) =>
           let impures := SH.impures h in
           let argss := FM.find predIndex impures in
           match argss with
             | None => None
             | Some argss => fold_args (fun args => @pred_read_word _ mep P F args p) argss
           end
         ; swrite_word := fun (P : ProverT types) (F : Facts P) (p v : expr types) (h : SH.SHeap types pcT stT) =>
           let impures := SH.impures h in
           let argss := FM.find predIndex impures in
           match argss with
             | None => None
             | Some argss =>
               match fold_args_update (fun args => @pred_write_word _ mep P F args p v) argss with
                 | None => None
                 | Some argss =>
                   Some {| SH.impures := FM.add predIndex argss impures
                         ; SH.pures   := SH.pures h
                         ; SH.other   := SH.other h
                         |}
               end
           end

         ; sread_byte := fun (P : ProverT types) (F : Facts P) (p : expr types) (h : SH.SHeap types pcT stT) =>
           let impures := SH.impures h in
           let argss := FM.find predIndex impures in
           match argss with
             | None => None
             | Some argss => fold_args (fun args => @pred_read_byte _ mep P F args p) argss
           end
         ; swrite_byte := fun (P : ProverT types) (F : Facts P) (p v : expr types) (h : SH.SHeap types pcT stT) =>
           let impures := SH.impures h in
           let argss := FM.find predIndex impures in
           match argss with
             | None => None
             | Some argss =>
               match fold_args_update (fun args => @pred_write_byte _ mep P F args p v) argss with
                 | None => None
                 | Some argss =>
                   Some {| SH.impures := FM.add predIndex argss impures
                         ; SH.pures   := SH.pures h
                         ; SH.other   := SH.other h
                         |}
               end
           end
         |}.

      (** Correctness **)
      Variable funcs : functions types.
      Variable preds : SEP.predicates types pcT stT.

      Variable stn_st : Type.

      Variables ptrT valT : tvar.

      Hypothesis mem_satisfies : PropX.codeSpec (tvarD types pcT) (tvarD types stT) -> ST.hprop (tvarD types pcT) (tvarD types stT) nil -> stn_st -> Prop.
      Hypothesis ReadWord : stn_st -> tvarD types ptrT -> option (tvarD types valT).
      Hypothesis WriteWord : stn_st -> tvarD types ptrT -> tvarD types valT -> option stn_st.
      Hypothesis ReadByte : stn_st -> tvarD types ptrT -> option (tvarD types valT).
      Hypothesis WriteByte : stn_st -> tvarD types ptrT -> tvarD types valT -> option stn_st.

      Variable pred : SEP.predicate types pcT stT.
      Hypothesis predAt : nth_error preds predIndex = Some pred.
      Hypothesis pred_correct :
        @MemEvalPred_correct types pcT stT stn_st ptrT valT mem_satisfies
        ReadWord WriteWord ReadByte WriteByte mep pred funcs.

      Lemma in_split : forall T (x : T) ls,
        In x ls -> exists a b, ls = a ++ x :: b.
      Proof.
        clear. induction ls. destruct 1.
        intros. destruct H. subst. exists nil. simpl; eauto.
        apply IHls in H. do 2 destruct H. subst; eauto. exists (a :: x0). simpl; eauto.
      Qed.

      (** This is all going to get put in a record **)
      Hypothesis mem_satisfies_himp : forall cs P Q stn_st,
        mem_satisfies cs P stn_st ->
        ST.himp cs P Q ->
        mem_satisfies cs Q stn_st.
      Hypothesis mem_satisfies_pure : forall cs p P stn_st,
        mem_satisfies cs (ST.star (ST.inj p) P) stn_st ->
        interp cs p.

      Lemma pull_single : forall cs uvars vars SH x x1 x0 stn_st,
        FM.find predIndex (SH.impures SH) = Some (x0 ++ x :: x1) ->
        mem_satisfies cs (SEP.sexprD funcs preds uvars vars (SH.sheapD SH)) stn_st ->
        mem_satisfies cs (SEP.sexprD funcs preds uvars vars
          (SEP.Star (SEP.Func predIndex x)
            (SH.starred (SEP.Func predIndex) x0 (SH.starred (SEP.Func predIndex) x1
              (SH.sheapD {| SH.impures := FM.remove predIndex (SH.impures SH)
                ; SH.pures := SH.pures SH
                ; SH.other := SH.other SH
              |}))))) stn_st.
      Proof.
        intros.
        assert (SEP.heq funcs preds uvars vars cs
          (SH.sheapD SH)
          (SEP.Star (SEP.Func predIndex x)
            (SH.starred (SEP.Func predIndex) x0 (SH.starred (SEP.Func predIndex) x1
              (SH.sheapD {| SH.impures := FM.remove predIndex (SH.impures SH)
                ; SH.pures := SH.pures SH
                ; SH.other := SH.other SH
              |}))))).
        { rewrite SH.starred_base. rewrite SH.starred_base.
          repeat rewrite SH.sheapD_def. simpl. SF.heq_canceler.
          rewrite SH.impuresD_Add with (f := predIndex) (argss := x0 ++ x :: x1).
          rewrite SH.starred_def. rewrite fold_right_app. simpl.
          rewrite <- SH.starred_def. rewrite SH.starred_base. rewrite <- SH.starred_def.
          SF.heq_canceler.
          { unfold MM.PROPS.Add. intros. repeat (rewrite MM.FACTS.add_o || rewrite MM.FACTS.remove_o).
            destruct (MF.FACTS.eq_dec predIndex y); subst; auto. }
          { intro. apply MM.FACTS.remove_in_iff in H1. intuition; congruence. } }
        eapply mem_satisfies_himp; eauto. apply SF.heq_himp; auto.
      Qed.

      Theorem MemEvaluator_MemEvalPred_correct : @MemEvaluator_correct types pcT stT MemEvalPred_to_MemEvaluator
        funcs preds stn_st ptrT valT mem_satisfies ReadWord WriteWord ReadByte WriteByte.
      Proof.
        constructor; simpl.

        { intros. revert H. case_eq (FM.find predIndex (SH.impures SH)); try congruence; intros.
          eapply fold_args_correct in H3. destruct H3. intuition.
          apply in_split in H4. destruct H4. destruct H3. subst.
          eapply pull_single in H; eauto.
          simpl in *. rewrite predAt in H.
          eapply sym_read_word_correct with (cs := cs) (Q := SEP.sexprD funcs preds uvars vars
               (SH.starred (SEP.Func predIndex) x0
                  (SH.starred (SEP.Func predIndex) x1
                     (SH.sheapD
                        {|
                        SH.impures := FM.remove (elt:=
                                        list (exprs types)) predIndex
                                        (SH.impures SH);
                        SH.pures := SH.pures SH;
                        SH.other := SH.other SH |})))) in H5; eauto.
          revert H. match goal with
                       | [ |- context [ match ?X with | _ => _ end ] ] => case_eq X
                     end; intros; auto.
          apply mem_satisfies_pure in H3. PropXTac.propxFo. }

        { intros. revert H.
          case_eq (FM.find predIndex (SH.impures SH)); try congruence.
          do 2 intro.
          case_eq (fold_args_update (fun args => pred_write_word mep P facts args pe ve) l); try congruence; intros.
          inversion H5; clear H5; subst.
          apply fold_args_update_correct in H4. do 4 destruct H4; intuition; subst.
          eapply pull_single in H; eauto. simpl in H.
          rewrite predAt in H.
          eapply sym_write_word_correct with (cs := cs)
            (Q := (SEP.sexprD funcs preds uvars vars
              (SH.starred (SEP.Func predIndex) x
                 (SH.starred (SEP.Func predIndex) x0
                    (SH.sheapD
                       {|
                       SH.impures := FM.remove (elt:=
                                       list (exprs types)) predIndex
                                       (SH.impures SH);
                       SH.pures := SH.pures SH;
                       SH.other := SH.other SH |})))))
            in H4; eauto.
          2: instantiate (1 := stn_m).
          revert H4.
          match goal with
            | [ |- match ?X with _ => _ end -> _ ] =>
              case_eq X; try contradiction
          end; intros.
          revert H5. case_eq (WriteWord stn_m p v); try contradiction; intros.
          eapply mem_satisfies_himp with (P :=
            (SEP.sexprD funcs preds uvars vars
              (SEP.Star (SEP.Func predIndex x2)
            (SH.starred (SEP.Func predIndex) x
               (SH.starred (SEP.Func predIndex) x0
                  (SH.sheapD
                     {|
                     SH.impures := FM.remove (elt:=
                                     list (exprs types)) predIndex
                                     (SH.impures SH);
                     SH.pures := SH.pures SH;
                     SH.other := SH.other SH |})))))).
          simpl. rewrite predAt. rewrite H4. eauto.
          match goal with
            | [ |- ST.himp ?cs (SEP.sexprD ?F ?P ?U ?G ?L) (SEP.sexprD _ _ _ _ ?R) ] =>
              change (SEP.himp F P U G cs L R)
          end.
          apply SF.heq_himp. do 2 rewrite SH.starred_base.
          repeat rewrite SH.sheapD_def; simpl. symmetry.
          rewrite SH.impuresD_Add with (f := predIndex) (argss := x ++ x2 :: x0) (i := FM.remove predIndex (SH.impures SH)).
          rewrite SH.starred_def. rewrite fold_right_app. simpl. rewrite <- SH.starred_def. rewrite SH.starred_base.
          rewrite <- SH.starred_def. SF.heq_canceler.
          { unfold MM.PROPS.Add. intros; repeat (rewrite MM.FACTS.add_o || rewrite MM.FACTS.remove_o).
            destruct (MF.FACTS.eq_dec predIndex y); auto. }
          { intro. apply MM.FACTS.remove_in_iff in H7; intuition congruence. }
          revert H.
          match goal with
            | [ |- context [ match ?X with _ => _ end ] ] =>
              case_eq X
          end; intros; eauto.
          apply mem_satisfies_pure in H5. PropXTac.propxFo. }

        { intros. revert H. case_eq (FM.find predIndex (SH.impures SH)); try congruence; intros.
          eapply fold_args_correct in H3. destruct H3. intuition.
          apply in_split in H4. destruct H4. destruct H3. subst.
          eapply pull_single in H; eauto.
          simpl in *. rewrite predAt in H.
          eapply sym_read_byte_correct with (cs := cs) (Q := SEP.sexprD funcs preds uvars vars
               (SH.starred (SEP.Func predIndex) x0
                  (SH.starred (SEP.Func predIndex) x1
                     (SH.sheapD
                        {|
                        SH.impures := FM.remove (elt:=
                                        list (exprs types)) predIndex
                                        (SH.impures SH);
                        SH.pures := SH.pures SH;
                        SH.other := SH.other SH |})))) in H5; eauto.
          revert H. match goal with
                       | [ |- context [ match ?X with | _ => _ end ] ] => case_eq X
                     end; intros; auto.
          apply mem_satisfies_pure in H3. PropXTac.propxFo. }

        { intros. revert H.
          case_eq (FM.find predIndex (SH.impures SH)); try congruence.
          do 2 intro.
          case_eq (fold_args_update (fun args => pred_write_byte mep P facts args pe ve) l); try congruence; intros.
          inversion H5; clear H5; subst.
          apply fold_args_update_correct in H4. do 4 destruct H4; intuition; subst.
          eapply pull_single in H; eauto. simpl in H.
          rewrite predAt in H.
          eapply sym_write_byte_correct with (cs := cs)
            (Q := (SEP.sexprD funcs preds uvars vars
              (SH.starred (SEP.Func predIndex) x
                 (SH.starred (SEP.Func predIndex) x0
                    (SH.sheapD
                       {|
                       SH.impures := FM.remove (elt:=
                                       list (exprs types)) predIndex
                                       (SH.impures SH);
                       SH.pures := SH.pures SH;
                       SH.other := SH.other SH |})))))
            in H4; eauto.
          2: instantiate (1 := stn_m).
          revert H4.
          match goal with
            | [ |- match ?X with _ => _ end -> _ ] =>
              case_eq X; try contradiction
          end; intros.
          revert H5. case_eq (WriteByte stn_m p v); try contradiction; intros.
          eapply mem_satisfies_himp with (P :=
            (SEP.sexprD funcs preds uvars vars
              (SEP.Star (SEP.Func predIndex x2)
            (SH.starred (SEP.Func predIndex) x
               (SH.starred (SEP.Func predIndex) x0
                  (SH.sheapD
                     {|
                     SH.impures := FM.remove (elt:=
                                     list (exprs types)) predIndex
                                     (SH.impures SH);
                     SH.pures := SH.pures SH;
                     SH.other := SH.other SH |})))))).
          simpl. rewrite predAt. rewrite H4. eauto.
          match goal with
            | [ |- ST.himp ?cs (SEP.sexprD ?F ?P ?U ?G ?L) (SEP.sexprD _ _ _ _ ?R) ] =>
              change (SEP.himp F P U G cs L R)
          end.
          apply SF.heq_himp. do 2 rewrite SH.starred_base.
          repeat rewrite SH.sheapD_def; simpl. symmetry.
          rewrite SH.impuresD_Add with (f := predIndex) (argss := x ++ x2 :: x0) (i := FM.remove predIndex (SH.impures SH)).
          rewrite SH.starred_def. rewrite fold_right_app. simpl. rewrite <- SH.starred_def. rewrite SH.starred_base.
          rewrite <- SH.starred_def. SF.heq_canceler.
          { unfold MM.PROPS.Add. intros; repeat (rewrite MM.FACTS.add_o || rewrite MM.FACTS.remove_o).
            destruct (MF.FACTS.eq_dec predIndex y); auto. }
          { intro. apply MM.FACTS.remove_in_iff in H7; intuition congruence. }
          revert H.
          match goal with
            | [ |- context [ match ?X with _ => _ end ] ] =>
              case_eq X
          end; intros; eauto.
          apply mem_satisfies_pure in H5. PropXTac.propxFo. }
      Qed.

    End To_MemEvaluator.

  End PredEval.

  Module Composite.
    Section typed.
      Variable types : list type.
      Variable pcT stT : tvar.

      Definition MemEvaluator_composite (l r : MemEvaluator types pcT stT) : MemEvaluator types pcT stT :=
        {| sread_word := fun P f e h =>
           match sread_word l P f e h with
             | None => sread_word r P f e h
             | Some v => Some v
           end
         ; swrite_word := fun P f p v h =>
           match swrite_word l P f p v h with
             | None => swrite_word r P f p v h
             | Some v => Some v
           end

         ; sread_byte := fun P f e h =>
           match sread_byte l P f e h with
             | None => sread_byte r P f e h
             | Some v => Some v
           end
         ; swrite_byte := fun P f p v h =>
           match swrite_byte l P f p v h with
             | None => swrite_byte r P f p v h
             | Some v => Some v
           end
         |}.

      Variables evalL evalR : MemEvaluator types pcT stT.

      Variable funcs : functions types.
      Variable preds : SEP.predicates types pcT stT.

      Variable stn_st : Type.

      Variables ptrT valT : tvar.

      Hypothesis mem_satisfies : PropX.codeSpec (tvarD types pcT) (tvarD types stT) -> ST.hprop (tvarD types pcT) (tvarD types stT) nil -> stn_st -> Prop.
      Hypothesis ReadWord : stn_st -> tvarD types ptrT -> option (tvarD types valT).
      Hypothesis WriteWord : stn_st -> tvarD types ptrT -> tvarD types valT -> option stn_st.
      Hypothesis ReadByte : stn_st -> tvarD types ptrT -> option (tvarD types valT).
      Hypothesis WriteByte : stn_st -> tvarD types ptrT -> tvarD types valT -> option stn_st.

      Hypothesis Lcorr : MemEvaluator_correct evalL funcs preds ptrT valT
        mem_satisfies ReadWord WriteWord ReadByte WriteByte.
      Hypothesis Rcorr : MemEvaluator_correct evalR funcs preds ptrT valT
        mem_satisfies ReadWord WriteWord ReadByte WriteByte.

      Theorem MemEvaluator_correct_composite : @MemEvaluator_correct types pcT stT (MemEvaluator_composite evalL evalR)
        funcs preds stn_st ptrT valT mem_satisfies ReadWord WriteWord ReadByte WriteByte.
      Proof.
        unfold MemEvaluator_composite. econstructor; intros; simpl in *;
        repeat match goal with
                 | [ H : match ?X with None => _ | Some _ => _ end = Some _ |- _ ] => revert H; case_eq X; intros
                 | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                 | [ |- _ ] =>
                   eapply ReadCorrect; [ | eassumption | | | ]; eauto
                 | [ |- _ ] =>
                   eapply WriteCorrect; [ | eassumption | | | | ]; eauto
                 | [ |- _ ] =>
                   eapply ReadByteCorrect; [ | eassumption | | | ]; eauto
                 | [ |- _ ] =>
                   eapply WriteByteCorrect; [ | eassumption | | | | ]; eauto
               end.
      Qed.
    End typed.
  End Composite.

End SymbolicEvaluator.
