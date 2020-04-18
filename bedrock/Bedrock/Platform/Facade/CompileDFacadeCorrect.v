Set Implicit Arguments.

Require Import Bedrock.Platform.Facade.CompileDFacade.
Export CompileDFacade.

Require Import Bedrock.Platform.Facade.FacadeFacts.
Require Import Bedrock.Platform.Facade.DFacadeFacts.
Require Import Bedrock.Platform.Facade.Facade.
Require Import Bedrock.Platform.Facade.DFacade.

Require Import Bedrock.Platform.Facade.NameDecoration.
Require Import Bedrock.Platform.Cito.SyntaxExpr.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

Require Import Bedrock.Platform.Cito.Option.
Require Import Coq.Bool.Bool.

Require Import Bedrock.Platform.Cito.GeneralTactics.
Require Import Bedrock.Platform.Cito.GeneralTactics3.
Require Import Bedrock.Platform.Cito.GeneralTactics4.
Require Import Bedrock.Platform.Cito.GeneralTactics5.

Require Import Bedrock.StringSet.
Import StringSet.
Require Import Bedrock.Platform.Cito.StringSetFacts.

Lemma syntax_ok_fptr_not_fv s : is_syntax_ok s = true -> ~ In fun_ptr_varname (free_vars s).
Proof.
  intros Hsyn.
  unfold is_syntax_ok in *.
  eapply andb_true_iff in Hsyn.
  openhyp.
  unfold is_good_varnames in *.
  intro Hin.
  eapply for_all_elim in H0; eauto.
  intuition.
Qed.

Section ADTValue.

  Variable ADTValue : Type.

  Notation State := (@State ADTValue).
  Notation Env := (@Env ADTValue).
  Notation Value := (@Value ADTValue).
  Notation FuncSpec := (@FuncSpec ADTValue).
  Notation RunsTo := (@RunsTo ADTValue).
  Notation Safe := (@Safe ADTValue).

  Require Import Bedrock.Memory.
  Require Import Bedrock.Platform.Cito.GLabel.

  Notation FEnv := (@Facade.Env ADTValue).
  Notation FFuncSpec := (@Facade.FuncSpec ADTValue).
  Notation FRunsTo := (@Facade.RunsTo ADTValue).
  Notation FSafe := (@Facade.Safe ADTValue).

  Require Import Bedrock.Platform.Cito.GLabelMap.
  Import GLabelMap.

  Arguments Facade.Operational {ADTValue} _.

  Definition compile_spec (spec : FuncSpec) : FFuncSpec :=
    match spec with
      | Axiomatic s => Facade.Axiomatic s
      | Operational s => Facade.Operational (compile_op s)
    end.

  Definition fenv_impls_env (fenv : FEnv) (env : Env) :=
    forall lbl spec,
      find lbl env = Some spec ->
      exists w,
        Label2Word fenv lbl = Some w /\
        Word2Spec fenv w = Some (compile_spec spec).

  Require Import Coq.Lists.List.
  Require Import Bedrock.Platform.Cito.ListFacts3.
  Require Import Bedrock.Platform.Cito.ListFacts4.

  Require Import Coq.Setoids.Setoid.

  Require Import Bedrock.Platform.Cito.StringMap.
  Import StringMap.
  Require Import Bedrock.Platform.Cito.StringMapFacts.
  Import FMapNotations.
  Local Open Scope fmap_scope.

  Hint Extern 0 (_ == _) => reflexivity.

  Arguments SCA {ADTValue} _.
  Arguments ADT {ADTValue} _.

  Existing Instance EqualOn_rel_Reflexive.
  Existing Instance EqualOn_rel_Symmetric.
  Existing Instance EqualOn_rel_Transitive.

  (* equivalent relation between states that only differ on temporary variables and temporary variables don't map to ADT values *)
  Section equiv.

    Variable s : StringSet.t.

    Definition no_adt_in (m : State) := forall k, StringSet.In k s -> not_mapsto_adt k m = true.

    Definition equiv a b := EqualOn (fun k => ~ StringSet.In k s) a b /\ no_adt_in a /\ no_adt_in b.

    Infix "===" := equiv (at level 70).

    Lemma equiv_sym a b : a === b -> b === a.
    Proof.
      intros H; unfold equiv in *.
      openhyp.
      repeat try_split; eauto.
      symmetry; eauto.
    Qed.

    Lemma equiv_trans a b c : a === b -> b === c -> a === c.
    Proof.
      intros H1 H2.
      unfold equiv in *.
      openhyp.
      repeat try_split; eauto.
      etransitivity; eauto.
    Qed.

    Global Add Relation State equiv
        symmetry proved by equiv_sym
        transitivity proved by equiv_trans
          as equiv_rel.

    Lemma Equal_not_mapsto_adt (st st' : State) k : st == st' -> not_mapsto_adt k st = not_mapsto_adt k st'.
    Proof.
      intros Heq.
      unfold not_mapsto_adt, is_mapsto_adt.
      rewrite Heq.
      eauto.
    Qed.

    Import Logic.

    Global Add Morphism (@not_mapsto_adt ADTValue) with signature eq ==> Equal ==> eq as Equal_not_mapsto_adt_m.
    Proof.
      intros; eapply Equal_not_mapsto_adt; eauto.
    Qed.

    Lemma Equal_no_adt_in st st' : st == st' -> (no_adt_in st <-> no_adt_in st').
    Proof.
      intros Heq.
      unfold no_adt_in in *.
      split; intros H.
      - intros k Hk.
        rewrite <- Heq; eauto.
      - intros k Hk.
        rewrite Heq; eauto.
    Qed.

    Global Add Morphism no_adt_in with signature Equal ==> iff as Equal_no_adt_in_m.
    Proof.
      intros; eapply Equal_no_adt_in; eauto.
    Qed.

    Lemma Equal_equiv a a' b b' : a == a' -> b == b' -> (a === b <-> a' === b').
    Proof.
      intros Ha Hb.
      unfold equiv in *.
      split; intro H.
      - rewrite <- Ha.
        rewrite <- Hb.
        eauto.
      - rewrite Ha.
        rewrite Hb.
        eauto.
    Qed.

    Global Add Morphism equiv
        with signature Equal ==> Equal ==> iff as Equal_equiv_m.
    Proof.
      intros; eapply Equal_equiv; eauto.
    Qed.

    Lemma find_adt_equiv st1 st2 k a : find k st1 = Some (ADT a) -> st1 === st2 -> find k st2 = Some (ADT a).
    Proof.
      intros Hf Heqv.
      unfold equiv in *.
      destruct Heqv as [Heqon [Hnadt1 Hnadt2]].
      destruct (StringSetFacts.In_dec k s) as [Hin | Hnin].
      - eapply Hnadt1 in Hin.
        eapply not_mapsto_adt_iff in Hin.
        contradict Hin.
        eexists; eauto.
      - rewrite <- Heqon by eauto.
        eauto.
    Qed.

  End equiv.

  Existing Instance equiv_rel_Symmetric.
  Existing Instance equiv_rel_Transitive.

  Lemma not_in_no_adt_in_add s k v st : no_adt_in s st -> ~ StringSet.In k s -> no_adt_in s (add k v st).
  Proof.
    intros H Hnin.
    unfold no_adt_in in *.
    intros k' Hk'.
    unfold not_mapsto_adt in *.
    unfold is_mapsto_adt in *.
    destruct (string_dec k k') as [Heqk | Hnek].
    - subst.
      contradiction.
    - rewrite add_neq_o by eauto.
      eauto.
  Qed.

  Lemma no_adt_in_remove s k st : no_adt_in s st -> no_adt_in s (remove k st).
  Proof.
    intros H.
    unfold no_adt_in in *.
    intros k' Hk'.
    unfold not_mapsto_adt in *.
    unfold is_mapsto_adt in *.
    destruct (string_dec k k') as [Heqk | Hnek].
    - subst.
      rewrite remove_eq_o by eauto.
      eauto.
    - rewrite remove_neq_o by eauto.
      eauto.
  Qed.

  Coercion StringSet.singleton : StringSet.elt >-> StringSet.t.

  Notation equivf := (equiv (StringSet.singleton fun_ptr_varname)).
  Infix "===" := equivf (at level 70).

  Lemma not_mapsto_adt_no_adt_in x st : not_mapsto_adt x st = true -> no_adt_in (StringSet.singleton x) st.
  Proof.
    intros Hnadt.
    unfold no_adt_in.
    intros k Hk.
    eapply StringSetFacts.singleton_iff in Hk.
    subst.
    eauto.
  Qed.

  Lemma no_adt_in_not_mapsto_adt x st : no_adt_in (StringSet.singleton x) st -> not_mapsto_adt x st = true.
  Proof.
    intros H.
    unfold no_adt_in in *.
    eapply H.
    eapply StringSetFacts.singleton_iff; eauto.
  Qed.

  Lemma equiv_refl st : not_mapsto_adt fun_ptr_varname st = true -> st === st.
  Proof.
    intros Hnadt.
    unfold equiv.
    repeat try_split.
    - reflexivity.
    - eapply not_mapsto_adt_no_adt_in; eauto.
    - eapply not_mapsto_adt_no_adt_in; eauto.
  Qed.

  Lemma equiv_nma_fpv st1 st2 : st1 === st2 -> not_mapsto_adt fun_ptr_varname st2 = true.
  Proof.
    intros Heqv.
    unfold equiv in *.
    openhyp.
    eapply no_adt_in_not_mapsto_adt; eauto.
  Qed.

  Lemma not_find_fpv_adt st1 st2 (a : ADTValue) : st1 === st2 -> find fun_ptr_varname st2 <> Some (ADT a).
  Proof.
    intros Heqv Hf.
    eapply equiv_nma_fpv in Heqv.
    eapply not_mapsto_adt_iff in Heqv.
    contradict Heqv.
    eexists; eauto.
  Qed.

  Lemma no_adt_in_add_sca k w st : no_adt_in (StringSet.singleton k) (add k (SCA w) st).
  Proof.
    unfold no_adt_in.
    intros k' Hk'.
    eapply StringSetFacts.singleton_iff in Hk'.
    subst.
    unfold not_mapsto_adt, is_mapsto_adt.
    rewrite add_eq_o by eauto.
    eauto.
  Qed.

  Lemma equiv_intro st1 st2 w st1' : st1' === st2 -> st1 == add fun_ptr_varname (SCA w) st2 -> st1 === st2.
  Proof.
    intros Heqv Heq.
    unfold equiv in *.
    destruct Heqv as [Heqon [Hnadt1 Hnadt2]].
    rewrite Heq.
    repeat try_split.
    - eapply out_add_EqualOn.
      + reflexivity.
      + intros Hnot; eapply Hnot.
        eapply StringSetFacts.singleton_iff; eauto.
    - eapply no_adt_in_add_sca; eauto.
    - eauto.
  Qed.

  Lemma find_equiv_fpv (st1 st2 : State) x : st1 === st2 -> x <> fun_ptr_varname -> find x st1 = find x st2.
  Proof.
    intros Heq Hgn.
    unfold equiv in *.
    simpl in *.
    destruct Heq as [Heq [Hnadt1 Hnadt2]].
    eapply Heq.
    eapply StringSetFacts.singleton_not_iff; eauto.
  Qed.
  Arguments find_equiv_fpv st1 st2 [_] _ _.

  Lemma find_equiv st1 st2 x : st1 === st2 -> is_good_varname x = true -> find x st1 = find x st2.
  Proof.
    intros Heq Hgn.
    unfold equiv in *.
    simpl in *.
    destruct Heq as [Heq [Hnadt1 Hnadt2]].
    destruct (string_dec x fun_ptr_varname) as [Heqx | Hnex].
    - subst.
      intuition.
    - eapply Heq.
      eapply singleton_not_iff; eauto.
  Qed.
  Arguments find_equiv st1 st2 [_] _ _.

  Section good_varname_x.

    Variable x : string.
    Hypothesis Hgn : is_good_varname x = true.

    Import Logic.

    Global Add Morphism (find x) with signature equivf ==> eq as find_equiv_m.
    Proof.
      intros; eapply find_equiv; eauto.
    Qed.

    Lemma not_mapsto_adt_equiv st1 st2 : st1 === st2 -> not_mapsto_adt x st1 = not_mapsto_adt x st2.
    Proof.
      intros Heq.
      unfold not_mapsto_adt, is_mapsto_adt.
      rewrite Heq.
      eauto.
    Qed.

    Lemma add_equiv st1 st2 v : st1 === st2 -> add x v st1 === add x v st2.
    Proof.
      intros Heq.
      unfold equiv in *.
      destruct Heq as [Heqon [Hnadt1 Hnadt2]].
      repeat try_split.
      - eapply add_EqualOn; eauto.
      - destruct (string_dec fun_ptr_varname x) as [Heqx | Hnex].
        + subst.
          discriminate Hgn.
        + eapply not_in_no_adt_in_add; eauto.
          eapply singleton_not_iff; eauto.
      - destruct (string_dec fun_ptr_varname x) as [Heqx | Hnex].
        + subst.
          discriminate Hgn.
        + eapply not_in_no_adt_in_add; eauto.
          eapply singleton_not_iff; eauto.
    Qed.

    Lemma remove_equiv st1 st2 : st1 === st2 -> remove x st1 === remove x st2.
    Proof.
      intros Heq.
      unfold equiv in *.
      destruct Heq as [Heqon [Hnadt1 Hnadt2]].
      repeat try_split.
      - eapply remove_EqualOn; eauto.
      - destruct (string_dec fun_ptr_varname x) as [Heqx | Hnex].
        + subst.
          discriminate Hgn.
        + eapply no_adt_in_remove; eauto.
      - destruct (string_dec fun_ptr_varname x) as [Heqx | Hnex].
        + subst.
          discriminate Hgn.
        + eapply no_adt_in_remove; eauto.
    Qed.

  End good_varname_x.

  Lemma mapM_find_equiv st1 st2 ls : st1 === st2 -> List.forallb is_good_varname ls = true -> mapM (sel st1) ls = mapM (sel st2) ls.
  Proof.
    induction ls; simpl; intros Heqv Hgn.
    - eauto.
    - rename a into k.
      eapply andb_true_iff in Hgn.
      destruct Hgn as [Hgnk Hgn].
      unfold sel in *.
      rewrite (find_equiv st1 st2) by eauto.
      destruct (option_dec (find k st2)) as [ [v Heq] | Hneq]; [rewrite Heq | rewrite Hneq]; try discriminate; try reflexivity.
      rewrite IHls by eauto.
      eauto.
  Qed.
  Arguments mapM_find_equiv st1 st2 [_] _ _.

  Lemma map_find_equiv st1 st2 ls : st1 === st2 -> List.forallb is_good_varname ls = true -> List.map (sel st1) ls = List.map (sel st2) ls.
  Proof.
    induction ls; simpl; intros Heqv Hgn.
    - eauto.
    - rename a into x.
      eapply andb_true_iff in Hgn.
      destruct Hgn as [Hgnx Hgn].
      f_equal.
      + eapply find_equiv; eauto.
      + eauto.
  Qed.
  Arguments map_find_equiv st1 st2 [_] _ _.

  Lemma eval_equiv st1 st2 e : st1 === st2 -> is_syntax_ok_e e = true -> eval st1 e = eval st2 e.
  Proof.
    induction e; simpl; intros Heqv Hsyn.
    - eapply is_syntax_ok_e_var_elim in Hsyn.
      eapply find_equiv; eauto.
    - eauto.
    - eapply is_syntax_ok_e_binop_elim in Hsyn.
      openhyp.
      rewrite IHe1; eauto.
      rewrite IHe2; eauto.
    - eapply is_syntax_ok_e_test_elim in Hsyn.
      openhyp.
      rewrite IHe1; eauto.
      rewrite IHe2; eauto.
  Qed.
  Arguments eval_equiv st1 st2 [_] _ _.

  Lemma eval_bool_equiv st1 st2 e : st1 === st2 -> is_syntax_ok_e e = true -> eval_bool st1 e = eval_bool st2 e.
  Proof.
    intros Heq Hsyn.
    unfold eval_bool in *.
    rewrite (eval_equiv st1 st2) by eauto; eauto.
  Qed.
  Arguments eval_bool_equiv st1 st2 [_] _ _.

  Lemma is_false_equiv st1 st2 e : is_false st1 e -> st1 === st2 -> is_syntax_ok_e e = true -> is_false st2 e.
  Proof.
    intros H Heq Hsyn.
    unfold is_false in *.
    rewrite (eval_bool_equiv st1 st2) in H by eauto; eauto.
  Qed.

  Lemma is_true_equiv st1 st2 e : is_true st1 e -> st1 === st2 -> is_syntax_ok_e e = true -> is_true st2 e.
  Proof.
    intros H Heq Hsyn.
    unfold is_true in *.
    rewrite (eval_bool_equiv st1 st2) in H by eauto; eauto.
  Qed.

  Lemma no_adt_leak_equiv st1 st2 input avars rvar : no_adt_leak input avars rvar st2 -> st1 === st2 -> no_adt_leak input avars rvar st1.
  Proof.
    intros H Heq.
    unfold no_adt_leak in *.
    intros; eapply H; eauto.
    eapply find_adt_equiv; eauto.
  Qed.

  Lemma add_remove_many_equiv args : forall types output1 output2 st1 st2, st1 === st2 -> List.forallb is_good_varname args = true -> output_eqv types output1 output2 -> length args = length types -> add_remove_many args types output1 st1 === add_remove_many args types output2 st2.
  Proof.
    induction args; destruct types; destruct output1; destruct output2; simpl; try solve [intros; try discriminate; intuition eauto].
    intros st1 st2 Heqv Hgn Hoeqv Hlen.
    inject Hlen.
    rename H into Hlen.
    rename a into k.
    eapply andb_true_iff in Hgn.
    destruct Hgn as [Hgnk Hgn].
    destruct Hoeqv as [Hv Hoeqv].
    destruct v as [w | a].
    - eauto.
    - subst.
      eapply IHargs; eauto.
      destruct o0 as [o|].
      + eapply add_equiv; eauto.
      + eapply remove_equiv; eauto.
  Qed.

  Lemma args_name_ok_make_map avars input : forallb is_good_varname avars = true -> @not_mapsto_adt ADTValue fun_ptr_varname (make_map avars input) = true.
  Proof.
    intros Hgn.
    eapply find_none_not_mapsto_adt.
    eapply not_find_in_iff.
    eapply make_map_not_in.
    intros Hin.
    eapply forallb_forall in Hgn; eauto.
    intuition.
  Qed.

  (* need some clever induction hypothesis strengthening to utilize induction hypothesis generated from the call case of FRunsTo *)
  Arguments no_adt_leak_equiv st1 st2 [_] _ _ _ _ _ _ _.
  Arguments no_adt_leak_equiv st1 st2 [_] _ _ _ _ _ _ _.
  Arguments no_adt_leak_equiv st1 st2 [_] _ _ _ _ _ _ _.
  Arguments no_adt_leak_equiv st1 st2 [_] _ _ _ _ _ _ _.
  Arguments no_adt_leak_equiv st1 st2 [_] _ _ _ _ _ _ _.
  Theorem compile_runsto' t t_env t_st t_st' :
    FRunsTo t_env t t_st t_st' ->
    forall s_env,
      fenv_impls_env t_env s_env ->
      (forall s,
         t = compile s ->
         is_syntax_ok s = true ->
         forall s_st,
           Safe s_env s s_st ->
           s_st === t_st ->
           exists s_st',
             RunsTo s_env s s_st s_st' /\
             s_st' === t_st') /\
      (forall x f args f_w spec input t_callee_st' ret,
         t = Facade.Call x f args ->
         eval t_st f = Some (SCA f_w) ->
         Word2Spec t_env f_w = Some (Facade.Operational (compile_op spec)) ->
         mapM (sel t_st) args = Some input ->
         let body := Body spec in
         let avars := ArgVars spec in
         let retvar := RetVar spec in
         let callee_st := make_map avars input in
         Safe s_env body callee_st ->
         FRunsTo t_env (compile body) callee_st t_callee_st' ->
         sel t_callee_st' retvar = Some ret ->
         no_adt_leak input avars retvar t_callee_st' ->
         let output := List.map (sel t_callee_st') avars in
         t_st' == add x ret (add_remove_many args input output t_st) ->
         exists s_callee_st',
           RunsTo s_env body callee_st s_callee_st' /\
           output_eqv input (List.map (sel s_callee_st') avars) (List.map (sel t_callee_st') avars) /\
           sel s_callee_st' retvar = sel t_callee_st' retvar /\
           no_adt_leak input avars retvar s_callee_st').
  Proof.
    induction 1; simpl; intros s_env Henv; (split; [destruct s; unfold_all; simpl in *; try solve [intros; try discriminate]; intros Hcomp Hsyn s_st Hsf Heqv | try solve [intros; try discriminate]]).
    {
      (* skip *)
      exists s_st; split.
      - eapply RunsToSkip; eauto.
      - eauto.
    }
    {
      (* seq *)
      inject Hcomp.
      inversion Hsf; subst.
      destruct H4 as [Hsf1 Hsf2].
      rename H into Hrt1.
      rename H0 into Hrt2.
      eapply is_syntax_ok_seq_elim in Hsyn.
      destruct Hsyn as [Hsyn1 Hsyn2].
      edestruct IHRunsTo1 as [IHRunsTo1' ?]; eauto.
      edestruct IHRunsTo1' as [s_st' [Hsst' Heq']]; eauto.
      edestruct IHRunsTo2 as [IHRunsTo2' ?]; eauto.
      edestruct IHRunsTo2' as [s_st'' [Hsst'' Heq'']]; eauto.
      exists s_st''; split.
      - eapply RunsToSeq; eauto.
      - eauto.
    }
    {
      (* dfacade - call *)
      inject Hcomp.
      rename s into x.
      rename g into lbl.
      rename l into args.
      rename H into Hrtlbl.
      rename H0 into Hrtcall.
      inversion Hrtlbl; subst.
      rename H1 into Hlw.
      rename H2 into Hnadt.
      rename H5 into Hst'.
      copy_as Hst' Hst'2.
      eapply equiv_intro in Hst'; eauto.
      assert (Heqv' : st' === s_st).
      {
        etransitivity; eauto; symmetry; eauto.
      }
      eapply is_syntax_ok_call_elim in Hsyn.
      destruct Hsyn as [Hsynx [Hsynargs Hargsnd]].
      inversion Hrtcall; unfold_all; subst.
      {
        (* axiomatic *)
        rename H3 into Hfw.
        rename H4 into Hspec.
        rename H5 into Hmm.
        rename H6 into Hnadt2.
        rename H7 into Hpre.
        rename H8 into Hlen.
        rename H11 into Hpost.
        rename H12 into Hst''.
        simpl in *.
        rewrite Hst'2 in Hfw.
        rewrite add_eq_o in Hfw by eauto.
        inject Hfw.
        inversion Hsf; subst.
        {
          rename H3 into Hflbl.
          rename H4 into Hmm'.
          rename H6 into Hxnadt.
          rename H7 into Hpre'.
          copy_as Hflbl Hflbl'; eapply Henv in Hflbl.
          destruct Hflbl as [f_w' [Hfw' Hspec']]; simpl in *.
          unif f_w'.
          unif (Facade.Axiomatic spec0).
          rewrite (mapM_find_equiv st' s_st) in Hmm by eauto.
          unif input0.
          exists (add x ret (add_remove_many args input (wrap_output output) s_st)).
          split.
          {
            eapply RunsToCallAx; eauto.
          }
          {
            rewrite Hst''.
            eapply add_equiv; eauto.
            copy_as Hmm Hmm'; eapply mapM_length in Hmm'.
            eapply add_remove_many_equiv; eauto.
            - symmetry; eauto.
            - eapply output_eqv_refl.
              unfold wrap_output.
              rewrite map_length.
              congruence.
          }
        }
        {
          rename H3 into Hflbl.
          copy_as Hflbl Hflbl'; eapply Henv in Hflbl.
          destruct Hflbl as [f_w' [Hfw' Hspec']]; simpl in *.
          unif f_w'.
          rewrite Hspec' in Hspec; discriminate.
        }
      }
      {
        (* operational *)
        rename H3 into Hfw.
        rename H4 into Hspec.
        rename H5 into Hlen.
        rename H6 into Hmm.
        rename H7 into Hnadt2.
        rename H8 into Hrtb.
        rename H9 into Hret.
        rename H12 into Hnleak.
        rename H13 into Hst''.
        simpl in *.
        rewrite Hst'2 in Hfw.
        rewrite add_eq_o in Hfw by eauto.
        inject Hfw.
        inversion Hsf; unfold_all; subst.
        {
          rename H3 into Hflbl.
          copy_as Hflbl Hflbl'; eapply Henv in Hflbl.
          destruct Hflbl as [f_w' [Hfw' Hspec']]; simpl in *.
          unif f_w'.
          rewrite Hspec' in Hspec; discriminate.
        }
        {
          rename H3 into Hflbl.
          rename H4 into Hlen'.
          rename H5 into Hmm'.
          rename H6 into Hnadt'.
          rename H8 into Hsfb.
          rename H9 into Hbodyok.
          copy_as Hflbl Hflbl'; eapply Henv in Hflbl.
          destruct Hflbl as [f_w' [Hfw' Hspec']]; simpl in *.
          unif f_w'.
          unif (@Facade.Operational ADTValue spec).
          destruct spec0; simpl in *.
          copy_as Hmm Hmm'2.
          rewrite (mapM_find_equiv st' s_st) in Hmm by eauto.
          unif input0.
          edestruct IHRunsTo2 as [trash IHRunsTo2']; eauto.
          edestruct IHRunsTo2' as [s_callee_st' Hscst']; eauto; simpl in *.
          {
            simpl in *.
            rewrite Hst'2.
            rewrite add_eq_o by eauto.
            eauto.
          }
          destruct Hscst' as [Hrtbs [Hmcst [Hcstr Hnadts]]].
          exists (add x ret (add_remove_many args input (List.map (sel s_callee_st') ArgVars) s_st)).
          split.
          {
            eapply RunsToCallOp; eauto.
            simpl.
            congruence.
          }
          {
            rewrite Hst''.
            eapply add_equiv; eauto.
            eapply add_remove_many_equiv; eauto.
            - symmetry; eauto.
            - eapply mapM_length; eauto.
          }
        }
      }
    }
    {
      (* if-true *)
      inject Hcomp.
      eapply is_syntax_ok_if_elim in Hsyn.
      destruct Hsyn as [Hsyne [Hsyn1 Hsyn2]].
      inversion Hsf; subst; rename H5 into He; rename H6 into Hsfbr.
      - edestruct IHRunsTo as [IHRunsTo' ?]; eauto.
        edestruct IHRunsTo' as [s_st' [Hsst' Heq']]; eauto.
        exists s_st'; split.
        + eapply RunsToIfTrue; eauto.
        + eauto.
      - eapply is_false_equiv in He; eauto.
        exfalso; eapply is_true_is_false; eauto.
    }
    {
      (* if-false *)
      inject Hcomp.
      eapply is_syntax_ok_if_elim in Hsyn.
      destruct Hsyn as [Hsyne [Hsyn1 Hsyn2]].
      inversion Hsf; subst; rename H5 into He; rename H6 into Hsfbr.
      - eapply is_true_equiv in He; eauto.
        exfalso; eapply is_true_is_false; eauto.
      - edestruct IHRunsTo as [IHRunsTo' ?]; eauto.
        edestruct IHRunsTo' as [s_st' [Hsst' Heq']]; eauto.
        exists s_st'; split.
        + eapply RunsToIfFalse; eauto.
        + eauto.
    }
    {
      (* while-true *)
      inject Hcomp.
      copy_as Hsyn Hsyn'.
      eapply is_syntax_ok_while_elim in Hsyn.
      destruct Hsyn as [Hsyne Hsynb].
      inversion Hsf; unfold_all; subst.
      - edestruct IHRunsTo1 as [IHRunsTo1' ?]; eauto.
        edestruct IHRunsTo1' as [s_st' [Hsst' Heq']]; eauto.
        edestruct IHRunsTo2 as [IHRunsTo2' ?]; eauto.
        edestruct (IHRunsTo2' (While e s)) as [s_st'' [Hsst'' Heq'']]; try eapply Heq'; eauto.
        exists s_st''; split.
        + eapply RunsToWhileTrue; eauto.
        + eauto.
      - rename H5 into He.
        eapply is_false_equiv in He; eauto.
        exfalso; eapply is_true_is_false; eauto.
    }
    {
      (* while-false *)
      inject Hcomp.
      eapply is_syntax_ok_while_elim in Hsyn.
      destruct Hsyn as [Hsyne Hsynb].
      inversion Hsf; unfold_all; subst.
      - rename H2 into He.
        eapply is_true_equiv in He; eauto.
        exfalso; eapply is_true_is_false; eauto.
      - exists s_st; split.
        + eapply RunsToWhileFalse; eauto.
        + eauto.
    }
    {
      (* assign *)
      inject Hcomp.
      rename s into x.
      rename H into He.
      rename H0 into Hnadt.
      rename H1 into Hst'.
      eapply is_syntax_ok_assign_elim in Hsyn.
      destruct Hsyn as [Hsynx Hsyne].
      erewrite <- eval_equiv in He by eauto.
      erewrite <- not_mapsto_adt_equiv in Hnadt by eauto.
      exists (add x (SCA w) s_st); split.
      - eapply RunsToAssign; eauto.
      - rewrite Hst'.
        eapply add_equiv; eauto.
    }
    {
      (* facade call - axiomatic *)
      unfold_all.
      intros x' f' args' f_w' spec' input' t_callee_st' ret' Heq Hfw Hspec Hmm Hsfb Hrtb Hret Hnadt Hst''2.
      inject Heq.
      unif (@SCA ADTValue f_w').
      rename H1 into Hspec'.
      rewrite Hspec' in Hspec.
      discriminate.
    }
    {
      (* facade call - operation *)
      unfold_all.
      intros x' f' args' f_w' spec' input' t_callee_st' ret' Heq Hfw Hspec Hmm Hsfb Hrtb Hret' Hnadt Hst''2.
      inject Heq.
      unif (@SCA ADTValue f_w').
      rename H1 into Hspec'.
      rewrite Hspec in Hspec'.
      rename H6 into Hret.
      inject Hspec'.
      unif input'.
      destruct spec'; simpl in *.
      edestruct IHRunsTo as [IHRunsTo' trash]; eauto.
      edestruct IHRunsTo' as [s_callee_st' [Hstb Hscst']]; eauto.
      {
        eapply equiv_refl.
        eapply args_name_ok_make_map; eauto.
      }
      rename H8 into Hst''.
      rewrite Hst'' in Hst''2.
      eapply add_add_remove_many_eq_elim in Hst''2; eauto; try (rewrite map_length; eauto).
      destruct Hst''2 as [Hreteq Houteq].
      exists s_callee_st'.
      repeat try_split; eauto.
      {
        rewrite (map_find_equiv s_callee_st' callee_st') by eauto.
        eauto.
      }
      {
        unfold sel in *.
        rewrite (find_equiv s_callee_st' callee_st') by eauto.
        rewrite Hret.
        rewrite Hret'.
        rewrite Hreteq.
        eauto.
      }
      {
        Arguments no_adt_leak_equiv st1 st2 [_] _ _ _ _ _ _ _.
        eapply (no_adt_leak_equiv _ callee_st'); eauto.
      }
    }
  Qed.

  Theorem compile_runsto t t_env t_st t_st' :
    FRunsTo t_env t t_st t_st' ->
    forall s_env,
      fenv_impls_env t_env s_env ->
      (forall s,
         t = compile s ->
         is_syntax_ok s = true ->
         forall s_st,
           Safe s_env s s_st ->
           s_st === t_st ->
           exists s_st',
             RunsTo s_env s s_st s_st' /\
             s_st' === t_st').
  Proof.
    intros; eapply compile_runsto'; eauto.
  Qed.

  Require Import Bedrock.Platform.Facade.SafeCoind.

  Theorem compile_safe s_env s s_st :
    Safe s_env s s_st ->
    is_syntax_ok s = true ->
    forall t_env t_st,
      fenv_impls_env t_env s_env ->
      s_st === t_st ->
      let t := compile s in
      FSafe t_env t t_st.
  Proof.
    simpl; intros Hsfs Hsyn t_env t_st Henv Heqv.
    eapply
      (Safe_coind
         (fun t t_st =>
            exists s s_st,
              Safe s_env s s_st /\
              is_syntax_ok s = true /\
              s_st === t_st /\
              (t = compile s \/
               exists x lbl args,
                 s = Call x lbl args /\
                 (t = Facade.Label fun_ptr_varname lbl \/
                  (t = Facade.Call x (Var fun_ptr_varname) args /\
                   exists f_w, Label2Word t_env lbl = Some f_w /\ find fun_ptr_varname t_st = Some (SCA f_w)))))
      ); [ .. | solve [repeat try_eexists; simpl in *; intuition eauto] ]; generalize Henv; clear; simpl; intros Henv; intros until st; rename st into t_st; intros [s [s_st [Hsfs [Hsyn [Heqv Ht]]]]]; destruct s; simpl in *; destruct Ht as [Ht | [x' [lbl' [arg' [Hs [Ht | [Ht [f_w' [Hlblfw' Hfpvfw']]]]]]]]]; try discriminate; inject Ht.

    Focus 7.
    {
      (* call *)
      symmetry in Hs; inject Hs.
      rename s into x.
      rename g into lbl.
      rename l into args.
      eapply is_syntax_ok_call_elim in Hsyn.
      destruct Hsyn as [Hsynx [Hsynargs Hsynnd]].
      split.
      {
        eapply is_no_dup_sound; eauto.
      }
      inversion Hsfs; unfold_all; subst.
      {
        (* axiomatic *)
        rename H2 into Hflbl.
        rename H3 into Hmm.
        rename H5 into Hnadt.
        rename H6 into Hpre.
        split.
        {
          erewrite <- not_mapsto_adt_equiv; eauto.
        }
        eapply Henv in Hflbl.
        destruct Hflbl as [f_w [Hlblw Hwspec]]; simpl in *.
        unif f_w'.
        exists f_w, input.
        repeat try_split.
        {
          eauto.
        }
        {
          rewrite (mapM_find_equiv s_st t_st) in Hmm by eauto.
          eauto.
        }
        left.
        exists spec.
        split; eauto.
      }
      (* opereational *)
      {
        rename H2 into Hflbl.
        rename H3 into Hlen.
        rename H4 into Hmm.
        rename H5 into Hnadt.
        rename H7 into Hsfsb.
        rename H8 into Hsb.
        split.
        {
          erewrite <- not_mapsto_adt_equiv; eauto.
        }
        eapply Henv in Hflbl.
        destruct Hflbl as [f_w [Hlblw Hwspec]]; simpl in *.
        unif f_w'.
        exists f_w, input.
        repeat try_split.
        {
          eauto.
        }
        {
          rewrite (mapM_find_equiv s_st t_st) in Hmm by eauto.
          eauto.
        }
        right.
        exists (compile_op spec).
        destruct spec; simpl in *.
        repeat try_split; eauto.
        {
          exists Body, (make_map ArgVars input).
          repeat try_split; eauto.
          eapply equiv_refl.
          eapply args_name_ok_make_map; eauto.
        }
        intros callee_st' Hrttb.
        eapply compile_runsto in Hrttb; eauto.
        destruct Hrttb as [callee_st'2 [Hrtsb Heqv']].
        eapply Hsb in Hrtsb.
        destruct Hrtsb as [Hrv Hnleak].
        split.
        {
          unfold sel in *.
          rewrite <- (find_equiv callee_st'2 callee_st') by eauto.
          eauto.
        }
        {
          eapply (no_adt_leak_equiv); eauto.
          symmetry; eauto.
        }
        eapply equiv_refl.
        eapply args_name_ok_make_map; eauto.
      }
    }
    Unfocus.

    {
      (* seq *)
      inversion Hsfs; subst.
      eapply is_syntax_ok_seq_elim in Hsyn.
      destruct Hsyn as [Hsyn1 Hsyn2].
      destruct H2 as [Hsfa Hsfb].
      split.
      - exists s1, s_st; eauto.
      - intros t_st' Hrtt; simpl in *.
        eapply compile_runsto in Hrtt; eauto.
        openhyp.
        repeat eexists_split; try eapply Hsfb; eauto.
    }

    {
      (* dfacade call *)
      rename s into x.
      rename g into f.
      rename l into args.
      copy_as Hsyn Hsyn'.
      eapply is_syntax_ok_call_elim in Hsyn.
      destruct Hsyn as [Hsynx Hsynargs].
      inversion Hsfs; subst.
      {
        (* axiomatic *)
        rename H2 into Hflbl.
        rename H3 into Hmm.
        rename H5 into Hnadt.
        rename H6 into Hpre.
        split.
        {
          exists (Call x f args), s_st.
          repeat try_split; eauto.
          right.
          exists x, f, args.
          repeat try_split; eauto.
        }
        intros t_st' Hrtt.
        eapply Henv in Hflbl.
        destruct Hflbl as [f_w [Hlblw Hwspec]]; simpl in *.
        inversion Hrtt; subst.
        unif w.
        rename H2 into Hnadt'.
        rename H5 into Hst'.
        exists (Call x f args), s_st.
        repeat try_split; eauto.
        {
          copy_as Hst' Hst'2.
          eapply equiv_intro in Hst'; eauto.
          etransitivity; eauto; symmetry; eauto.
        }
        right.
        exists x, f, args.
        repeat try_split; eauto.
        right.
        repeat try_split; eauto.
        exists f_w.
        repeat try_split; eauto.
        rewrite Hst'.
        rewrite add_eq_o by eauto; eauto.
      }
      {
        (* operational *)
        rename H2 into Hflbl.
        rename H3 into Hlen.
        rename H4 into Hmm.
        rename H5 into Hnadt.
        rename H7 into Hsfsb.
        rename H8 into Hsb.
        split.
        {
          exists (Call x f args), s_st.
          repeat try_split; eauto.
          right.
          exists x, f, args.
          repeat try_split; eauto.
        }
        intros t_st' Hrtt.
        eapply Henv in Hflbl.
        destruct Hflbl as [f_w [Hlblw Hwspec]]; simpl in *.
        inversion Hrtt; subst.
        unif w.
        rename H2 into Hnadt'.
        rename H5 into Hst'.
        exists (Call x f args), s_st.
        repeat try_split; eauto.
        {
          copy_as Hst' Hst'2.
          eapply equiv_intro in Hst'; eauto.
          etransitivity; eauto; symmetry; eauto.
        }
        right.
        exists x, f, args.
        repeat try_split; eauto.
        right.
        repeat try_split; eauto.
        exists f_w.
        repeat try_split; eauto.
        rewrite Hst'.
        rewrite add_eq_o by eauto; eauto.
      }
    }

    {
      (* if *)
      eapply is_syntax_ok_if_elim in Hsyn.
      destruct Hsyn as [Hsyne [Hsyn1 Hsyn2]].
      inversion Hsfs; subst.
      - left.
        rename H3 into Hcond.
        rename H4 into Hsfbr.
        split.
        + eapply is_true_equiv; eauto.
        + repeat eexists_split; eauto.
      - right.
        rename H3 into Hcond.
        rename H4 into Hsfbr.
        split.
        + eapply is_false_equiv; eauto.
        + repeat eexists_split; eauto.
    }

    {
      (* while *)
      copy_as Hsyn Hysn'.
      eapply is_syntax_ok_while_elim in Hsyn.
      destruct Hsyn as [Hsyne Hsynb].
      inversion Hsfs; unfold_all; subst.
      - left.
        rename H1 into Hcond.
        rename H2 into Hsfbody.
        rename H4 into Hsfk.
        repeat try_split.
        + eapply is_true_equiv; eauto.
        + repeat eexists_split; eauto.
        + intros t_st' Hrtt; simpl in *.
          eapply compile_runsto in Hrtt; eauto.
          openhyp.
          exists (While e s).
          repeat eexists_split; try eapply Hsfk; eauto.
      - right.
        eapply is_false_equiv; eauto.
    }

    {
      (* assign *)
      eapply is_syntax_ok_assign_elim in Hsyn.
      destruct Hsyn as [Hsynx Hsyne].
      inversion Hsfs; unfold_all; subst.
      split.
      - erewrite <- not_mapsto_adt_equiv; eauto.
      - eexists.
        erewrite <- eval_equiv; eauto.
    }

    {
      (* label *)
      symmetry in Hs; inject Hs.
      rename s into x.
      rename g into lbl.
      rename l into args.
      split.
      - eapply equiv_nma_fpv; eauto.
      - inversion Hsfs; unfold_all; subst.
        + rename H2 into Hflbl.
          eapply Henv in Hflbl.
          openhyp; eexists; eauto.
        + rename H2 into Hflbl.
          eapply Henv in Hflbl.
          openhyp; eexists; eauto.
    }

  Qed.

End ADTValue.
