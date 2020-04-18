Set Implicit Arguments.

Require Import Bedrock.Platform.Facade.CompileSafe.
Require Import Bedrock.Platform.Facade.CompileRunsTo.
Require Import Bedrock.Platform.Facade.CompileDFacadeCorrect.

Section ADTValue.

  Variable ADTValue : Type.

  Require Import Bedrock.Platform.Facade.DFacade.

  Notation State := (@State ADTValue).
  Notation Env := (@Env ADTValue).
  Notation Value := (@Value ADTValue).
  Notation FuncSpec := (@FuncSpec ADTValue).
  Notation RunsTo := (@RunsTo ADTValue).
  Notation Safe := (@Safe ADTValue).

  Require Import Bedrock.Memory.
  Require Import Bedrock.Platform.Cito.GLabel.

  Notation CState := (@Semantics.State ADTValue).
  Notation CCallee := (@Semantics.Callee ADTValue).
  Notation CInternal := (@Semantics.Internal ADTValue).
  Notation CRunsTo := (@Semantics.RunsTo ADTValue).
  Notation CEnv := ((glabel -> option W) * (W -> option CCallee))%type.

  Notation FEnv := (@Facade.Env ADTValue).

  Require Import Bedrock.Platform.Cito.GLabelMap.

  Notation compile s := (Compile.compile (compile s)).

  Notation compile_spec s := (CompileRunsTo.compile_spec (@CompileDFacadeCorrect.compile_spec ADTValue s)).

  Require Import Bedrock.Platform.Cito.Label2Word Bedrock.Platform.Cito.Label2WordFacts.

  Require Import Bedrock.Platform.Cito.GLabelMap.
  Import GLabelMap.
  Require Import Bedrock.Platform.Cito.GLabelMapFacts.
  Import FMapNotations.
  Local Open Scope fmap_scope.

  Definition cenv_impls_env (cenv : CEnv) (env : Env) :=
    (forall lbl spec,
      GLabelMap.find lbl env = Some spec ->
      exists w,
        fst cenv lbl = Some w /\
        snd cenv w = Some (compile_spec spec)) /\
    stn_injective (fun k => In k env) (fst cenv).

  Require Import Bedrock.StringSet.

  Require Import Bedrock.Platform.Cito.Option.

  Require Import Bedrock.Platform.Cito.GeneralTactics.
  Require Import Bedrock.Platform.Cito.GeneralTactics3.
  Require Import Bedrock.Platform.Cito.GeneralTactics4.
  Require Import Bedrock.Platform.Cito.GeneralTactics5.

  Lemma cenv_impls_env_fenv cenv env : cenv_impls_env cenv env -> exists fenv, CompileRunsTo.cenv_impls_env cenv fenv /\ fenv_impls_env fenv env.
  Proof.
    intros [H Hinj].
    set (fenv :=
           {|
             Label2Word := fst cenv;
             Word2Spec w := option_map (@CompileDFacadeCorrect.compile_spec _) (find_by_word (fst cenv) (elements env) w)
           |} : FEnv).
    unfold cenv_impls_env in *.
    unfold CompileRunsTo.cenv_impls_env in *.
    unfold fenv_impls_env in *.
    exists fenv.
    unfold_all; simpl in *.
    split.
    {
      split.
      {
        eauto.
      }
      {
        intros w fspec Hfw.
        eapply option_map_some_elim in Hfw.
        destruct Hfw as [spec [Hfw ?]].
        subst.
        eapply find_by_word_elements_elim in Hfw.
        destruct Hfw as [lbl [Hflbl Hlblw]].
        eapply H in Hflbl.
        destruct Hflbl as [w' [Hlblw' Hw'spec]].
        unif w'.
        eauto.
      }
    }
    {
      intros lbl spec Hflbl.
      copy_as Hflbl Hflbl'.
      eapply H in Hflbl.
      destruct Hflbl as [w [Hlblw Hwspec]].
      exists w.
      split; eauto.
      eapply option_map_some_intro; eauto.
      eapply find_by_word_elements_intro; eauto.
    }
  Qed.

  Require Import Bedrock.Platform.Cito.StringMap.
  Import StringMap.
  Require Import Bedrock.Platform.Cito.StringMapFacts.
  Import FMapNotations.
  Local Open Scope fmap_scope.

  Notation equivf := (equiv (StringSet.singleton fun_ptr_varname)).
  Infix "===" := equivf (at level 70).

  Require Import Coq.Strings.String.

  Require Import Bedrock.Platform.Facade.NameDecoration.
  Require Import Bedrock.Platform.Facade.FacadeFacts Bedrock.Platform.Facade.DFacadeFacts.

  Existing Instance equiv_rel_Symmetric.
  Existing Instance equiv_rel_Transitive.

  Lemma equiv_related (st st' : State) cst : related st cst -> st' === st -> find fun_ptr_varname st' = None -> related st' cst.
  Proof.
    intros Hr Heqv Hfpv.
    unfold related.
    split.
    {
      intros k v Hfk.
      destruct (string_dec k fun_ptr_varname) as [Heqk | Hnek].
      {
        subst.
        rewrite Hfk in Hfpv; discriminate.
      }
      erewrite find_equiv_fpv in Hfk; eauto.
      eapply Hr in Hfk.
      eauto.
    }
    intros p a Hpa.
    eapply Hr in Hpa.
    destruct Hpa as [x [[Hxp Hxa] Huni]].
    destruct (string_dec x fun_ptr_varname) as [Heqx | Hnex].
    {
      subst.
      contradict Hxa.
      eapply not_find_fpv_adt; eauto.
    }
    exists x.
    split.
    {
      split; eauto.
      erewrite find_equiv_fpv; eauto.
    }
    intros x' [Hx'p Hx'a].
    destruct (string_dec x' fun_ptr_varname) as [Heqx' | Hnex'].
    {
      subst.
      contradict Hx'a.
      symmetry in Heqv.
      eapply not_find_fpv_adt; eauto.
    }
    erewrite find_equiv_fpv in Hx'a; eauto.
  Qed.

  Require Import Bedrock.Platform.Cito.StringSetFacts.
  Import StringSet.
  Require Import Bedrock.Platform.Cito.WordMap.
  Import WordMap.
  Require Import Bedrock.Platform.Cito.WordMapFacts.
  Import FMapNotations.
  Local Open Scope fmap_scope.

  Theorem compile_runsto t t_env t_st t_st' :
    CRunsTo t_env t t_st t_st' ->
    forall s,
      t = compile s ->
      is_syntax_ok s = true ->
      (* h1 : the heap portion that this program is allowed to change *)
      forall h1,
        h1 <= snd t_st ->
        forall s_st,
          related s_st (fst t_st, h1) ->
          StringMap.find fun_ptr_varname s_st = None ->
          forall s_env,
            cenv_impls_env t_env s_env ->
            Safe s_env s s_st ->
            exists s_st',
              RunsTo s_env s s_st s_st' /\
              (* h2 : the frame heap (the outside portion that won't be touched by this program *)
              let h2 := snd t_st - h1 in
              (* the frame heap will be intacked in the final state *)
              h2 <= snd t_st' /\
              (* variables not appearing as LHS won't change value in Cito state *)
              (forall x, ~ StringSet.In x (assigned s) -> is_good_varname x = true -> Locals.sel (fst t_st) x = Locals.sel (fst t_st') x) /\
              (* main result: final source-level and target level states are related *)
              related s_st' (fst t_st', snd t_st' - h2).
  Proof.
    intros Hcrt s Hcomp Hsyn h1 Hsm s_st Hr Hnotmp s_env Henv Hsf.
    eapply cenv_impls_env_fenv in Henv.
    destruct Henv as [fenv [Htenv Hfenv]].
    eapply CompileRunsTo.compile_runsto in Hcrt; eauto.
    - destruct Hcrt as [s_st' [Hfrt Hsst']]; simpl in *.
      destruct Hsst' as [Hsm' [Hnoass [Hnocollide Hr']]].
      eapply CompileDFacadeCorrect.compile_runsto in Hfrt; eauto.
      + destruct Hfrt as [d_st' [Hdrt Heqv]].
        exists d_st'.
        repeat try_split.
        * eauto.
        * eauto.
        * intros x Hnin Hgvar.
          eapply Hnoass.
          intros Hin.
          contradict Hnin.
          eapply compile_assigned in Hin; trivial.
        * eapply equiv_related; eauto.
          eapply not_free_vars_no_change in Hdrt; eauto.
          erewrite Hdrt; eauto.
          eapply syntax_ok_fptr_not_fv; eauto.
      + eapply equiv_refl; eauto.
        eapply find_none_not_mapsto_adt; eauto.
    - eapply CompileDFacadeCorrect.compile_safe; eauto.
      eapply equiv_refl; eauto.
      eapply find_none_not_mapsto_adt; eauto.
  Qed.

  Notation CSafe := (@Semantics.Safe ADTValue).

  Theorem compile_safe s_env s s_st :
  Safe s_env s s_st ->
  is_syntax_ok s = true ->
  StringMap.find fun_ptr_varname s_st = None ->
  (* h1 : the heap portion that this program is allowed to change *)
  forall vs h h1,
    h1 <= h ->
    related s_st (vs, h1) ->
    forall t_env t t_st,
      cenv_impls_env t_env s_env ->
      t = compile s ->
      t_st = (vs, h) ->
      CSafe t_env t t_st.
  Proof.
    simpl; intros Hsfs Hsyn Hsstok vs h h1 Hsm Hr t_env t t_st Henv Ht Htst.
    subst.
    eapply cenv_impls_env_fenv in Henv.
    destruct Henv as [fenv [Htenv Hfenv]].
    eapply CompileSafe.compile_safe; eauto.
    eapply CompileDFacadeCorrect.compile_safe; eauto.
    eapply equiv_refl.
    eapply find_none_not_mapsto_adt; eauto.
  Qed.

End ADTValue.
