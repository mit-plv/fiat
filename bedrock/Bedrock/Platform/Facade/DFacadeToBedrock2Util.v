Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.ADT.

Section ADTValue.

  Variable ADTValue : Type.

  Require Import Bedrock.Platform.Cito.StringMap Bedrock.Platform.Cito.WordMap Bedrock.Platform.Cito.GLabelMap.

  Require Import AxSpec.
  Notation AxiomaticSpec := (@AxiomaticSpec ADTValue).
  Require Import Bedrock.Platform.Facade.DFModule.
  Require Import Bedrock.Platform.Cito.StringMapFacts.
  Require Import Bedrock.Platform.Cito.ListFacts3.
  Variable module : DFModule ADTValue.
  Notation imports := (Imports module).
  Require Import String.
  (* the name of the module that contains operational export specs *)
  Variable op_mod_name : string.
  Require Import Bedrock.Platform.Facade.NameDecoration.
  Require Import Bedrock.Platform.Cito.NameDecoration.
  Hypothesis op_mod_name_ok : is_good_module_name op_mod_name = true.
  Notation Value := (@Value ADTValue).
  Require Import Bedrock.Platform.Facade.DFacade.
  Require Import Bedrock.Platform.Facade.CompileDFModule.
  Require Import Bedrock.Platform.Facade.NameDecoration.
  Definition good_module := compile_to_gmodule module op_mod_name op_mod_name_ok.
  Require Import List.
  Definition gmodules := good_module :: nil.

  Require Import Bedrock.Platform.Cito.StringMap.
  Import StringMap.
  Require Import Bedrock.Platform.Cito.StringMapFacts.
  Import FMapNotations.
  Local Open Scope fmap_scope.
  Require Import Bedrock.Platform.Facade.Listy.
  Import Notations Instances.
  Local Open Scope listy_scope.

  Require Import Bedrock.Platform.Cito.GoodModuleDec.
  Require Import Bedrock.Platform.Cito.GoodModuleDecFacts.
  Require Import Bedrock.Platform.Cito.Semantics.
  Require Import Bedrock.Platform.Facade.CompileDFacadeToCito.
  Import WordMapFacts.FMapNotations.
  Local Open Scope fmap_scope.

  Require Import ConvertLabel.
  Require Import LinkSpec.

  Lemma env_good_to_use_cenv_impls_env gmodules stn fs : env_good_to_use gmodules imports stn fs -> cenv_impls_env (from_bedrock_label_map (Labels stn), fs stn) (GLabelMap.map (@Axiomatic _) imports).
  Proof.
    intros Hgu.
    unfold env_good_to_use, cenv_impls_env in *.
    destruct Hgu as [Hsgu [Hinj Hfsgu] ].
    unfold stn_good_to_use, fs_good_to_use in *.
    split.
    {
      intros lbl spec Hflbl.
      Require Import Bedrock.Platform.Cito.GLabelMapFacts.
      rewrite map_o in Hflbl.
      Require Import Bedrock.Platform.Cito.Option.
      eapply option_map_some_elim in Hflbl.
      destruct Hflbl as [aspec [Hflbl' ?] ].
      subst.
      simpl in *.
      assert (Hlblin : label_in gmodules imports lbl).
      {
        unfold label_in.
        right; eauto.
        eapply find_Some_in; eauto.
      }
      eapply Hsgu in Hlblin.
      eapply ex_up in Hlblin.
      destruct Hlblin as [w Hw].
      assert (fs stn w = Some (Foreign aspec)).
      {
        eapply Hfsgu.
        exists lbl.
        split; eauto.
        unfold label_mapsto.
        right.
        exists aspec.
        split; eauto.
      }
      exists w.
      split; eauto.
    }
    intros k.
    intros k' w Hin1 Hin2 Hf1 Hf2.
    simpl in *.
    eapply in_find_Some in Hin1.
    destruct Hin1 as [s1 Hs1].
    rewrite map_o in Hs1.
    eapply option_map_some_elim in Hs1.
    destruct Hs1 as [as1 [Has1 ?] ].
    subst; simpl in *.
    eapply in_find_Some in Hin2.
    destruct Hin2 as [s2 Hs2].
    rewrite map_o in Hs2.
    eapply option_map_some_elim in Hs2.
    destruct Hs2 as [as2 [Has2 ?] ].
    subst; simpl in *.
    eapply Hinj; eauto.
    {
      unfold label_in.
      right; eauto.
      eapply find_Some_in; eauto.
    }
    {
      unfold label_in.
      right; eauto.
      eapply find_Some_in; eauto.
    }
  Qed.

  Require Import Bedrock.Platform.Facade.CompileRunsTo.
  Lemma empty_related vs : @CompileRunsTo.related ADTValue (StringMap.empty _) (vs, (WordMap.empty _)).
  Proof.
    unfold related.
    split.
    {
      intros x v Hf.
      Require Import Bedrock.Platform.Cito.StringMapFacts.
      rewrite empty_o in Hf.
      discriminate.
    }
    intros p a Hf.
    simpl in *.
    rewrite WordMapFacts.empty_o in Hf.
    discriminate.
  Qed.

  Import StringMapFacts.FMapNotations.

  Lemma related_Equal st1 st2 vs1 vs2 h1 h2 : @related ADTValue st1 (vs1, h1) -> st2 == st1 -> (forall k, vs2 k = vs1 k) -> WordMap.Equal h2 h1 -> related st2 (vs2, h2).
  Proof.
    intros Hr Heq Hvs Hh.
    unfold related in *; simpl in *.
    split.
    {
      intros x v Hf.
      rewrite Heq in Hf.
      rewrite Hh.
      rewrite Hvs.
      eapply Hr in Hf.
      eauto.
    }
    intros p a Hf.
    rewrite Hh in Hf.
    eapply Hr in Hf.
    destruct Hf as [x [Hex Huni] ].
    rewrite <- Heq in Hex.
    rewrite <- Hvs in Hex.
    exists x.
    split.
    - eauto.
    - intros x' Hx'.
      rewrite Heq in Hx'.
      rewrite Hvs in Hx'.
      eauto.
  Qed.

  Require Import Coq.Setoids.Setoid.
  Global Add Morphism (@CompileRunsTo.related ADTValue) with signature StringMap.Equal ==> Logic.eq ==> iff as related_Equal_m.
  Proof.
    intros st1 st2 Heq cst.
    destruct cst as [vs h] in *.
    split; intros.
    eapply related_Equal; eauto.
    symmetry; eauto.
    reflexivity.
    eapply related_Equal; eauto.
    reflexivity.
  Qed.

  Import WordMapFacts.FMapNotations.

  Require Import Bedrock.Platform.Cito.StringMapFacts.

  Require Import Bedrock.Platform.Cito.GeneralTactics4.
  Arguments empty {_}.

  Require Import Bedrock.Platform.Cito.SemanticsUtil.
  Require Import Bedrock.Platform.Cito.SemanticsFacts9.

  Arguments store_pair {_} _ _.

  Import StringMapFacts StringMap.StringMap.

  Lemma related_add_adt st vs h x (a : ADTValue) w : related st (vs, h) -> w = vs x -> ~ WordMap.In w h -> not_mapsto_adt x st = true -> related (add x (ADT a) st) (vs, WordMap.add w a h).
    intros Hr ? Hninw Hninx.
    subst.

    unfold related in *; simpl in *.
    split.
    {
      intros x' v' Hf.
      destruct (string_dec x' x) as [Heq | Hne].
      {
        subst.
        rewrite add_eq_o in Hf by eauto.
        inject Hf.
        simpl in *.
        rewrite WordMapFacts.add_eq_o by eauto.
        eauto.
      }
      rewrite add_neq_o in Hf by eauto.
      eapply Hr in Hf.
      destruct v' as [w' | a']; simpl in *.
      {
        eauto.
      }
      unfold Locals.sel in *.
      destruct (weq (vs x') (vs x)) as [Heqw | Hnew].
      {
        rewrite Heqw in *.
        contradict Hninw.
        eapply WordMapFacts.find_Some_in; eauto.
      }
      rewrite WordMapFacts.add_neq_o by eauto.
      eauto.
    }
    intros p a' Hf.
    destruct (weq p (vs x)) as [? | Hne].
    {
      subst.
      rewrite WordMapFacts.add_eq_o in Hf by eauto.
      inject Hf.
      exists x.
      split.
      {
        split.
        - eauto.
        - rewrite add_eq_o by eauto.
          eauto.
      }
      intros x' [Hvsx' Hfx'].
      destruct (string_dec x' x) as [? | Hne].
      {
        eauto.
      }
      rewrite add_neq_o in Hfx' by eauto.
      eapply Hr in Hfx'.
      simpl in *.
      unfold Locals.sel in *.
      rewrite Hvsx' in *.
      contradict Hninw.
      eapply WordMapFacts.find_Some_in; eauto.
    }
    rewrite WordMapFacts.add_neq_o in Hf by eauto.
    eapply Hr in Hf.
    destruct Hf as [x' [ [Hvsx' Hfx'] Huni] ].
    exists x'.
    split.
    {
      split; eauto.
      destruct (string_dec x' x) as [? | Hnex].
      {
        subst.
        eapply not_mapsto_adt_iff in Hninx.
        contradict Hninx.
        eexists; eauto.
      }
      rewrite add_neq_o by eauto.
      eauto.
    }
    intros x'' [Hvsx'' Hfx''].
    subst.
    unfold Locals.sel in *.
    destruct (string_dec x'' x) as [? | Hnex''].
    {
      subst.
      rewrite add_eq_o in Hfx'' by eauto.
      inject Hfx''.
      eapply Hr in Hfx'.
      simpl in *.
      rewrite Hvsx'' in *.
      contradict Hninw.
      eapply WordMapFacts.find_Some_in; eauto.
    }
    rewrite add_neq_o in Hfx'' by eauto.
    eapply Huni; eauto.
  Qed.

  Lemma related_add st vs h x v w : @related ADTValue st (vs, h) -> w = vs x -> word_scalar_match (w, v) -> not_in_heap w v h -> not_mapsto_adt x st = true  -> related (add x v st) (vs, store_pair h (w, v)).
    intros Hr ? Hmatch Hninw Hninx.
    subst.
    destruct v as [w | a].
    {
      eapply related_Equal.
      {
        eapply related_add_sca; eauto.
        reflexivity.
      }
      { reflexivity. }
      {
        unfold word_scalar_match in *; simpl in *.
        subst.
        intros k.
        destruct (string_dec k x) as [? | Hne].
        - subst.
          symmetry; eapply Locals.sel_upd_eq; eauto.
        - symmetry; eapply Locals.sel_upd_ne; eauto.
      }
      unfold store_pair; simpl.
      reflexivity.
    }
    eapply related_Equal.
    {
      eapply related_add_adt; eauto.
    }
    {
      reflexivity.
    }
    { eauto. }
    {
      reflexivity.
    }
  Qed.

  Lemma make_map_make_heap_related' ks :
    forall values pairs st h vs cst,
      NoDup ks ->
      StringMap.Equal st (make_map ks values) ->
      WordMap.Equal h (@make_heap' ADTValue pairs) ->
      good_scalars pairs ->
      disjoint_ptrs pairs ->
      List.map fst pairs = List.map vs ks ->
      List.map snd pairs = values ->
      vs = fst cst ->
      h = snd cst ->
      CompileRunsTo.related st cst.
  Proof.
    induction ks; destruct values; destruct pairs; simpl; try solve [intros; try discriminate]; intros st h vs cst Hnd Hst Hh Hgs Hdp Hfst Hsnd ? ?; subst; destruct cst as [vs h]; simpl in *.
    {
      unfold make_heap in *; simpl in *.
      eapply related_Equal.
      - eapply empty_related.
      - eauto.
      - intros; eauto.
      - eauto.
    }
    rename a into k.
    destruct p as [w v']; simpl in *.
    inject Hsnd.
    inject Hfst.
    rename H into Hfst.
    unfold make_heap' in *.
    simpl in *.
    unfold good_scalars in *.
    inversion Hgs; subst; clear Hgs.
    rename H1 into Hmatch.
    rename H2 into Hgs.
    inversion Hnd; subst; clear Hnd.
    rename H1 into Hnink.
    rename H2 into Hnd.
    eapply disjoint_ptrs_cons_elim in Hdp.
    destruct Hdp as [Hninw Hdisj].
    eapply related_Equal.
    2 : eapply Hst.
    3 : eapply Hh.
    2 : solve [eauto].
    eapply related_add; trivial.
    {
      eapply IHks; try reflexivity; eauto.
    }
    {
      eapply no_clash_ls_not_in_heap; eauto.
    }
    {
      eapply find_none_not_mapsto_adt.
      eapply not_find_in_iff.
      eapply make_map_not_in; eauto.
    }
  Qed.

  Lemma make_map_make_heap_related ks :
    forall values pairs st h vs cst,
      NoDup ks ->
      StringMap.Equal st (make_map ks values) ->
      WordMap.Equal h (@make_heap ADTValue pairs) ->
      good_scalars pairs ->
      disjoint_ptrs pairs ->
      List.map fst pairs = List.map vs ks ->
      List.map snd pairs = values ->
      vs = fst cst ->
      h = snd cst ->
      CompileRunsTo.related st cst.
  Proof.
    intros; eapply make_map_make_heap_related'; eauto.
    rewrite <- make_heap_make_heap' by eauto.
    eauto.
  Qed.

  (*
    Lemma prog_safe cenv stmt cst stn fs v1 v2 w1 w2 :
      env_good_to_use gmodules imports stn fs ->
      fst cenv = from_bedrock_label_map (Labels stn) ->
      snd cenv = fs stn ->
      stmt = Compile.compile (CompileDFacade.compile prog) ->
      pre_cond v1 v2 ->
      disjoint_ptrs ((w1, v1) :: (w2, v2) :: nil) ->
      good_scalars ((w1, v1) :: (w2, v2) :: nil) ->
      w1 = Locals.sel (fst cst) argvar1 ->
      w2 = Locals.sel (fst cst) argvar2 ->
      snd cst == make_heap ((w1, v1) :: (w2, v2) :: nil) ->
      Safe cenv stmt cst.
    Proof.
      destruct cenv as [l2w w2spec]; simpl in *.
      destruct cst as [vs h]; simpl in *.
      intros Hegtu ? ? ? Hpre Hdisj Hgs ? ? Hheq.
      subst.
      eapply compile_safe; try reflexivity; simpl in *; trivial.
      {
        eapply dfacade_safe; eauto.
        reflexivity.
      }
      {
        eapply unit_syntax_ok.
      }
      {
        eauto.
      }
      {
        eapply WordMapFacts.submap_refl.
      }
      {
        eapply make_map_make_heap_related with (ks := argvars); eauto; simpl in *.
        reflexivity.
        eauto.
      }
      {
        eapply env_good_to_use_cenv_impls_env; eauto.
      }
    Qed.
   *)
  Import StringMapFacts.FMapNotations.

  Import WordMapFacts.FMapNotations.

  Require Import Bedrock.Platform.Cito.GeneralTactics5.

  Arguments empty {_}.
  (* a special version of make_map_related_make_heap *)
  Lemma make_map_related_make_heap_singleton k w v st h vs cst pairs :
    StringMapFacts.Submap (add k v empty) st ->
    (forall k', k' <> k -> @not_mapsto_adt ADTValue k' st = true ) ->
    CompileRunsTo.related st cst ->
    w = vs k ->
    vs = fst cst ->
    h == snd cst ->
    pairs = (w, v) :: nil ->
    WordMap.Equal h (make_heap pairs) /\
    disjoint_ptrs pairs /\
    good_scalars pairs.
  Proof.
    intros Hst Hnoleak Hr ? ? Hh ? .
    subst.
    destruct cst as [vs h']; simpl in *.
    rewrite Hh.
    split.
    {
      unfold make_heap.
      simpl.
      unfold store_pair; simpl.
      destruct v as [w | a]; simpl in *.
      {
        intros p.
        Import WordMapFacts WordMap.WordMap.
        rewrite empty_o.
        simpl in *.
        destruct (option_dec (find p h')) as [ [v Hv] | Hnone].
        {
          eapply Hr in Hv.
          destruct Hv as [x [ [Hvsx Hfx] Huni] ]; simpl in *.
          destruct (string_dec x k) as [? | Hnex].
          {
            subst.
            Import StringMapFacts StringMap.StringMap.
            specialize (Hst k (SCA _ w)).
            rewrite Hst in Hfx.
            discriminate.
            rewrite add_eq_o by eauto.
            eauto.
          }
          eapply Hnoleak in Hnex.
          eapply not_mapsto_adt_iff in Hnex.
          contradict Hnex.
          eexists; eauto.
        }
        eauto.
      }
      intros p.
      Import WordMapFacts WordMap.WordMap.
      destruct (weq p (vs k)) as [? | Hnep].
      {
        subst.
        rewrite add_eq_o by eauto.
        specialize (Hst k (ADT a)).
        Import StringMapFacts StringMap.StringMap.
        rewrite add_eq_o in Hst by eauto.
        specialize (Hst eq_refl).
        eapply Hr in Hst.
        simpl in *.
        eauto.
      }
      Import WordMapFacts WordMap.WordMap.
      rewrite add_neq_o by eauto.
      rewrite empty_o.
      destruct (option_dec (find p h')) as [ [v Hv] | Hnone].
      {
        eapply Hr in Hv.
        destruct Hv as [x [ [Hvsx Hfx] Huni] ]; simpl in *.
        destruct (string_dec x k) as [? | Hnex].
        {
          subst.
          intuition.
        }
        eapply Hnoleak in Hnex.
        eapply not_mapsto_adt_iff in Hnex.
        contradict Hnex.
        eexists; eauto.
      }
      eauto.
    }
    split.
    {
      unfold disjoint_ptrs; simpl in *.
      destruct v; simpl in *; intuition; NoDup.
    }
    unfold good_scalars.
    destruct v as [w | a]; simpl in *.
    {
      econstructor; intuition.
      unfold word_scalar_match; simpl.
      Import StringMapFacts StringMap.StringMap.
      specialize (Hst k (SCA _ w)).
      rewrite add_eq_o in Hst by eauto.
      specialize (Hst eq_refl).
      eapply Hr in Hst.
      simpl in *.
      eauto.
    }
    {
      econstructor; intuition; NoDup.
    }
  Qed.

(*
    Lemma prog_runsto cenv stmt cst cst' stn fs v1 v2 w1 w2 :
      RunsTo cenv stmt cst cst' ->
      env_good_to_use gmodules imports stn fs ->
      fst cenv = from_bedrock_label_map (Labels stn) ->
      snd cenv = fs stn ->
      stmt = Compile.compile (CompileDFacade.compile prog) ->
      pre_cond v1 v2 ->
      disjoint_ptrs {(w1, v1); (w2, v2)} ->
      good_scalars {(w1, v1); (w2, v2)} ->
      w1 = Locals.sel (fst cst) argvar1 ->
      w2 = Locals.sel (fst cst) argvar2 ->
      snd cst == make_heap {(w1, v1); (w2, v2)} ->
      exists vr,
        let wr := Locals.sel (fst cst') retvar in
        let pairs := {(wr, vr)} in
        post_cond v1 v2 vr /\
        snd cst' == make_heap pairs /\
        disjoint_ptrs pairs /\
        good_scalars pairs.
    Proof.
      destruct cenv as [l2w w2spec]; simpl in *.
      destruct cst as [vs h]; simpl in *.
      destruct cst' as [vs' h']; simpl in *.
      intros Hrt Hegtu ? ? ? Hpre Hdisj Hgs ? ? Hheq.
      subst.
      eapply CompileDFacadeToCito.compile_runsto in Hrt; try reflexivity; simpl in *; trivial.
      destruct Hrt as [st' [Hrt [Hsm Hr] ] ].
      6 : eapply env_good_to_use_cenv_impls_env; eauto.
      2 : eapply unit_syntax_ok.
      Focus 3.
      {
        eapply make_map_make_heap_related with (ks := argvars); eauto; simpl in *.
        reflexivity.
        eauto.
        eauto.
      }
      Unfocus.
      simpl in *.
      {
        eapply dfacade_runsto in Hrt; eauto.
        2 : reflexivity.
        destruct Hrt as [ret [Hst' [Hnoleak Hpost] ] ].
        eapply make_map_related_make_heap_singleton in Hr.
        {
          destruct Hr as [Hh' [Hgs' Hdisj'] ].
          exists ret.
          repeat try_split.
          - eauto.
          - eapply Hh'.
          - eauto.
          - eauto.
        }
        {
          instantiate (1 := ret).
          instantiate (1 := retvar).
          eauto.
        }
        {
          intros k Hnin.
          eauto.
        }
        {
          reflexivity.
        }
        {
          reflexivity.
        }
        {
          simpl.
          Require Import Bedrock.Platform.Cito.WordMapFacts.
          rewrite diff_same.
          rewrite diff_empty.
          reflexivity.
        }
        {
          eauto.
        }
      }
      {
        eapply submap_refl.
      }
      {
        eauto.
      }
      {
        eapply dfacade_safe; eauto.
        reflexivity.
      }
    Qed.
*)

End ADTValue.
