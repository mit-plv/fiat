Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.MakeWrapper.
Require Import Bedrock.Platform.Cito.ADT Bedrock.Platform.Cito.RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Module Import MakeWrapperMake := MakeWrapper.Make E M.
  Export MakeWrapperMake.

  Import LinkSpecMake.
  Require Import Bedrock.Platform.Cito.LinkSpecFacts.

  Require Import Bedrock.Platform.Cito.Inv.
  Module Import InvMake := Make E.
  Module Import InvMake2 := Make M.

  Import LinkSpecMake2.
  Require Import Bedrock.Platform.Cito.StringMap Bedrock.Platform.Cito.WordMap Bedrock.Platform.Cito.GLabelMap.

  Require Import Bedrock.Platform.Cito.LinkFacts.
  Module Import LinkFactsMake := Make E.

  Require Import Bedrock.Platform.Facade.CompileUnit Bedrock.Platform.Facade.CompileOut.
  Module Import CompileOutMake := CompileOut.Make E M.
  Export CompileOutMake.

  Section TopSection.

    (* pre_cond arg1 arg2 *)
    Variable pre_cond : Value ADTValue -> Value ADTValue -> Prop.
    (* post_cond arg1 arg2 ret *)
    Variable post_cond : Value ADTValue -> Value ADTValue -> Value ADTValue -> Prop.
    (* input of the this compiler *)
    Variable compile_unit : CompileUnit pre_cond post_cond.

    Notation prog := (CompileUnit.prog compile_unit).
    Definition unit_no_assign_to_args := (CompileUnit.no_assign_to_args compile_unit).
    Definition unit_syntax_ok := (CompileUnit.syntax_ok compile_unit).
    Definition unit_compile_syntax_ok := (CompileUnit.compile_syntax_ok compile_unit).
    Notation imports := (CompileUnit.imports compile_unit).

    Notation Value := (@Value ADTValue).

    Notation dfacade_safe := (CompileUnit.pre_safe compile_unit).
    Notation dfacade_runsto := (CompileUnit.pre_runsto_post compile_unit).

    Require Import Bedrock.Platform.Facade.DFacade.
    Require Import Bedrock.Platform.Facade.DFModule.
    Require Import Bedrock.Platform.Facade.CompileDFModule.
    Require Import Bedrock.Platform.Facade.NameDecoration.

    Definition core := Build_OperationalSpec argvars retvar prog eq_refl eq_refl unit_no_assign_to_args eq_refl eq_refl unit_syntax_ok.
    Definition function :=Build_DFFun core unit_compile_syntax_ok.
    Definition module : DFModule ADTValue.
      refine
        (Build_DFModule imports (StringMap.add fun_name function (@StringMap.empty _)) _).
      destruct compile_unit.
      simpl in *.
      rename import_module_names_ok into Himn.
      eapply Bool.andb_true_iff in Himn.
      destruct Himn as [? Himn].
      eauto.
    Defined.
    
    Require Import Bedrock.Platform.Cito.ListFacts3.

    Notation specs := (GLabelMap.map (@Axiomatic _) imports).

    Require Import Bedrock.Platform.Cito.StringMap.
    Import StringMap.
    Require Import Bedrock.Platform.Cito.StringMapFacts.
    Import FMapNotations.
    Local Open Scope fmap_scope.

    Require Import Bedrock.Platform.Facade.Listy.
    Import Notations Instances.
    Local Open Scope listy_scope.

    Definition good_module := compile_to_gmodule module module_name eq_refl.

    Definition modules := good_module :: nil.

    Require Import Bedrock.Platform.Cito.GoodModuleDec.
    Require Import Bedrock.Platform.Cito.GoodModuleDecFacts.

    Definition dummy_gf : GoodFunction.
      refine (to_good_function f _).
      eapply is_good_func_sound.
      reflexivity.
    Defined.

    Definition spec_op := hd dummy_gf (Functions good_module).

    Notation spec_op_b := (func_spec modules imports (module_name, fun_name) spec_op).

    Require Import Bedrock.Platform.Cito.Semantics.

    Require Import Bedrock.Platform.Facade.CompileDFacadeToCito.

    Import WordMapFacts.FMapNotations.
    Local Open Scope fmap_scope.
    Require Import Bedrock.Platform.Cito.GLabelMapFacts.
    Require Import Bedrock.Platform.Cito.Option.

    Lemma env_good_to_use_cenv_impls_env modules stn fs : env_good_to_use modules imports stn fs -> cenv_impls_env (from_bedrock_label_map (Labels stn), fs stn) (GLabelMap.map (@Axiomatic _) imports).
    Proof.
      intros Hgu.
      unfold env_good_to_use, cenv_impls_env in *.
      destruct Hgu as [Hsgu [Hinj Hfsgu] ].
      unfold stn_good_to_use, fs_good_to_use in *.
      split.
      {
        intros lbl spec Hflbl.
        rewrite map_o in Hflbl.
        eapply option_map_some_elim in Hflbl.
        destruct Hflbl as [aspec [Hflbl' ?] ].
        subst.
        simpl in *.
        assert (Hlblin : label_in modules imports lbl).
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
    Require Import Bedrock.Platform.Cito.StringMapFacts.
    Lemma empty_related vs : @CompileRunsTo.related ADTValue (StringMap.empty _) (vs, (WordMap.empty _)).
    Proof.
      unfold related.
      split.
      {
        intros x v Hf.
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

    Lemma prog_safe cenv stmt cst stn fs v1 v2 w1 w2 :
      env_good_to_use modules imports stn fs ->
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

    Import StringMapFacts.FMapNotations.

    Import WordMapFacts.FMapNotations.

    Require Import Bedrock.Platform.Cito.GeneralTactics5.

    Arguments empty {_}.
    (* a special version of make_map_related_make_heap *)
    Import WordMapFacts WordMap.WordMap.
    Import StringMapFacts StringMap.StringMap.
    Import WordMapFacts WordMap.WordMap.
    Import StringMapFacts StringMap.StringMap.
    Import WordMapFacts WordMap.WordMap.
    Import StringMapFacts StringMap.StringMap.
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
        unfold Make.InvMake.SemanticsMake.heap_empty.
        simpl.
        unfold store_pair; simpl.
        destruct v as [w | a]; simpl in *.
        {
          intros p.
          rewrite WordMapFacts.empty_o.
          simpl in *.
          destruct (option_dec (WordMap.find p h')) as [ [v Hv] | Hnone].
          {
            eapply Hr in Hv.
            destruct Hv as [x [ [Hvsx Hfx] Huni] ]; simpl in *.
            destruct (string_dec x k) as [? | Hnex].
            {
              subst.
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
        unfold Make.InvMake.SemanticsMake.heap_upd.
        intros p.
        destruct (weq p (vs k)) as [? | Hnep].
        {
          subst.
          rewrite WordMapFacts.add_eq_o by eauto.
          specialize (Hst k (ADT a)).
          rewrite add_eq_o in Hst by eauto.
          specialize (Hst eq_refl).
          eapply Hr in Hst.
          simpl in *.
          eauto.
        }
        rewrite WordMapFacts.add_neq_o by eauto.
        rewrite WordMapFacts.empty_o.
        destruct (option_dec (WordMap.find p h')) as [ [v Hv] | Hnone].
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
        destruct v; simpl in *; intuition.
      }
      unfold good_scalars.
      destruct v as [w | a]; simpl in *.
      {
        econstructor; intuition.
        unfold word_scalar_match; simpl.
        specialize (Hst k (SCA _ w)).
        rewrite add_eq_o in Hst by eauto.
        specialize (Hst eq_refl).
        eapply Hr in Hst.
        simpl in *.
        eauto.
      }
      {
        econstructor; intuition.
        unfold word_scalar_match; simpl.
        eauto.
      }
    Qed.
    Require Import Bedrock.Platform.Cito.WordMapFacts.

    Lemma prog_runsto cenv stmt cst cst' stn fs v1 v2 w1 w2 :
      RunsTo cenv stmt cst cst' ->
      env_good_to_use modules imports stn fs ->
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
      destruct Hrt as [st' [Hrt [Hsm [Hseleq Hr] ] ] ].
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

    Import Made.

    Definition output_module := bimport [[ (module_name!fun_name, spec_op_b) ]]
      bmodule export_module_name {{
        bfunction fun_name(argvar1, argvar2, "R") [compileS pre_cond post_cond]
          "R" <-- Call module_name!fun_name(extra_stack, argvar1, argvar2)
          [PRE[_, R] Emp
           POST[R'] [| R' = R |] ];;
          Return "R"
        end
      }}.

    Require Import Bedrock.Platform.AutoSep.

    Require Import Bedrock.Platform.Cito.GeneralTactics3.
    Opaque mult.
    Import LinkMake.StubsMake.StubMake.LinkSpecMake2.CompileFuncSpecMake.InvMake.
    Require Import Bedrock.sep.Locals.

    Theorem is_state_in2 : forall vs sp args e_stack h F, locals ("rp" :: "extra_stack" :: args) vs e_stack sp * is_heap h * mallocHeap 0 * F ===> is_state sp (Locals.sel vs "rp") (wordToNat (Locals.sel vs "extra_stack")) e_stack args (vs, h) nil * mallocHeap 0 * F.
      intros; sepLemma.
      etransitivity; [ | apply is_state_in'' ]; auto.
      sepLemma.
    Qed.

  Theorem is_state_out'' sp rp args pairs vs e_stack e_stack' h :
    NoDup args
    -> ~List.In "rp" args
    -> ~List.In "extra_stack" args
    -> length args = length pairs
    -> is_state sp rp e_stack e_stack' nil
    (vs, h) (List.map fst pairs)
    ===> Ex vs', locals ("rp" :: "extra_stack" :: args) vs' e_stack' sp
    * is_heap h * [| sel vs' "extra_stack" = e_stack |]
    * [| saved_vars vs' args pairs |].
    unfold is_state, locals, Inv.has_extra_stack; simpl.
    intros.
    apply Himp_ex_c.
    exists (upd (upd (zip_vals args pairs) "extra_stack" e_stack) "rp" rp).
    selify.
    replace (S (S (length args)) * 4)%nat with (8 + 4 * length args)%nat by omega.
    rewrite map_length.
    rewrite <- H2.
    rewrite natToWord_plus.
    eapply Himp_trans; [ | do 4 (apply Himp_star_frame; [ | apply Himp_refl ]);
      apply Himp_star_frame; [ apply Himp_refl | apply ptsto32m'_out ] ].
    simpl.
    generalize (List.map fst pairs); intro.
    unfold array at 1; simpl.
    sepLemma.
    do 2 (apply saved_vars_irrel; auto).
    eauto using saved_vars_zip_vars.

    etransitivity; [ apply himp_star_comm | ].
    apply himp_star_frame.
    etransitivity; [ | apply Arrays.ptsto32m'_in ].
    etransitivity; [ | apply ptsto32m_shift_base ].
    unfold array.
    instantiate (1 := 8).
    simpl.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.
    reflexivity.
    auto.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.
    unfold natToW.
    sepLemma.
  Qed.
  Require Import Coq.Arith.Mult.
  Require Import Bedrock.Platform.Cito.WordFacts.

  Theorem is_state_out''' sp rp args pairs vs h e_stack e_stack' :
                              NoDup args
                              -> ~List.In "rp" args
                              -> ~List.In "extra_stack" args
                              -> toArray args vs = List.map fst pairs
                              -> is_state sp rp e_stack e_stack' args
                                          (vs, h) nil
                                          ===> Ex vs', locals ("rp" :: "extra_stack" :: args) vs' e_stack' sp
                                                       * is_heap h * [| sel vs' "extra_stack" = e_stack |]
                                                       * [| saved_vars vs' args pairs |].
    unfold Himp; intros.
    etransitivity.
    2 : eapply is_state_out''; eauto.
    2 : eapply toArray_map_length; eauto.
    change LinkSpecMake2.CompileFuncSpecMake.InvMake2.is_state with is_state.
    unfold is_state, locals, Inv.has_extra_stack; simpl.
    rewrite H2.
    rewrite mult_0_r.
    rewrite wplus_0.
    set (array (List.map _ _) _).
    set (is_heap _).
    rewrite map_length.
    replace (length args) with (length pairs).
    rewrite plus_0_r.
    clear_all.
    sepLemma.
    symmetry; eapply toArray_map_length; eauto.
    Grab Existential Variables.
    eauto.
  Qed.

  Theorem is_state_out''''' vs sp rp F e_stack e_stack' args h (pairs : list (W * Value ADTValue)):
    toArray args vs = List.map fst pairs ->
                               NoDup args
                               -> ~List.In "rp" args
                               -> ~List.In "extra_stack" args
                               -> (is_state sp rp e_stack e_stack' args
                                            (vs, h) nil * mallocHeap 0) * F
                                                                                     ===> Ex vs', locals ("rp" :: "extra_stack" :: args) vs' e_stack' sp * is_heap h
                                                                                                  * [| sel vs' "extra_stack" = e_stack|]
                                                                                                  * mallocHeap 0 * F.
    intros Hfstpairs.
    intros.
    eapply Himp_trans; [ do 2 (apply Himp_star_frame; [ | apply Himp_refl ]); apply is_state_out''' | ]; eauto.
    set (_ :: _ :: _).
    clear_all.
    sepLemma.
  Qed.

  Transparent mult.
    Import LinkSpecMake2.CompileFuncSpecMake.InvMake.SemanticsMake.

    Theorem output_module_ok : moduleOk output_module.
      clear_all.
      vcgen.

      sep_auto.
      sep_auto.
      sep_auto.
      sep_auto.

      post.
      call_cito (extra_stack) (argvars).
      hiding ltac:(evaluate auto_ext).
      unfold name_marker.
      hiding ltac:(step auto_ext).
      unfold spec_without_funcs_ok.
      post.
      descend.
      set (vs := Locals.upd _ argvar2 _) in *.
      eapply CompileExprs.change_hyp.
      Focus 2.
      apply (@is_state_in2 vs).
      autorewrite with sepFormula.
      clear H10.
      hiding ltac:(step auto_ext).
      eapply prog_safe; eauto; simpl in *; try reflexivity.
      hiding ltac:(step auto_ext).
      repeat ((apply existsL; intro) || (apply injL; intro) || apply andL); reduce.
      apply swap; apply injL; intro.
      openhyp.
      match goal with
        | [ x : State |- _ ] => destruct x; simpl in *
      end.
      rename H11 into Hrunsto.
      eapply prog_runsto in Hrunsto; eauto.
      simpl in *.
      destruct Hrunsto as [vr [Hpost [Hheq [Hdisj Hgs] ] ] ].
      eapply replace_imp.
      set (vs := Locals.upd _ argvar2 _) in *.
      change extra_stack with (wordToNat (Locals.sel vs "extra_stack")).

      eapply is_state_out'''''.
      {
        instantiate (1 := {(_, _); (_, _)}).
        simpl; eauto.
      }
      {
        NoDup.
      }
      {
        NoDup.
      }
      {
        NoDup.
      }

      clear H10.
      hiding ltac:(step auto_ext).
      hiding ltac:(step auto_ext).

      sep_auto.
      sep_auto.
      {
        rewrite H10.
        rewrite H13.
        rewrite H1.
        words.
      }
      {
        eauto.
      }
      {
        rewrite H7.
        rewrite H12.
        eauto.
      }
      {
        rewrite H7.
        rewrite H12.
        eauto.
      }
      sep_auto.
      sep_auto.
      sep_auto.
      Grab Existential Variables.
      eauto.
      eauto.
    Qed.

    Notation compile_cito_to_bedrock := compile_to_bedrock.

    Notation output_module_impl := (compile_cito_to_bedrock modules imports).

    Open Scope bool_scope.

    Require Import Coq.Bool.Bool.

    Import MakeWrapperMake.LinkMake.
    Import MakeWrapperMake.LinkMake.LinkModuleImplsMake.

    Theorem output_module_impl_ok : moduleOk output_module_impl.
    Proof.

      match goal with
        | |- moduleOk (compile_to_bedrock ?Modules ?Imports ) =>
          let H := fresh in
          assert (GoodToLink_bool Modules Imports = true);
            [ unfold GoodToLink_bool(*; simpl*) |
              eapply GoodToLink_bool_sound in H; openhyp; simpl in *; eapply result_ok; simpl in * ]
            ; eauto
      end.

      pose (Himn := import_module_names_ok).
      eapply andb_true_iff in Himn.
      destruct Himn as [Himn1 Himn2].
      eapply andb_true_iff.
      split.
      eapply andb_true_iff.
      split.
      {
        reflexivity.
      }
      {
        eapply forallb_forall.
        intros x Hin.
        eapply forallb_forall in Himn1.
        2 : solve [eapply Hin].
        destruct (in_dec string_dec x (List.map GName modules)); simpl in *.
        - intuition.
          subst; simpl in *; intuition.
        - eauto.
      }
      {
        eauto.
      }
    Qed.

    Definition compile : CompileOut pre_cond post_cond := Build_CompileOut output_module_ok eq_refl output_module_impl_ok.

  End TopSection.

  (* In case Bedrock's tactic 'link' doesn't work well with simpl and unfold. Isn't needed in my test case *)
  Module LinkUnfoldHelp.

    Import MakeWrapperMake.LinkMake.LinkModuleImplsMake.

    Arguments Imports /.
              Arguments Exports /.
              Arguments CompileModuleMake.mod_name /.
              Arguments impl_module_name /.
              Arguments GName /.
              Arguments append /.
              Arguments CompileModuleMake.imports /.
              Arguments LinkMake.StubsMake.StubMake.bimports_diff_bexports /.
              Arguments LinkMake.StubsMake.StubMake.bimports_diff_bexports /.
              Arguments diff_map /.
              Arguments GLabelMapFacts.diff_map /.
              Arguments List.filter /.
              Arguments LinkMake.StubsMake.StubMake.LinkSpecMake2.func_impl_export /.
              Arguments LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label /.
              Arguments LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label /.
              Arguments GName /.
              Arguments impl_module_name /.
              Arguments append /.
              Arguments IsGoodModule.FName /.
              Arguments CompileModuleMake.mod_name /.
              Arguments impl_module_name /.
              Arguments LinkMake.StubsMake.StubMake.bimports_diff_bexports /.
              Arguments LinkMake.StubsMake.StubMake.LinkSpecMake2.func_impl_export /.
              Arguments LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label /.
              Arguments impl_module_name /.
              Arguments CompileModuleMake.imports /.

              Ltac link_simp2 :=
                simpl Imports;
                simpl Exports;
                unfold CompileModuleMake.mod_name;
                unfold impl_module_name;
                simpl GName;
                simpl append;
                unfold CompileModuleMake.imports;
                unfold LinkMake.StubsMake.StubMake.bimports_diff_bexports, LinkMake.StubsMake.StubMake.bimports_diff_bexports;
                unfold diff_map, GLabelMapFacts.diff_map;
                simpl List.filter;
                unfold LinkMake.StubsMake.StubMake.LinkSpecMake2.func_impl_export, LinkMake.StubsMake.StubMake.LinkSpecMake2.func_impl_export;
                unfold LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label, LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label;
                simpl GName;
                unfold impl_module_name;
                simpl append;
                simpl IsGoodModule.FName;
                unfold CompileModuleMake.mod_name;
                unfold impl_module_name;
                unfold LinkMake.StubsMake.StubMake.bimports_diff_bexports;
                unfold LinkMake.StubsMake.StubMake.LinkSpecMake2.func_impl_export;
                unfold LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label;
                unfold impl_module_name;
                unfold CompileModuleMake.imports.

    Ltac link2 ok1 ok2 :=
      eapply linkOk; [ eapply ok1 | eapply ok2
                       | reflexivity
                       | link_simp2; link_simp; eauto ..
                     ].

  End LinkUnfoldHelp.

End Make.
