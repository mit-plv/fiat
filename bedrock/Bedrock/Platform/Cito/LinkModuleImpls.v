Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.ADT.
Require Import Bedrock.Platform.Cito.RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Bedrock.Platform.AutoSep.
  Require Import Bedrock.StructuredModule.
  Require Import Bedrock.Platform.Cito.StructuredModuleFacts.
  Require Import Bedrock.Platform.Cito.GoodModule.
  Require Import Bedrock.Platform.Cito.GoodFunction.
  Require Import Bedrock.Platform.Cito.ConvertLabel.
  Require Import Bedrock.Platform.Facade.NameDecoration.
  Require Import Bedrock.Platform.Wrap.
  Require Import Bedrock.Platform.Cito.GeneralTactics.
  Require Import Bedrock.Platform.Cito.GeneralTactics2.
  Require Import Bedrock.Platform.Cito.StringFacts2.

  Require Import Bedrock.Platform.Cito.CompileModule.
  Module Import CompileModuleMake := Make E M.
  Require Import Bedrock.Platform.Cito.CompileFuncSpec.
  Import CompileFuncMake.
  Import CompileFuncImplMake.
  Import CompileFuncSpecMake.
  Require Import Bedrock.Platform.Cito.Inv.
  Import InvMake.
  Require Import Bedrock.Platform.Cito.Semantics.
  Import SemanticsMake.
  Import InvMake2.
  Require Import Bedrock.Platform.Cito.GoodOptimizer.
  Import GoodOptimizerMake.

  Require Import Bedrock.Platform.Cito.LinkSpec.
  Module Import LinkSpecMake := Make E.
  Module Import LinkSpecMake2 := Make M.

  Require Import Bedrock.Platform.Cito.ListFacts1.
  Require Import Bedrock.Platform.Cito.ListFacts2.

  Require Import Bedrock.StringSet.
  Module Import SS := StringSet.
  Require Import Bedrock.Platform.Cito.StringSetFacts.

  Require Import Bedrock.Labels.
  Require Import Bedrock.LabelMap.
  Require Bedrock.Platform.Cito.LabelMapFacts.
  Require Import Bedrock.Platform.Cito.GLabel.
  Require Import Bedrock.Platform.Cito.GLabelMap.
  Import GLabelMap.
  Require Import Bedrock.Platform.Cito.GLabelMapFacts.

  Require Import Bedrock.Platform.Cito.ConvertLabelMap.
  Import Notations.
  Open Scope clm_scope.

  Section TopSection.

    (* modules to be linked *)
    Variable modules : list GoodModule.

    Hypothesis ModulesNotEmpty : modules <> nil.

    Definition FName := SyntaxFunc.Name.

    Definition MName := GoodModule.Name.

    Hypothesis NoDupModuleNames : List.NoDup (List.map MName modules).

    Variable optimizer : Optimizer.

    Hypothesis IsGoodOptimizer : GoodOptimizer optimizer.

    (* Since modules <> nil, dummy will never be used. *)
    Definition dummy := @StructuredModule.bmodule_ nil "" nil.

    Definition link_all ls := fold_right_2 link dummy ls.

    Definition compile m := CompileModuleMake.compile m IsGoodOptimizer.

    Import ListNotations.
    Import FMapNotations.
    Open Scope fmap.
    Notation to_set := StringSetFacts.of_list.

    Hint Extern 1 => reflexivity.

    Definition impl_MName m := impl_module_name (MName m).

    Require Import Coq.Lists.SetoidList.
    Hint Constructors NoDupA.
    Hint Unfold NoDupKey.

    Lemma compile_module_Imports : forall m, Imports (compile m) === {}.
        intros.
        unfold compile, CompileModuleMake.compile.
        unfold compiled_funcs, bmodule_, Imports.
        unfold imports.
        rewrite importsMap_of_list.
        eapply to_blm_Equal.
        eauto.
        econstructor.
    Qed.

    Notation get_module_Exports := module_impl_exports.

    Lemma compile_module_Exports : forall m, Exports (compile m) === get_module_Exports m.
        intros.
        unfold compile, CompileModuleMake.compile.
        unfold compiled_funcs, bmodule_; simpl.
        rewrite exps_spec.
        eapply to_blm_Equal.
        rewrite map_map.
        unfold func_to_import, compile_func; simpl in *.
        unfold mod_name.
        reflexivity.
    Qed.

    Lemma compile_module_Modules : forall m, SS.Equal (Modules (compile m)) (singleton (impl_MName m)).
      intros.
      unfold compile, CompileModuleMake.compile; simpl.
      unfold mod_name.
      unfold impl_MName.
      eauto.
    Qed.

    Ltac incl_tran_cons := eapply incl_tran; [ | eassumption ]; intuition.

    Require Import Bedrock.Platform.Cito.StringSetTactics.

    Lemma In_exports_module_name : forall k m, In k (get_module_Exports m) -> fst k = impl_MName m.
      unfold get_module_Exports.
      intros.
      eapply In_to_map in H.
      unfold InKey in *.
      rewrite map_map in H.
      simpl in *.
      eapply in_map_iff in H.
      openhyp.
      subst.
      eauto.
    Qed.

    Lemma impl_MName_neq_Disjoint : forall m1 m2, impl_MName m1 <> impl_MName m2 -> Disjoint (get_module_Exports m1) (get_module_Exports m2).
      unfold Disjoint.
      intros.
      not_not.
      openhyp.
      eapply In_exports_module_name in H.
      eapply In_exports_module_name in H0.
      congruence.
    Qed.

    Lemma Disjoint_exports_many_exports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map impl_MName (m :: ms)) -> Disjoint (get_module_Exports m) (update_all (List.map get_module_Exports ms)).
      induction ms; simpl; intros.
      rewrite update_all_nil.
      eapply Disjoint_empty.
      rewrite update_all_cons.
      eapply Disjoint_update.
      eapply NoDup_cons_cons in H0.
      eapply impl_MName_neq_Disjoint; eauto.
      eapply IHms.
      incl_tran_cons.
      simpl.
      inversion H0; subst.
      inversion H4; subst.
      econstructor; eauto.
      intuition.
    Qed.

    Lemma NoDup_MName_NoDup_impl_Name : forall ms, List.NoDup (List.map MName ms) -> List.NoDup (List.map impl_MName modules).
      intros.
      unfold impl_MName.
      rewrite <- map_map.
      eapply Injection_NoDup; eauto.
      unfold IsInjection.
      intros.
      not_not.
      unfold impl_module_name in *.
      eapply append_inj_2; eauto.
    Qed.

    Lemma link_all_ok :
      forall (ms : list GoodModule),
        let linked := link_all (List.map compile ms) in
        let module_names := List.map impl_MName ms in
        let linked_module_names := to_set module_names in
        let linked_exports := update_all (List.map get_module_Exports ms) in
        let linked_imports := {} in
        ms <> nil ->
        incl ms modules ->
        List.NoDup module_names ->
        moduleOk linked /\
        SS.Equal (Modules linked) linked_module_names /\
        Exports linked === linked_exports /\
        Imports linked === linked_imports.
    Proof.
      Opaque CompileModuleMake.compile.
      unfold link_all.
      induction ms; simpl; intros.
      intuition.
      destruct ms; simpl in *.

      descend.
      eapply CompileModuleMake.compileOk.
      rewrite compile_module_Modules.
      rewrite P.add_union_singleton.
      eapply Equal_Subset_iff; split; subset_solver.
      rewrite compile_module_Exports.
      rewrite update_all_single.
      eauto.
      rewrite compile_module_Imports.
      eauto.

      simpl in *.
      destruct IHms.
      intuition.
      incl_tran_cons.
      inversion H1; subst; eauto.
      openhyp.

      descend.
      eapply linkOk.
      eapply CompileModuleMake.compileOk.
      eapply H2.

      eapply inter_is_empty_iff.
      rewrite H3.
      rewrite P.add_union_singleton.
      rewrite compile_module_Modules.
      eapply Disjoint_union.
      split.
      eapply Disjoint_singletons.
      eapply NoDup_cons_cons.
      eauto.
      eapply Disjoint_singleton.
      inversion H1; subst.
      not_not.
      eapply of_list_spec in H6.
      intuition.

      eapply importsOk_Compat.
      rewrite H4.
      rewrite compile_module_Imports.
      eapply to_blm_Compat.
      Existing Instance Compat_rel_Symmetric.
      symmetry.
      eapply Compat_empty.
      eapply importsOk_Compat.
      rewrite H5.
      rewrite compile_module_Exports.
      eapply to_blm_Compat.
      symmetry.
      eapply Compat_empty.
      eapply importsOk_Compat.
      rewrite H5.
      rewrite compile_module_Imports.
      eapply to_blm_Compat.
      eapply Compat_empty.

      rewrite H3.
      rewrite compile_module_Modules.
      repeat rewrite of_list_cons.
      repeat rewrite P.add_union_singleton.
      eapply Equal_Subset_iff; split; subset_solver.
      rewrite XCAP_union_update.
      rewrite H4.
      repeat rewrite update_all_cons.
      set (_ + update_all _).
      rewrite Disjoint_update_sym.
      rewrite to_blm_update.
      eapply LabelMapFacts.update_m; eauto.
      eapply compile_module_Exports.
      unfold t0; clear t0.
      rewrite <- update_all_cons.
      eapply Disjoint_exports_many_exports with (ms := g :: ms); eauto.
      rewrite XCAP_union_update.
      repeat rewrite XCAP_diff_diff.
      rewrite H5.
      rewrite H4.
      rewrite compile_module_Imports.
      rewrite compile_module_Exports.
      repeat rewrite <- to_blm_diff.
      rewrite <- to_blm_update.
      eapply to_blm_Equal.
      repeat rewrite empty_diff; eauto.
    Qed.

    Definition ms := List.map compile modules.

    Definition m := link_all ms.

    (* Interface *)

    Theorem module_ok : moduleOk m.
      unfold m.
      unfold ms.
      eapply link_all_ok; intuition.
      eapply NoDup_MName_NoDup_impl_Name; eauto.
    Qed.

    Theorem module_imports : Imports m === {}.
      edestruct link_all_ok; eauto.
      intuition.
      eapply NoDup_MName_NoDup_impl_Name; eauto.
      openhyp.
      eauto.
    Qed.

    Theorem module_exports : Exports m === LinkSpecMake2.impl_exports modules.
      edestruct link_all_ok; eauto.
      intuition.
      eapply NoDup_MName_NoDup_impl_Name; eauto.
      openhyp.
      unfold m.
      rewrite H1.
      eapply to_blm_Equal.
      eauto.
    Qed.

    Theorem module_module_names : SS.Equal (Modules m) (to_set (List.map impl_MName modules)).
      edestruct link_all_ok; eauto.
      intuition.
      eapply NoDup_MName_NoDup_impl_Name; eauto.
      openhyp.
      unfold m.
      rewrite H0.
      eauto.
    Qed.

  End TopSection.

End Make.
