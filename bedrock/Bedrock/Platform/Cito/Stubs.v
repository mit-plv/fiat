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

  Require Import Bedrock.Platform.Cito.Stub.
  Module Import StubMake := Make E M.
  Require Import Bedrock.Platform.Cito.CompileFuncSpec.
  Import CompileFuncSpecMake.
  Require Import Bedrock.Platform.Cito.Inv.
  Import InvMake.
  Require Import Bedrock.Platform.Cito.Semantics.
  Import SemanticsMake.
  Import InvMake2.

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

    (* modules to be exported *)
    Variable modules : list GoodModule.

    Notation FName := SyntaxFunc.Name.
    Notation MName := GoodModule.Name.
    Notation module_names := (List.map MName modules).

    Hypothesis NoDupModuleNames : List.NoDup module_names.

    (* imported specs *)
    Variable imports : t ForeignFuncSpec.

    Notation fst2 := (fun x => @fst _ _ (@fst _ _ x)).
    Notation imported_module_names := (List.map fst2 (elements imports)).

    Hypothesis NoSelfImport : ListFacts1.Disjoint module_names imported_module_names.

    Hypotheses ImportsGoodModuleName : forall l, In l imports -> IsGoodModuleName (fst l).

    Import ListNotations.
    Import FMapNotations.
    Open Scope fmap.

    Notation do_make_module := (make_module modules imports).

    Require Import Coq.Lists.SetoidList.
    Hint Constructors NoDupA.
    Hint Unfold NoDupKey.

    Ltac incl_tran_cons := eapply incl_tran; [ | eassumption ]; intuition.

    Require Import Bedrock.Platform.Cito.StringSetTactics.

    Notation to_set := StringSetFacts.of_list.

    Notation get_module_Exports := (LinkSpecMake2.module_exports modules imports).
    Notation foreign_imports := (LinkSpecMake2.imports imports).
    Notation total_exports := (LinkSpecMake2.exports modules imports).
    Notation get_module_Imports := (StubMake.get_module_Imports modules imports).

    Lemma MName_neq_Disjoint : forall m1 m2, MName m1 <> MName m2 -> Disjoint (get_module_Exports m1) (get_module_Exports m2).
      unfold Disjoint.
      intros.
      not_not.
      openhyp.
      eapply In_exports_module_name in H.
      eapply In_exports_module_name in H0.
      congruence.
    Qed.

    Lemma Disjoint_exports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Disjoint (get_module_Exports m) (update_all (List.map get_module_Exports ms)).
      induction ms; simpl; intros.
      unfold update_all; simpl.
      eapply Disjoint_empty.
      rewrite update_all_cons.
      eapply Disjoint_update.
      eapply NoDup_cons_cons in H0.
      eapply MName_neq_Disjoint; eauto.
      eapply IHms.
      incl_tran_cons.
      simpl.
      inversion H0; subst.
      inversion H4; subst.
      econstructor; eauto.
      intuition.
    Qed.

    Lemma Compat_exports_many_exports : forall ms m, List.In m ms -> incl ms modules -> List.NoDup (List.map MName ms) -> Compat (get_module_Exports m) (update_all (List.map get_module_Exports ms)).
      induction ms; simpl; intros.
      intuition.
      openhyp.
      subst.
      rewrite update_all_cons.
      eapply Compat_update.
      econstructor.
      eapply Disjoint_Compat.
      eapply Disjoint_exports; eauto.
      rewrite update_all_cons.
      eapply Compat_update.
      eapply Disjoint_Compat.
      eapply MName_neq_Disjoint.
      eapply NoDup_cons_elim in H1; eauto.
      eapply in_map; eauto.
      eapply IHms; eauto.
      incl_tran_cons.
      inversion H1; subst; eauto.
    Qed.

    Lemma Compat_exports_foreign_imports : forall m, List.In m modules -> Compat (get_module_Exports m) foreign_imports.
      intros.
      eapply Disjoint_Compat.
      eapply Disjoint_exports_foreign_imports; eauto.
    Qed.

    Notation get_module_impl_Imports := module_impl_exports.

    Lemma Disjoint_exports_impl_imports : forall m1 m2, List.In m1 modules -> List.In m2 modules -> Disjoint (get_module_Exports m1) (get_module_impl_Imports m2).
      intros.
      unfold get_module_impl_Imports.
      unfold Disjoint.
      intros.
      intuition.
      eapply In_exports_module_name in H2.
      eapply In_to_map in H3.
      unfold InKey in *.
      unfold func_impl_export in *.
      rewrite map_map in H3.
      simpl in *.
      eapply in_map_iff in H3.
      openhyp.
      subst.
      unfold impl_label in *.
      simpl in *.
      eapply IsGoodModuleName_not_impl_module_name.
      eapply GoodModule_GoodName.
      eexists; eauto.
    Qed.

    Lemma Compat_exports_impl_imports : forall m1 m2, List.In m1 modules -> List.In m2 modules -> Compat (get_module_Exports m1) (get_module_impl_Imports m2).
      intros.
      eapply Disjoint_Compat.
      eapply Disjoint_exports_impl_imports; eauto.
    Qed.

    Lemma Disjoint_impl_imports_foreign_imports : forall m, List.In m modules -> Disjoint (get_module_impl_Imports m) foreign_imports.
      intros.
      unfold get_module_impl_Imports.
      unfold Disjoint.
      intros.
      intuition.
      unfold LinkSpecMake2.imports in *.
      eapply mapi_in_iff with (m := imports) in H2.
      eapply In_to_map in H1.
      unfold InKey in *.
      unfold func_impl_export in *.
      rewrite map_map in H1.
      simpl in *.
      eapply in_map_iff in H1.
      openhyp.
      subst.
      unfold impl_label in *.
      eapply IsGoodModuleName_not_impl_module_name.
      eapply ImportsGoodModuleName.
      eauto.
      eexists.
      simpl.
      eauto.
    Qed.

    Lemma Compat_impl_imports_foreign_imports : forall m, List.In m modules -> Compat (get_module_impl_Imports m) foreign_imports.
      intros.
      eapply Disjoint_Compat.
      eapply Disjoint_impl_imports_foreign_imports; eauto.
    Qed.

    Lemma In_impl_imports_module_name : forall k m, In k (get_module_impl_Imports m) -> fst k = impl_module_name (MName m).
      unfold get_module_impl_Imports.
      intros.
      eapply In_to_map in H.
      unfold InKey in *.
      rewrite map_map in H.
      unfold impl_label in *.
      simpl in *.
      eapply in_map_iff in H.
      openhyp.
      subst.
      eauto.
    Qed.

    Lemma impl_module_name_is_injection : forall s1 s2, impl_module_name s1 = impl_module_name s2 -> s1 = s2.
      intros.
      unfold impl_module_name in *.
      eapply append_inj_2; eauto.
    Qed.

    Lemma Disjoint_impl_imports_impl_imports : forall m1 m2, List.In m1 modules -> List.In m2 modules -> MName m1 <> MName m2 -> Disjoint (get_module_impl_Imports m1) (get_module_impl_Imports m2).
      intros.
      unfold Disjoint.
      intros.
      not_not.
      openhyp.
      eapply In_impl_imports_module_name in H1.
      eapply In_impl_imports_module_name in H2.
      rewrite H1 in H2.
      eapply impl_module_name_is_injection; eauto.
    Qed.

    Lemma Compat_impl_imports_impl_imports : forall m1 m2, List.In m1 modules -> List.In m2 modules -> MName m1 <> MName m2 -> Compat (get_module_impl_Imports m1) (get_module_impl_Imports m2).
      intros.
      eapply Disjoint_Compat.
      eapply Disjoint_impl_imports_impl_imports; eauto.
    Qed.
    Existing Instance Disjoint_rel_Symmetric.

    Lemma Disjoint_exports_imports : forall m, List.In m modules -> Disjoint (get_module_Exports m) (get_module_Imports m).
      intros.
      unfold StubMake.get_module_Imports.
      symmetry.
      eapply Disjoint_after_diff.
    Qed.

    Lemma Compat_exports_total_exports : forall m, List.In m modules -> Compat (get_module_Exports m) total_exports.
      intros.
      eapply Compat_exports_many_exports; eauto.
      intuition.
    Qed.
    Existing Instance Compat_rel_Symmetric.

    Lemma Compat_many_exports_total_exports : forall ms, incl ms modules -> Compat (update_all (List.map get_module_Exports ms)) total_exports.
      intros.
      symmetry.
      eapply Compat_update_all.
      eapply Forall_forall.
      intros.
      eapply in_map_iff in H0.
      openhyp.
      subst.
      symmetry.
      eapply Compat_exports_total_exports; eauto.
    Qed.

    Lemma Disjoint_many_exports_impl_imports : forall ms m, incl (m :: ms) modules -> Disjoint (update_all (List.map get_module_Exports ms)) (get_module_impl_Imports m).
      intros.
      symmetry.
      eapply Disjoint_update_all.
      eapply Forall_forall.
      intros.
      eapply in_map_iff in H0.
      openhyp.
      subst.
      symmetry.
      eapply Disjoint_exports_impl_imports; intuition.
    Qed.

    Lemma Compat_many_exports_impl_imports : forall ms m, incl (m :: ms) modules -> Compat (update_all (List.map get_module_Exports ms)) (get_module_impl_Imports m).
      intros.
      eapply Disjoint_Compat.
      eapply Disjoint_many_exports_impl_imports; eauto.
    Qed.

    Lemma Compat_exports_imports : forall m1 m2, List.In m1 modules -> List.In m2 modules -> MName m1 <> MName m2 -> Compat (get_module_Exports m1) (get_module_Imports m2).
      intros.
      unfold StubMake.get_module_Imports.
      symmetry.
      eapply Compat_diff.
      symmetry.
      repeat eapply Compat_update.
      eapply Compat_exports_total_exports; eauto.
      eapply Compat_exports_foreign_imports; eauto.
      eapply Compat_exports_impl_imports; eauto.
    Qed.

    Lemma Disjoint_total_exports_foreign_imports : Disjoint total_exports foreign_imports.
      eapply Disjoint_many_exports_foreign_imports; intuition.
    Qed.

    Lemma Disjoint_total_exports_impl_imports : forall m, List.In m modules -> Disjoint total_exports (get_module_impl_Imports m).
      intros.
      eapply Disjoint_many_exports_impl_imports; intuition.
    Qed.

    Lemma Compat_total_exports_impl_imports : forall m, List.In m modules -> Compat total_exports (get_module_impl_Imports m).
      intros.
      eapply Compat_many_exports_impl_imports; intuition.
    Qed.
    Existing Instance Compat_rel_Reflexive.

    Lemma Compat_imports_imports : forall m1 m2, List.In m1 modules -> List.In m2 modules -> MName m1 <> MName m2 -> Compat (get_module_Imports m1) (get_module_Imports m2).
      intros.
      unfold StubMake.get_module_Imports.
      eapply Compat_diff.
      symmetry.
      eapply Compat_diff.
      repeat eapply Compat_update; symmetry; repeat eapply Compat_update.
      reflexivity.
      eapply Compat_total_exports_foreign_imports; eauto.
      eapply Compat_total_exports_impl_imports; eauto.
      symmetry; eapply Compat_total_exports_foreign_imports; eauto.
      reflexivity.
      symmetry; eapply Compat_impl_imports_foreign_imports; eauto.
      symmetry; eapply Compat_total_exports_impl_imports; eauto.
      eapply Compat_impl_imports_foreign_imports; eauto.
      eapply Compat_impl_imports_impl_imports; eauto.
    Qed.

    Lemma compat_imports_exports : forall ms m, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Compat (get_module_Imports m) (update_all (List.map get_module_Exports ms)).
      intros.
      unfold StubMake.get_module_Imports.
      eapply Compat_diff.
      symmetry.
      repeat eapply Compat_update.
      eapply Compat_many_exports_total_exports.
      incl_tran_cons.
      inversion H0; subst; eauto.
      eapply Compat_many_exports_foreign_imports; eauto.
      incl_tran_cons.
      inversion H0; subst; eauto.
      eapply Compat_many_exports_impl_imports; eauto.
    Qed.

    Lemma compat_exports_imports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Compat (get_module_Exports m) (update_all (List.map get_module_Imports ms) - update_all (List.map get_module_Exports ms)).
      intros.
      symmetry.
      eapply Compat_diff.
      symmetry.
      eapply Compat_update_all.
      eapply Forall_forall.
      intros.
      eapply in_map_iff in H1.
      openhyp.
      subst.
      eapply Compat_exports_imports.
      intuition.
      intuition.
      simpl in *.
      eapply NoDup_cons_elim in H0; eauto.
      eapply in_map; eauto.
    Qed.

    Lemma compat_imports_many_imports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Compat (get_module_Imports m) (update_all (List.map get_module_Imports ms)).
      intros.
      eapply Compat_update_all.
      eapply Forall_forall.
      intros.
      eapply in_map_iff in H1.
      openhyp.
      subst.
      eapply Compat_imports_imports.
      intuition.
      intuition.
      simpl in *.
      eapply NoDup_cons_elim in H0; eauto.
      eapply in_map; eauto.
    Qed.

    Lemma compat_imports_imports : forall m ms, incl (m :: ms) modules -> List.NoDup (List.map MName (m :: ms)) -> Compat (get_module_Imports m) (update_all (List.map get_module_Imports ms) - update_all (List.map get_module_Exports ms)).
      intros.
      symmetry.
      eapply Compat_diff.
      symmetry.
      eapply compat_imports_many_imports; eauto.
    Qed.

    Lemma combine_imports_exports :
      forall a ms,
        incl (a :: ms) modules ->
        List.NoDup (List.map MName (a :: ms)) ->
        update_all (List.map get_module_Imports ms) -
        update_all (List.map get_module_Exports ms) - get_module_Exports a +
        (get_module_Imports a - update_all (List.map get_module_Exports ms)) ==
        get_module_Imports a +
        update_all (List.map get_module_Imports ms) -
        (get_module_Exports a + update_all (List.map get_module_Exports ms)).
      intros.
      rewrite Disjoint_diff_update_comm.
      rewrite update_diff_same.
      rewrite Compat_update_sym.
      rewrite diff_update.
      rewrite diff_diff_sym.
      reflexivity.
      symmetry.
      eapply compat_imports_many_imports; eauto.
      eapply Disjoint_diff.
      eapply Disjoint_exports_imports.
      intuition.
    Qed.

    Hypothesis ModulesNotEmpty : modules <> nil.

    Notation total_impls := (LinkSpecMake2.impl_exports modules).

    Definition final_imports := foreign_imports + total_impls.

    Lemma not_nil_cons : forall A ls, ls <> @nil A -> exists x xs, ls = x :: xs.
      destruct ls; intuition eauto.
    Qed.

    Lemma foreign_imports_Disjoint_total_impls : Disjoint foreign_imports total_impls.
      eapply Disjoint_update_all.
      eapply Forall_forall.
      intros.
      eapply in_map_iff in H.
      openhyp.
      subst.
      symmetry.
      eapply Disjoint_impl_imports_foreign_imports; eauto.
    Qed.

    Lemma neq_sym : forall A (a b : A), a <> b -> b <> a.
      intuition.
    Qed.

    Lemma AllCompat_many_impls : forall ms, incl ms modules -> List.NoDup (List.map MName ms) -> AllCompat (List.map get_module_impl_Imports ms).
      induction ms; simpl; intros.
      econstructor.
      econstructor.
      eapply Forall_forall.
      intros.
      eapply in_map_iff in H1; openhyp; subst.
      simpl in *.
      eapply Compat_impl_imports_impl_imports; eauto.
      intuition.
      intuition.
      eapply neq_sym.
      eapply NoDup_cons_elim; eauto.
      eapply in_map; eauto.
      eapply IHms.
      incl_tran_cons.
      inversion H0; subst; eauto.
    Qed.

    Lemma AllCompat_impls : AllCompat (List.map get_module_impl_Imports modules).
      eapply AllCompat_many_impls; eauto.
      intuition.
    Qed.

    Lemma AllCompat_many_imports : forall ms, incl ms modules -> List.NoDup (List.map MName ms) -> AllCompat (List.map get_module_Imports ms).
      induction ms; simpl; intros.
      econstructor.
      econstructor.
      eapply Forall_forall.
      intros.
      eapply in_map_iff in H1; openhyp; subst.
      simpl in *.
      eapply Compat_imports_imports; eauto.
      intuition.
      intuition.
      eapply neq_sym.
      eapply NoDup_cons_elim; eauto.
      eapply in_map; eauto.
      eapply IHms.
      incl_tran_cons.
      inversion H0; subst; eauto.
    Qed.

    Lemma AllCompat_imports : AllCompat (List.map get_module_Imports modules).
      eapply AllCompat_many_imports; eauto.
      intuition.
    Qed.

    Lemma final_imports_correct : update_all (List.map get_module_Imports modules) - total_exports == final_imports.
      unfold Equal; intros.
      eapply option_univalence; split; intros.
      eapply find_2 in H.
      eapply diff_mapsto_iff in H.
      openhyp.
      eapply update_all_elim in H.
      openhyp.
      eapply in_map_iff in H.
      openhyp.
      subst.
      unfold StubMake.get_module_Imports in *.
      unfold final_imports.
      eapply diff_mapsto_iff in H1.
      openhyp.
      eapply update_mapsto_iff in H.
      openhyp.
      eapply find_1.
      eapply update_mapsto_iff.
      left.
      eapply update_all_intro; eauto.
      eapply AllCompat_impls.
      eapply in_map; eauto.
      eapply update_mapsto_iff in H.
      openhyp.
      eapply find_1.
      eapply update_mapsto_iff.
      right.
      split.
      eauto.
      nintro.
      eapply foreign_imports_Disjoint_total_impls; eauto.
      split; eauto.
      eapply MapsTo_In; eauto.
      eapply MapsTo_In in H; intuition.
      unfold final_imports in H.
      eapply find_2 in H.
      eapply update_mapsto_iff in H.
      openhyp.
      eapply update_all_elim in H.
      openhyp.
      eapply in_map_iff in H.
      openhyp; subst.
      eapply find_1.
      eapply diff_mapsto_iff.
      split.
      eapply update_all_intro.
      eapply AllCompat_imports.
      eapply in_map; eauto.
      unfold StubMake.get_module_Imports.
      eapply diff_mapsto_iff.
      split.
      eapply update_mapsto_iff; eauto.
      intuition.
      eapply Disjoint_exports_impl_imports; eauto.
      split; eauto.
      eapply MapsTo_In; eauto.
      nintro.
      eapply Disjoint_total_exports_impl_imports; eauto.
      split; eauto.
      eapply MapsTo_In; eauto.
      eapply find_1.
      eapply diff_mapsto_iff.
      split.
      generalize ModulesNotEmpty; intro HH.
      eapply not_nil_cons in HH.
      openhyp.
      eapply update_all_intro.
      eapply AllCompat_imports.
      eapply in_map.
      rewrite H1; intuition.
      unfold StubMake.get_module_Imports.
      eapply diff_mapsto_iff.
      split.
      eapply update_mapsto_iff.
      right.
      split.
      eapply update_mapsto_iff.
      eauto.
      nintro.
      eapply Disjoint_impl_imports_foreign_imports; eauto.
      rewrite H1; intuition.
      split; eauto.
      eapply MapsTo_In; eauto.
      nintro.
      eapply Disjoint_exports_foreign_imports; eauto.
      rewrite H1; intuition.
      split; eauto.
      eapply MapsTo_In; eauto.
      nintro.
      eapply Disjoint_total_exports_foreign_imports; eauto.
      split; eauto.
      eapply MapsTo_In; eauto.
    Qed.

    (* Since modules <> nil, dummy will never be used. *)
    Definition dummy := @StructuredModule.bmodule_ nil "" nil.

    Definition link_all ls := fold_right_2 link dummy ls.
    Hint Extern 1 => reflexivity.

    Lemma link_all_ok :
      forall (ms : list GoodModule),
        let linked := link_all (List.map do_make_module ms) in
        let module_names := List.map MName ms in
        let linked_module_names := to_set module_names in
        let linked_exports := update_all (List.map get_module_Exports ms) in
        let linked_imports := update_all (List.map get_module_Imports ms) - linked_exports in
        ms <> nil ->
        incl ms modules ->
        List.NoDup module_names ->
        moduleOk linked /\
        SS.Equal (Modules linked) linked_module_names /\
        Exports linked === linked_exports /\
        Imports linked === linked_imports.
    Proof.
      Opaque make_module.
      unfold link_all.
      induction ms; simpl; intros.
      intuition.
      destruct ms; simpl in *.

      descend.
      eapply make_module_ok; eauto.
      intuition.
      rewrite make_module_Modules by intuition.
      setoid_rewrite of_list_singleton.
      eauto.
      rewrite make_module_Exports by intuition.
      rewrite update_all_single.
      eauto.
      rewrite make_module_Imports by intuition.
      repeat rewrite update_all_single.
      rewrite Disjoint_diff_no_effect.
      eauto.
      symmetry.
      eapply Disjoint_exports_imports; intuition.

      simpl in *.
      destruct IHms.
      intuition.
      incl_tran_cons.
      inversion H1; subst; eauto.
      openhyp.

      descend.
      eapply linkOk.
      eapply make_module_ok; eauto.
      intuition.
      eapply H2.

      eapply inter_is_empty_iff.
      rewrite H3.
      setoid_rewrite of_list_cons.
      rewrite make_module_Modules by intuition.
      eapply Disjoint_union.
      split.
      eapply Disjoint_singletons.
      inversion H1; subst.
      eapply NoDup_cons_cons.
      eauto.
      eapply Disjoint_singleton.
      inversion H1; subst.
      not_not.
      eapply of_list_spec in H6.
      intuition.

      eapply importsOk_Compat.
      rewrite H4.
      rewrite make_module_Imports by intuition.
      eapply to_blm_Compat.
      eapply compat_imports_exports with (ms := g :: ms); eauto.
      eapply importsOk_Compat.
      rewrite H5.
      rewrite make_module_Exports by intuition.
      eapply to_blm_Compat.
      symmetry.
      eapply compat_exports_imports with (ms := g :: ms); eauto.
      eapply importsOk_Compat.
      rewrite H5.
      rewrite make_module_Imports by intuition.
      eapply to_blm_Compat.
      eapply compat_imports_imports with (ms := g :: ms); eauto.

      rewrite H3.
      rewrite make_module_Modules by intuition.
      repeat setoid_rewrite of_list_cons.
      repeat setoid_rewrite P.add_union_singleton.
      eapply Equal_Subset_iff; split; subset_solver.
      rewrite XCAP_union_update.
      rewrite H4.
      repeat rewrite update_all_cons.
      set (_ + update_all _).
      rewrite Disjoint_update_sym.
      rewrite to_blm_update.
      eapply LabelMapFacts.update_m; eauto.
      eapply make_module_Exports; intuition.
      unfold t0; clear t0.
      rewrite <- update_all_cons.
      eapply Disjoint_exports with (ms := g :: ms); eauto.
      rewrite XCAP_union_update.
      repeat rewrite XCAP_diff_diff.
      rewrite H5.
      rewrite H4.
      rewrite make_module_Imports by intuition.
      rewrite make_module_Exports by intuition.
      repeat rewrite <- to_blm_diff.
      rewrite <- to_blm_update.
      eapply to_blm_Equal.
      repeat rewrite update_all_cons with (m := get_module_Imports a).
      repeat rewrite update_all_cons with (m := get_module_Exports a).
      eapply combine_imports_exports with (ms := g :: ms); eauto.
    Qed.

    Definition ms := List.map do_make_module modules.

    Definition m := link_all ms.

    (* Interface *)

    Theorem module_ok : moduleOk m.
      unfold m.
      unfold ms.
      eapply link_all_ok; intuition.
    Qed.

    Theorem module_imports : Imports m === final_imports.
      edestruct link_all_ok; eauto.
      intuition.
      openhyp.
      unfold m.
      rewrite H2.
      eapply to_blm_Equal.
      eapply final_imports_correct.
    Qed.

    Theorem module_exports : Exports m === total_exports.
      edestruct link_all_ok; eauto.
      intuition.
      openhyp.
      unfold m.
      rewrite H1.
      eapply to_blm_Equal.
      eauto.
    Qed.

    Theorem module_module_names : SS.Equal (Modules m) (to_set module_names).
      edestruct link_all_ok; eauto.
      intuition.
      openhyp.
      unfold m.
      rewrite H0.
      eauto.
    Qed.

  End TopSection.

End Make.
