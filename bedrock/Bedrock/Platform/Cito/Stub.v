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
  Require Import Bedrock.Platform.Cito.NameDecoration.
  Require Import Bedrock.Platform.Wrap.
  Require Import Bedrock.Platform.Cito.GeneralTactics.

  Require Import Bedrock.Platform.Cito.CompileFuncSpec.
  Module Import CompileFuncSpecMake := Make E M.
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

    Notation exports := (exports_IFS modules).

    Definition accessible_labels := keys imports ++ keys exports.

    Notation func_spec := (func_spec modules imports).

    Definition func_spec_IFS id (spec : InternalFuncSpec) := func_spec id spec.

    Definition bimports_base : list import :=
      elements
        (mapi foreign_func_spec imports) ++
      elements
        (mapi func_spec_IFS exports).

    Import ListNotations.
    Import FMapNotations.
    Open Scope fmap.

    Notation get_module_impl_Imports := module_impl_exports.
    Notation total_exports := (LinkSpecMake2.exports modules imports).
    Notation foreign_imports := (LinkSpecMake2.imports imports).
    Notation get_module_Exports := (module_exports modules imports).

    Definition get_module_Imports m := total_exports + foreign_imports + get_module_impl_Imports m - get_module_Exports m.

    Section module.

      Variable m : GoodModule.

      Hypothesis in_modules : List.In m modules.

      Section f.

        Variable f : GoodFunction.

        Section body.

          Variable im : LabelMap.t assert.

          Variable im_g : importsGlobal im.

          Definition mod_name := MName m.

          Definition tgt := impl_label mod_name (FName f).

          Definition body :=
            @Seq_ _ im_g mod_name
                  (AssertStar_ im mod_name accessible_labels (CompileFuncSpecMake.spec f))
                  (Goto_ im_g mod_name tgt).

        End body.

        Definition make_stub : function (MName m) :=
          (FName f, func_spec (MName m, FName f) f, body).

      End f.

      Notation Func_to_impl_import := func_impl_export.

      Definition bimports : list import :=
        bimports_base ++ List.map (Func_to_impl_import m) (Functions m).

      Definition stubs := List.map make_stub (Functions m).

      Definition bexports := List.map (@func_to_import _) stubs.

      Definition bimports_diff_bexports := diff_map bimports bexports.

      Definition make_module := StructuredModule.bmodule_ bimports_diff_bexports stubs.

      Require Import Bedrock.Platform.Cito.GeneralTactics2.

      Hint Extern 1 => reflexivity.

      Require Import Coq.Lists.SetoidList.

      Lemma In_exports : forall l, In l exports -> exists m f, List.In m modules /\ List.In f (Functions m) /\ l = (MName m, FName f).
        intros.
        eapply In_to_map in H.
        unfold InKey in *.
        eapply in_map_iff in H.
        openhyp.
        rewrite <- H in *.
        clear H.
        rename H0 into H.
        eapply In_app_all_elim in H.
        openhyp.
        eapply in_map_iff in H0.
        openhyp.
        rewrite <- H0 in *.
        unfold module_exports_IFS in *.
        eapply in_map_iff in H.
        openhyp.
        rewrite <- H in *.
        unfold MName; simpl in *.
        descend.
        eauto.
        eauto.
        eauto.
      Qed.

      Lemma NoDupKey_bimports_base : NoDupKey bimports_base.
        eapply NoDupKey_NoDup_fst.
        unfold bimports_base.
        erewrite map_app.
        eapply NoDup_app.
        eapply NoDupKey_NoDup_fst.
        eapply elements_3w.
        eapply NoDupKey_NoDup_fst.
        eapply elements_3w.
        eapply Disjoint_map with (f := fst).
        eapply Disjoint_symm.
        eapply Disjoint_incl.
        eauto.

        unfold incl.
        intros.
        eapply in_map_iff in H.
        openhyp.
        rewrite <- H in *.
        clear H.
        rename H0 into H.
        eapply In_fst_elements_In in H.
        eapply mapi_in_iff with (m := exports) in H.
        eapply In_exports in H.
        openhyp.
        rewrite H1 in *; simpl in *.
        unfold MName; simpl in *.
        eapply in_map_iff.
        eexists.
        eauto.

        unfold incl.
        intros.
        rewrite <- map_map.
        eapply incl_map in H.
        eauto.
        unfold incl.
        intros.
        eapply In_fst_elements_In.
        eapply In_fst_elements_In in H0.
        eapply mapi_in_iff; eauto.
      Qed.

      Lemma impl_label_is_injection : forall mn, IsInjection (impl_label mn).
        unfold IsInjection, impl_label; intuition.
      Qed.

      Lemma GoodModule_GoodName : forall m : GoodModule, IsGoodModuleName (MName m).
        intros m0; destruct m0; simpl; eauto.
      Qed.

      Lemma In_bimports_base_fst : forall x, List.In x bimports_base ->  In (fst x) imports \/ exists m f, List.In m modules /\ List.In f (Functions m) /\ fst x = (MName m, FName f).
        intros.
        unfold bimports_base in *.
        eapply in_app_or in H.
        openhyp.
        left.
        destruct x.
        simpl.
        eapply InA_eqke_In in H.
        eapply elements_2 in H.
        eapply mapi_in_iff.
        eexists.
        eauto.
        right.
        destruct x.
        simpl.
        eapply InA_eqke_In in H.
        eapply elements_2 in H.
        eapply MapsTo_In in H.
        eapply mapi_in_iff with (m := exports) in H.
        eapply In_exports; eauto.
      Qed.

      Lemma bimports_base_good_names : forall x, List.In x bimports_base -> IsGoodModuleName (fst (fst x)).
        intros.
        eapply In_bimports_base_fst in H.
        openhyp.
        eauto.
        rewrite H1 in *.
        simpl.
        eapply GoodModule_GoodName.
      Qed.

      Lemma NoDupKey_bimports : NoDupKey bimports.
        unfold bimports.
        eapply NoDupKey_app.
        eapply NoDupKey_bimports_base.
        eapply NoDupKey_NoDup_fst.
        erewrite map_map.
        unfold Func_to_impl_import.
        simpl.
        unfold FName.
        erewrite <- map_map.
        eapply Injection_NoDup.
        eapply impl_label_is_injection.
        eapply NoDupFuncNames.
        unfold DisjointKey.
        unfold InKey.
        intuition.
        erewrite map_map in H1.
        unfold Func_to_impl_import in *.
        simpl in *.
        eapply in_map_iff in H1.
        openhyp.
        rewrite <- H in *.
        eapply in_map_iff in H0.
        openhyp.
        eapply f_equal with (f := fst) in H0.
        unfold impl_label in *.
        simpl in *.
        eapply bimports_base_good_names in H2.
        eapply IsGoodModuleName_not_impl_module_name in H2.
        contradict H2.
        eexists.
        symmetry.
        eauto.
      Qed.

      Lemma GoodModule_NoDup_labels : forall a : GoodModule, List.NoDup (List.map (fun x : GoodFunction => (MName a, FName x)) (Functions a)).
        destruct a; simpl in *.
        unfold FName.
        eauto.
        generalize NoDupFuncNames; intro HH.
        eapply Injection_NoDup with (f := fun s => (Name, s)) in HH.
        rewrite map_map in HH.
        eauto.
        unfold IsInjection; intuition.
      Qed.

      Notation get_module_exports := module_exports_IFS.

      Lemma NoDupKey_app_all :
        forall ls : list GoodModule,
          List.NoDup (List.map MName ls) ->
          NoDupKey (app_all (List.map get_module_exports ls)).
        clear.
        induction ls; simpl; intros.
        econstructor.
        eapply NoDupKey_app.
        eapply NoDupKey_NoDup_fst.
        unfold get_module_exports.
        rewrite map_map.
        simpl.
        eapply GoodModule_NoDup_labels.
        eapply IHls.
        inversion H; subst.
        eauto.
        unfold DisjointKey.
        unfold InKey.
        intros.
        intuition.
        eapply in_map_iff in H1.
        openhyp.
        subst.
        unfold get_module_exports in H1.
        eapply in_map_iff in H1.
        openhyp.
        subst.
        rewrite map_app_all in H2.
        eapply In_app_all_elim in H2.
        openhyp.
        rewrite map_map in H2.
        simpl in *.
        unfold get_module_exports in H2.
        eapply in_map_iff in H2.
        openhyp.
        subst.
        rewrite map_map in H0.
        simpl in *.
        eapply in_map_iff in H0.
        openhyp.
        injection H0; intros; subst.
        rewrite <- H5 in *.
        eapply in_map with (f := MName) in H3.
        inversion H; subst.
        contradiction.
      Qed.

      Lemma incl_bexports_bimports : incl bexports bimports.
        unfold incl, bexports, stubs.
        intros.
        rewrite map_map in H.
        unfold func_to_import, make_stub in *.
        simpl in *.
        eapply in_map_iff in H.
        openhyp.
        rewrite <- H in *.
        clear H.
        unfold bimports.
        eapply in_or_app.
        left.
        unfold bimports_base.
        eapply in_or_app.
        right.
        eapply InA_eqke_In.
        eapply elements_1.
        unfold func_spec_IFS.
        eapply find_2.
        erewrite find_mapi.
        f_equal.
        instantiate (1 := x).
        reflexivity.
        eapply find_1.
        eapply MapsTo_to_map.
        eapply NoDupKey_app_all; eauto.
        eapply In_app_all_intro.
        Focus 2.
        eapply in_map_iff.
        eexists.
        eauto.
        unfold get_module_exports.
        eapply in_map_iff.
        eexists.
        eauto.
      Qed.

      Notation fs := (fs modules imports).
      Notation is_export := (is_export modules).
      Notation is_import := (is_import imports).

      Require Import Bedrock.Platform.Cito.Option.
      Require Import Bedrock.Platform.Cito.Label2WordFacts.

      Lemma fs_internal :
        forall stn p spec,
          fs stn p = Some (Internal spec) ->
          exists lbl : glabel,
            find lbl exports = Some spec /\
            Labels stn lbl = Some p.
      Proof.
        intros.
        unfold LinkSpec.fs in *.
        destruct (option_dec (is_export stn p)).
        {
          destruct s.
          rewrite e in H.
          injection H; intros.
          subst.
          unfold LinkSpec.is_export in *.
          eapply find_by_word_elements_elim; eauto.
        }
        rewrite e in H.
        destruct (is_import stn p); intuition.
        discriminate.
      Qed.

      Lemma augment_elim :
        forall imps specs stn (lbls : list glabel),
          augment imps specs stn lbls ->
          (forall x, List.In x lbls -> LabelMap.LabelMap.find (x : Labels.label) imps <> None) ->
          forall l p spec,
            List.In l lbls ->
            Labels stn l = Some p ->
            LabelMap.LabelMap.find (l : Labels.label) imps = Some spec ->
            specs p = Some spec.
      Proof.
        induction lbls; simpl; intros.
        intuition.
        destruct H1.
        subst.
        destruct l.
        unfold to_bedrock_label in *.
        simpl in *.
        rewrite H3 in H.
        openhyp.
        congruence.
        generalize H0; specialize (H0 a); intro.
        eapply ex_up in H0.
        openhyp.
        destruct a.
        unfold to_bedrock_label in *.
        simpl in *.
        rewrite H0 in H.
        openhyp.
        eauto.
        eauto.
      Qed.

      Lemma imports_bimports : forall k v, find k imports = Some v -> find_list k bimports = Some (foreign_func_spec k v).
        unfold bimports, bimports_base.
        intros.
        eapply NoDup_app_find_list.
        eapply NoDupKey_bimports.
        eapply NoDup_app_find_list.
        eapply NoDupKey_unapp1.
        eapply NoDupKey_bimports.
        unfold bimports, bimports_base.
        intuition.
        rewrite find_list_elements.
        eapply find_mapi; eauto.
      Qed.

      Corollary in_imports_in_bimports : forall x, In x imports -> List.In x (List.map fst bimports).
      unfold bimports, bimports_base.
      intros.
      erewrite map_app.
      eapply in_or_app.
      left.
      erewrite map_app.
      eapply in_or_app.
      left.
      eapply In_fst_elements_In.
      eapply mapi_in_iff; eauto.
      Qed.

      Lemma exports_bimports : forall k v, find k exports = Some v -> find_list k bimports = Some (func_spec k v).
        unfold bimports, bimports_base.
        intros.
        eapply NoDup_app_find_list.
        eapply NoDupKey_bimports.
        eapply NoDup_app_find_list_2.
        eapply NoDupKey_unapp1.
        eapply NoDupKey_bimports.
        unfold bimports, bimports_base.
        intuition.
        rewrite find_list_elements.
        unfold func_spec_IFS.
        erewrite find_mapi; eauto.
      Qed.

      Corollary in_exports_in_bimports : forall x, In x exports -> List.In x (List.map fst bimports).
      unfold bimports, bimports_base.
      intros.
      erewrite map_app.
      eapply in_or_app.
      left.
      erewrite map_app.
      eapply in_or_app.
      right.
      eapply In_fst_elements_In.
      eapply mapi_in_iff; eauto.
      Qed.

      Lemma NoDupKey_bexports : NoDupKey bexports.
        unfold bexports.
        unfold stubs.
        rewrite map_map.
        unfold func_to_import.
        unfold make_stub; simpl in *.
        eapply NoDupKey_NoDup_fst.
        rewrite map_map.
        simpl.
        eapply GoodModule_NoDup_labels.
      Qed.

      Lemma NoDup_union : NoDupKey (bimports_diff_bexports ++ bexports).
        unfold bimports_diff_bexports.
        eapply NoDupKey_app.
        eapply diff_NoDupKey.
        eapply NoDupKey_bimports.
        eapply NoDupKey_bexports.
        eapply diff_DisjointKey.
      Qed.

      Lemma Equal_union_bimports : Equal_map (bimports_diff_bexports ++ bexports) bimports.
        unfold bimports_diff_bexports.
        eapply diff_union.
        eapply NoDupKey_bimports.
        eapply NoDupKey_bexports.
        eapply incl_bexports_bimports.
      Qed.

      Definition full_imports := fullImports bimports_diff_bexports stubs.

      Lemma fullImports_eq_bimports : forall (k : glabel), LabelMap.LabelMap.find (k : Labels.label) full_imports = find_list k bimports.
        intros.
        unfold full_imports in *.
        erewrite fullImports_spec.
        eapply Equal_union_bimports.
        eapply NoDup_union.
      Qed.

      Require Import Bedrock.Platform.Cito.SetoidListFacts.

      Corollary bimports_fullImports : forall (x : glabel), List.In x (List.map fst bimports) -> LabelMap.LabelMap.find (x : label) full_imports <> None.
      Proof.
        intros.
        specialize In_find_list_not_None; intros.
        eapply InA_eq_In_iff in H.
        eapply H0 in H.
        eapply ex_up in H.
        openhyp.
        rewrite fullImports_eq_bimports.
        intuition.
      Qed.

      Lemma accessible_labels_subset_fullImports :
        forall x : glabel,
          List.In x accessible_labels ->
          LabelMap.LabelMap.find (x : Labels.label) full_imports <> None.
      Proof.
        unfold accessible_labels.
        intros.
        eapply in_app_or in H.
        destruct H.

        unfold keys in *; eapply In_fst_elements_In in H.
        eapply in_imports_in_bimports in H.
        eapply bimports_fullImports; eauto.

        unfold keys in *; eapply In_fst_elements_In in H.
        eapply in_exports_in_bimports in H.
        eapply bimports_fullImports; eauto.
      Qed.

      Lemma exports_accessible_labels : forall l, find l exports <> None -> List.In l accessible_labels.
        unfold accessible_labels.
        intros.
        eapply in_or_app.
        right.
        unfold keys in *; eapply In_fst_elements_In.
        eapply In_find_not_None; eauto.
      Qed.

      Lemma exports_fullImports : forall (l : glabel) spec, find l exports = Some spec -> LabelMap.LabelMap.find (l : label) full_imports = Some (func_spec l spec).
        intros.
        rewrite fullImports_eq_bimports.
        eapply exports_bimports; eauto.
      Qed.

      Lemma tgt_fullImports : forall f, List.In f (Functions m) -> LabelMap.LabelMap.find (tgt f : Labels.label) full_imports = Some (CompileFuncSpecMake.spec f).
        intros.
        rewrite fullImports_eq_bimports.
        unfold bimports, bimports_base.
        eapply NoDup_app_find_list_2.
        eapply NoDupKey_bimports.
        unfold tgt.
        unfold mod_name.
        eapply In_find_list_Some.
        eapply NoDupKey_unapp2.
        eapply NoDupKey_bimports.
        unfold bimports, bimports_base.
        intuition.
        unfold Func_to_impl_import in *; simpl in *.
        eapply in_map with (f := fun x => Func_to_impl_import m x) in H.
        eapply InA_eqke_In.
        eauto.
      Qed.

      Lemma fs_foreign :
        forall stn p spec,
          fs stn p = Some (Foreign spec) ->
          exists lbl : glabel,
            find lbl imports = Some spec /\
            Labels stn lbl = Some p.
      Proof.
        intros.
        unfold LinkSpec.fs in *.
        destruct (option_dec (is_export stn p)).
        {
          destruct s.
          rewrite e in H.
          intuition.
          discriminate.
        }
        rewrite e in H.
        destruct (option_dec (is_import stn p)).
        {
          destruct s.
          rewrite e0 in H.
          injection H; intros; subst.
          unfold LinkSpec.is_import in *.
          eapply find_by_word_elements_elim; eauto.
        }
        rewrite e0 in H; discriminate.
      Qed.

      Lemma imports_accessible_labels : forall l, find l imports <> None -> List.In l accessible_labels.
        unfold accessible_labels.
        intros.
        eapply in_or_app.
        left.
        unfold keys in *; eapply In_fst_elements_In.
        eapply In_find_not_None; eauto.
      Qed.

      Lemma imports_fullImports : forall (l : glabel) spec, find l imports = Some spec -> LabelMap.LabelMap.find (l : label) full_imports = Some (foreign_func_spec l spec).
        intros.
        rewrite fullImports_eq_bimports.
        eapply imports_bimports; eauto.
      Qed.

      Lemma specs_internal :
        forall specs stn p spec,
          augment full_imports specs stn accessible_labels ->
          fs stn p = Some (Internal spec) ->
          exists id, specs p = Some (func_spec id spec).
      Proof.
        intros.
        eapply fs_internal in H0.
        openhyp.
        eapply augment_elim in H; eauto.
        eapply accessible_labels_subset_fullImports.
        eapply exports_accessible_labels.
        intuition.
        eapply exports_fullImports; eauto.
      Qed.

      Lemma specs_foreign :
        forall specs stn p spec,
          augment full_imports specs stn accessible_labels ->
          fs stn p = Some (Foreign spec) ->
          exists lbl, specs p = Some (foreign_func_spec lbl spec).
      Proof.
        intros.
        eapply fs_foreign in H0.
        openhyp.
        eapply augment_elim in H; eauto.
        eapply accessible_labels_subset_fullImports.
        eapply imports_accessible_labels.
        intuition.
        eapply imports_fullImports; eauto.
      Qed.

      Lemma fs_funcs_ok :
        forall specs stn,
          augment full_imports specs stn accessible_labels ->
          interp specs (funcs_ok stn fs).
      Proof.
        unfold funcs_ok.
        post; descend.

        apply injL; intro.
        Opaque internal_spec.
        eapply specs_internal in H; eauto.
        post; descend.
        eauto.

        unfold LinkSpecMake2.func_spec.
        unfold name_marker.
        unfold spec_without_funcs_ok at 2.
        step auto_ext.
        step auto_ext.
        Transparent internal_spec.
        step auto_ext.
        rewrite sepFormula_eq; apply Imply_refl.

        apply injL; intro.
        Opaque InvMake2.foreign_spec.
        eapply specs_foreign in H; eauto; openhyp.
        post; descend.
        instantiate (1 := foreign_func_spec x1 x0).
        eauto.

        unfold foreign_func_spec.
        unfold name_marker.
        step auto_ext.
        eauto.
        Transparent InvMake2.foreign_spec.
        step auto_ext.
        rewrite sepFormula_eq; apply Imply_refl.
      Qed.

      Lemma InKey_exports_elim : forall A (f : _ -> A) (ms : list GoodModule) m lbl, List.In m ms -> List.NoDup (List.map MName ms) -> fst lbl = MName m -> InKey lbl (app_all (List.map get_module_exports ms)) -> InKey lbl (List.map (fun x : GoodFunction => (MName m, FName x, f x)) (Functions m)).
        clear.
        induction ms; simpl; intros.
        unfold InKey in *; simpl in *; intuition.
        destruct H.
        subst.
        eapply inkey_app_or in H2.
        destruct H2.
        unfold get_module_exports in *.
        unfold InKey in *.
        rewrite map_map in *.
        simpl in *.
        eauto.
        unfold InKey in H.
        eapply in_map_iff in H.
        openhyp.
        subst.
        eapply In_app_all_elim in H2.
        openhyp.
        eapply in_map_iff in H2.
        openhyp.
        subst.
        unfold get_module_exports in *.
        eapply in_map_iff in H.
        openhyp.
        subst.
        simpl in *.
        rewrite <- H1 in *.
        inversion H0; subst.
        eapply in_map with (f := MName) in H3.
        contradiction.
        eapply inkey_app_or in H2.
        destruct H2.
        unfold InKey in H2.
        eapply in_map_iff in H2.
        openhyp.
        subst.
        unfold get_module_exports in H3.
        eapply in_map_iff in H3.
        openhyp.
        subst.
        simpl in *.
        rewrite H1 in *.
        inversion H0; subst.
        eapply in_map with (f := MName) in H.
        contradiction.
        eapply IHms; eauto.
        inversion H0; subst.
        eauto.
      Qed.

      Require Import Bedrock.Platform.Cito.StringFacts2.

      Require Import Bedrock.Platform.Cito.NameVC.

      Lemma module_name_not_in_bimports_diff_bexports : ~ List.In (MName m) (List.map fst2 bimports_diff_bexports).
        intuition.
        unfold fst_2 in *.
        rewrite <- map_map in H.
        eapply in_map_iff in H.
        openhyp.
        destruct x; simpl in *.
        subst.
        unfold bimports_diff_bexports in *.
        eapply diff_In in H0.
        openhyp.
        contradict H0.
        unfold bimports in *.
        eapply inkey_app_or in H.
        unfold Func_to_impl_import in *.
        openhyp.
        unfold bimports_base in *.
        eapply inkey_app_or in H.
        openhyp.
        eapply In_fst_elements_In in H.
        eapply mapi_in_iff with (m := imports) in H.
        unfold Disjoint in *.
        exfalso.
        eapply NoSelfImport with (e := MName m).
        split.
        eapply in_map; eauto.

        eapply In_fst_elements_In in H.
        eapply in_map with (f := fst) in H.
        simpl in *.
        rewrite map_map in H.
        eauto.

        eapply In_fst_elements_In in H.
        eapply mapi_in_iff with (m := exports) in H.
        eapply In_to_map in H.
        unfold bexports.
        unfold func_to_import.
        unfold stubs.
        unfold make_stub.
        rewrite map_map.
        simpl in *.
        eapply InKey_exports_elim; eauto.

        unfold InKey in H.
        rewrite map_map in H.
        simpl in *.
        unfold impl_label in *.
        eapply in_map_iff in H.
        openhyp.
        injection H; intros.
        contradict H2.
        eapply prefix_neq.
        eapply cito_module_impl_prefix_not_empty; eauto.
      Qed.

      Lemma module_name_not_in_imports : NameNotInImports (MName m) bimports_diff_bexports.
        eapply NotIn_NameNotInImports.
        eapply module_name_not_in_bimports_diff_bexports.
      Qed.

      Lemma no_dup_func_names : NoDupFuncNames stubs.
        eapply NoDup_NoDupFuncNames.
        unfold stubs.
        rewrite map_map.
        unfold make_stub; simpl in *.
        destruct m; simpl in *.
        eauto.
      Qed.

      Lemma In_exports_module_name : forall k m, In k (get_module_Exports m) -> fst k = MName m.
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

      Lemma Disjoint_exports_foreign_imports : forall m, List.In m modules -> Disjoint (get_module_Exports m) foreign_imports.
        intros.
        unfold Disjoint.
        intros.
        unfold ListFacts1.Disjoint in *.
        specialize (NoSelfImport (fst k)).
        not_not.
        openhyp.
        eapply In_exports_module_name in H0.
        rewrite H0 in *.
        split.
        eapply in_map; eauto.
        eapply mapi_in_iff with (m := imports) in H1.
        eapply In_MapsTo in H1.
        openhyp.
        eapply in_map_iff.
        exists (k, x).
        split.
        eauto.
        eapply InA_eqke_In.
        eapply elements_1; eauto.
      Qed.
      Existing Instance Disjoint_rel_Symmetric.

      Lemma Disjoint_many_exports_foreign_imports : forall ms, incl ms modules -> Disjoint (update_all (List.map get_module_Exports ms)) foreign_imports.
        intros.
        symmetry.
        eapply Disjoint_update_all.
        eapply Forall_forall.
        intros.
        eapply in_map_iff in H0.
        openhyp.
        subst.
        symmetry.
        eapply Disjoint_exports_foreign_imports; eauto.
      Qed.

      Lemma Compat_many_exports_foreign_imports : forall ms, incl ms modules -> Compat (update_all (List.map get_module_Exports ms)) foreign_imports.
        intros.
        eapply Disjoint_Compat.
        eapply Disjoint_many_exports_foreign_imports; eauto.
      Qed.

      Lemma Disjoint_total_exports_foreign_imports : Disjoint total_exports foreign_imports.
        unfold LinkSpecMake2.exports.
        eapply Disjoint_many_exports_foreign_imports; intuition.
      Qed.

      Lemma Compat_total_exports_foreign_imports : Compat total_exports foreign_imports.
        unfold LinkSpecMake2.exports.
        eapply Compat_many_exports_foreign_imports; intuition.
      Qed.

      Require Import Coq.Classes.Morphisms.
      Require Import Coq.Setoids.Setoid.

      Lemma Equal_get_module_Exports : forall m, mapi func_spec_IFS (of_list (get_module_exports m)) == get_module_Exports m.
        intros.
        unfold module_exports.
        unfold to_map.
        unfold get_module_exports.
        rewrite mapi_of_list.
        rewrite map_map.
        simpl.
        eauto.
      Qed.

      Lemma exports_Equal_total_exports : mapi func_spec_IFS exports == total_exports.
        unfold exports_IFS.
        unfold LinkSpecMake2.exports.
        unfold to_map.
        rewrite app_all_update_all.
        rewrite mapi_update_all_comm.
        rewrite map_map.
        rewrite map_map.
        eapply update_all_Equal.
        eapply Forall2_map.
        unfold pointwise_relation.
        eapply Equal_get_module_Exports.
        eapply NoDupKey_app_all; eauto.
      Qed.

      Lemma bimports_base_Equal_update : of_list bimports_base == total_exports + foreign_imports.
        intros.
        rewrite Compat_update_sym.
        Focus 2.
        eapply Compat_total_exports_foreign_imports.
        unfold bimports_base.
        rewrite of_list_app.
        rewrite of_list_3.
        rewrite of_list_3.
        rewrite exports_Equal_total_exports.
        reflexivity.
        eapply NoDupKey_bimports_base; eauto.
      Qed.

      Lemma bimports_Equal_update_update : of_list bimports == total_exports + foreign_imports + get_module_impl_Imports m.
        intros.
        unfold bimports.
        rewrite of_list_app.
        rewrite bimports_base_Equal_update.
        reflexivity.
        eapply NoDupKey_bimports; eauto.
      Qed.

      Lemma bexports_Equal_exports : of_list bexports == get_module_Exports m.
        intros.
        unfold bexports.
        unfold stubs.
        unfold make_stub.
        rewrite map_map.
        unfold func_to_import.
        simpl.
        unfold module_exports.
        reflexivity.
      Qed.

      Definition get_module_exports_map m := of_list (get_module_exports m).

      Lemma exports_alt : exports == update_all (List.map get_module_exports_map modules).
        unfold exports_IFS.
        unfold get_module_exports_map.
        rewrite app_all_update_all.
        rewrite map_map.
        eauto.
        eapply NoDupKey_app_all; eauto.
      Qed.

      Lemma NoDupKey_get_module_exports : forall m, NoDupKey (get_module_exports m).
        intros.
        eapply NoDupKey_NoDup_fst.
        unfold get_module_exports.
        rewrite map_map.
        simpl.
        eapply GoodModule_NoDup_labels.
      Qed.

      Lemma AllCompat_exports : AllCompat (List.map get_module_exports_map modules).
        unfold get_module_exports_map.
        rewrite <- map_map.
        eapply NoDupKey_app_all_AllCompat.
        eapply NoDupKey_app_all; eauto.
      Qed.

      Lemma exports_mapsto_iff : forall l v, MapsTo l v exports <-> exists m f, List.In m modules /\ List.In f (Functions m) /\ l = (MName m, FName f) /\ v = f.
        split; intros.
        rewrite exports_alt in H.
        eapply update_all_elim in H.
        openhyp.
        eapply in_map_iff in H; openhyp; subst.
        unfold get_module_exports_map in *.
        eapply of_list_1 with (l := get_module_exports _) in H0.
        eapply InA_eqke_In in H0.
        unfold get_module_exports in *.
        eapply in_map_iff in H0; openhyp; subst.
        injection H; intros; subst.
        descend; eauto.
        eapply NoDupKey_get_module_exports.

        openhyp.
        subst.
        rewrite exports_alt.
        unfold get_module_exports_map.
        eapply update_all_intro.
        eapply AllCompat_exports.
        eapply in_map; eauto.
        eapply of_list_1.
        eapply NoDupKey_get_module_exports.
        eapply InA_eqke_In.
        unfold get_module_exports.
        eapply in_map_iff.
        eexists; eauto.
      Qed.

      Definition proj_imply1 pc state G (p : propX pc state G) : propX pc state G :=
        match p with
          | Imply _ p1 _ => p1
          | p' => p'
        end.

      Definition proj_and1 pc state G (p : propX pc state G) : propX pc state G :=
        match p with
          | And _ p1 _ => p1
          | p' => p'
        end.

      Definition unexX pc state G (p : propX pc state G) : { T : Type & T -> propX pc state G } :=
        match p with
          | PropX.Exists _ _ p1 => existT _ _ p1
          | p' => existT (fun T => T -> propX pc state _) _ (fun _ : unit => Inj True)
        end.

      Require Import Coq.Logic.Eqdep.

      Definition uninjX pc state G (p : propX pc state G) : Prop :=
        match p with
          | Inj _ P => P
            | _ => True
          end.

      Lemma name_marker_injective : forall l1 l2, name_marker l1 = name_marker l2 -> l1 = l2.
        intros.
        unfold name_marker in *.
        apply (f_equal (@unexX _ _ _)) in H; simpl in H.
        apply inj_pair2 in H.
        apply (f_equal (fun f => f l1)) in H.
        apply (f_equal (@uninjX _ _ _)) in H; simpl in H.
        assert (l1 = l1) by eauto.
        rewrite H in H0.
        eauto.
      Qed.

      Lemma func_spec_eq_id_eq : forall (stn : settings) l1 l2 f1 f2, func_spec l1 f1 = func_spec l2 f2 -> l1 = l2.
        intros.
        unfold LinkSpecMake2.func_spec in *.
        evar (st : (ST.settings * state)%type).
        apply (f_equal (fun f => f st)) in H.
        apply (f_equal (@proj_imply1 _ _ _)) in H; simpl in H.
        apply (f_equal (@proj_and1 _ _ _)) in H; simpl in H.
        eapply name_marker_injective; eauto.
        Grab Existential Variables.
        repeat (econstructor; eauto).
      Qed.

      Lemma foreign_func_spec_eq_id_eq : forall (stn : settings) l1 l2 f1 f2, foreign_func_spec l1 f1 = foreign_func_spec l2 f2 -> l1 = l2.
        intros.
        unfold foreign_func_spec in *.
        evar (st : (ST.settings * state)%type).
        apply (f_equal (fun f => f st)) in H.
        apply (f_equal (@proj_and1 _ _ _)) in H; simpl in H.
        eapply name_marker_injective; eauto.
        Grab Existential Variables.
        repeat (econstructor; eauto).
      Qed.

      Lemma func_spec_neq_foreign_func_spec : forall (stn : settings) l1 l2 f1 f2, func_spec l1 f1 <> foreign_func_spec l2 f2.
        intros.
        nintro.
        unfold LinkSpecMake2.func_spec, foreign_func_spec in H.
        evar (st : (ST.settings * state)%type).
        apply (f_equal (fun f => f st)) in H.
        discriminate.
        Grab Existential Variables.
        repeat (econstructor; eauto).
      Qed.

      Lemma augment_injective_exports : forall specs stn, augment (fullImports bimports_diff_bexports stubs) specs stn accessible_labels -> forall (l1 l2 : glabel), In l1 exports -> In l2 exports -> forall p, Labels stn l1 = Some p -> Labels stn l2 = Some p -> l1 = l2.
        intros.
        generalize H; intro.
        eapply In_MapsTo in H0; openhyp.
        eapply In_MapsTo in H1; openhyp.
        eapply augment_elim in H.
        2 : eapply accessible_labels_subset_fullImports.
        Focus 2.
        eapply exports_accessible_labels.
        eapply in_find_iff.
        eapply MapsTo_In; eauto.
        2 : eauto.
        Focus 2.
        eapply exports_fullImports.
        eapply find_1; eauto.

        eapply augment_elim in H4.
        2 : eapply accessible_labels_subset_fullImports.
        Focus 2.
        eapply exports_accessible_labels.
        eapply in_find_iff.
        eapply MapsTo_In.
        eapply H0.
        2 : eauto.
        Focus 2.
        eapply exports_fullImports.
        eapply find_1; eauto.

        rewrite H4 in H.
        injection H; intros.
        eapply func_spec_eq_id_eq; eauto.
      Qed.

      Lemma augment_injective_imports : forall specs stn, augment (fullImports bimports_diff_bexports stubs) specs stn accessible_labels -> forall (l1 l2 : glabel), In l1 imports -> In l2 imports -> forall p, Labels stn l1 = Some p -> Labels stn l2 = Some p -> l1 = l2.
        intros.
        generalize H; intro.
        eapply In_MapsTo in H0; openhyp.
        eapply In_MapsTo in H1; openhyp.
        eapply augment_elim in H.
        2 : eapply accessible_labels_subset_fullImports.
        Focus 2.
        eapply imports_accessible_labels.
        eapply in_find_iff.
        eapply MapsTo_In; eauto.
        2 : eauto.
        Focus 2.
        eapply imports_fullImports.
        eapply find_1; eauto.

        eapply augment_elim in H4.
        2 : eapply accessible_labels_subset_fullImports.
        Focus 2.
        eapply imports_accessible_labels.
        eapply in_find_iff.
        eapply MapsTo_In.
        eapply H0.
        2 : eauto.
        Focus 2.
        eapply imports_fullImports.
        eapply find_1; eauto.

        rewrite H4 in H.
        injection H; intros.
        eapply foreign_func_spec_eq_id_eq; eauto.
      Qed.

      Lemma imports_Disjoint_exports : forall k, ~ (In k imports /\ In k exports).
        intros.
        nintro.
        openhyp.
        eapply Disjoint_total_exports_foreign_imports.
        split.
        rewrite <- exports_Equal_total_exports.
        eapply mapi_in_iff; eauto.
        unfold LinkSpecMake2.imports.
        eapply mapi_in_iff; eauto.
      Qed.

      Lemma augment_injective_exports_imports : forall specs stn, augment (fullImports bimports_diff_bexports stubs) specs stn accessible_labels -> forall (l1 l2 : glabel) p1 p2, In l1 exports -> In l2 imports -> Labels stn l1 = Some p1 -> Labels stn l2 = Some p2 -> p1 <> p2.
        intros.
        nintro.
        subst.

        generalize H; intro.
        eapply In_MapsTo in H0; openhyp.
        eapply In_MapsTo in H1; openhyp.
        eapply augment_elim in H.
        2 : eapply accessible_labels_subset_fullImports.
        Focus 2.
        eapply imports_accessible_labels.
        eapply in_find_iff.
        eapply MapsTo_In; eauto.
        2 : eauto.
        Focus 2.
        eapply imports_fullImports.
        eapply find_1; eauto.

        eapply augment_elim in H4.
        2 : eapply accessible_labels_subset_fullImports.
        Focus 2.
        eapply exports_accessible_labels.
        eapply in_find_iff.
        eapply MapsTo_In.
        eauto.
        2 : eauto.
        Focus 2.
        eapply exports_fullImports.
        eapply find_1; eauto.

        rewrite H4 in H.
        injection H; intros.
        eapply func_spec_neq_foreign_func_spec; eauto.
      Qed.

      Lemma is_export_iff : forall specs stn, augment (fullImports bimports_diff_bexports stubs) specs stn accessible_labels -> forall p v, is_export stn p = Some v <-> exists (lbl : glabel), MapsTo lbl v exports /\ Labels stn lbl = Some p.
        intro.
        intro.
        intro HH.
        split; intros.
        {
          unfold LinkSpec.is_export in *.
          eapply find_by_word_elements_elim in H; eauto.
          openhyp.
          eexists; split.
          - eapply find_mapsto_iff; eauto.
          - eauto.
        }
        openhyp.
        unfold LinkSpec.is_export in *.
        eapply find_by_word_elements_intro; eauto.
        - intros lbl1 lbl2 p' Hin1 Hin2 Hp1 Hp2.
          eapply augment_injective_exports; eauto.
        - eapply find_mapsto_iff; eauto.
      Qed.

      Lemma is_import_iff : forall specs stn, augment (fullImports bimports_diff_bexports stubs) specs stn accessible_labels -> forall p v, is_import stn p = Some v <-> exists (lbl : glabel), MapsTo lbl v imports /\ Labels stn lbl = Some p.
        intro.
        intro.
        intro HH.
        split; intros.
        {
          unfold LinkSpec.is_import in *.
          eapply find_by_word_elements_elim in H; eauto.
          openhyp.
          eexists; split.
          - eapply find_mapsto_iff; eauto.
          - eauto.
        }

        openhyp.
        unfold LinkSpec.is_import in *.
        eapply find_by_word_elements_intro; eauto.
        - intros lbl1 lbl2 p' Hin1 Hin2 Hp1 Hp2.
          eapply augment_injective_imports; eauto.
        - eapply find_mapsto_iff; eauto.
      Qed.

      Notation fs_good_to_use := (LinkSpec.fs_good_to_use modules imports fs).

      Lemma augment_fs_good_to_use : forall specs stn, augment (fullImports bimports_diff_bexports stubs) specs stn accessible_labels -> fs_good_to_use stn.
        split; intros; unfold label_mapsto in *.

        (* elimination *)
        destruct spec0.
        eapply fs_foreign in H0.
        openhyp.
        descend.
        eauto.
        right.
        descend.
        eauto.
        eauto.
        eapply fs_internal in H0.
        openhyp.
        descend.
        eauto.
        eapply find_2 in H0.
        eapply exports_mapsto_iff in H0.
        openhyp; subst.
        left.
        descend; eauto.

        (* introduction *)
        openhyp.

        (* in exports *)
        subst.
        unfold LinkSpec.fs.
        assert (is_export stn p = Some (x2 : InternalFuncSpec)).
        eapply is_export_iff; eauto.
        descend; eauto.
        eapply exports_mapsto_iff.
        descend; eauto.

        rewrite H1.
        eauto.

        (* in imports *)
        subst.
        unfold LinkSpec.fs.
        destruct (option_dec (is_export stn p)).
        destruct s.
        rewrite e.
        eapply is_export_iff in e; eauto.
        openhyp.

        exfalso.
        eapply find_2 in H2.
        eapply augment_injective_exports_imports.
        2 : eapply MapsTo_In; eauto.
        2 : eapply MapsTo_In; eauto.
        eauto.
        eauto.
        eauto.
        eauto.

        rewrite e.
        assert (is_import stn p = Some x0).

        eapply is_import_iff; eauto.
        descend; eauto.
        eapply find_2; eauto.
        rewrite H1.
        eauto.
      Qed.

      Lemma Some_not_None : forall A o, o <> None <-> exists a : A, o = Some a.
        split; intros.
        eapply ex_up; eauto.
        openhyp.
        nintro.
        rewrite H0 in H; intuition.
      Qed.

      Lemma augment_elim_2 :
        forall imps specs stn (lbls : list glabel),
          augment imps specs stn lbls ->
          (forall x, List.In x lbls -> LabelMap.find (x : Labels.label) imps <> None) ->
          forall l,
            List.In l lbls ->
            Labels stn l <> None.
      Proof.
        induction lbls; simpl; intros.
        intuition.
        destruct H1.
        subst.
        destruct l.
        unfold to_bedrock_label in *.
        simpl in *.
        destruct (option_dec (LabelMap.LabelMap.find (elt:=assert) (s, Global s0) imps)).
        destruct s1.
        rewrite e in H.
        openhyp.
        eapply Some_not_None; eexists; eauto.
        generalize H0; specialize (H0 (s, s0)); intro; simpl in *.
        rewrite e in H0.
        intuition.

        destruct a.
        unfold to_bedrock_label in *.
        simpl in *.
        destruct (option_dec (LabelMap.LabelMap.find (elt:=assert) (s, Global s0) imps)).
        destruct s1.
        rewrite e in H.
        openhyp.
        eauto.
        generalize H0; specialize (H0 (s, s0)); intro; simpl in *.
        rewrite e in H0.
        intuition.
      Qed.

      Notation stn_good_to_use := (LinkSpec.stn_good_to_use modules imports).

      Lemma augment_stn_good_to_use : forall specs stn, augment (fullImports bimports_diff_bexports stubs) specs stn accessible_labels -> stn_good_to_use stn.
      Proof.
        unfold LinkSpec.stn_good_to_use.
        unfold label_in.
        intros.
        openhyp.

        (* in exports *)
        assert (In lbl exports).
        subst.
        eapply MapsTo_In.
        eapply exports_mapsto_iff.
        descend; eauto.
        subst.
        eapply augment_elim_2 in H.
        2 : eapply accessible_labels_subset_fullImports.
        Focus 2.
        eapply exports_accessible_labels.
        eapply in_find_iff.
        eauto.
        eauto.

        (* in imports *)
        eapply augment_elim_2 in H.
        2 : eapply accessible_labels_subset_fullImports.
        Focus 2.
        eapply imports_accessible_labels.
        eapply in_find_iff.
        eauto.
        eauto.
      Qed.

      Lemma augment_stn_injective : forall specs stn, augment (fullImports bimports_diff_bexports stubs) specs stn accessible_labels -> stn_injective (label_in modules imports) (glabel2w stn).
      Proof.
        unfold stn_injective.
        intros.

        unfold label_in in H0.
        openhyp.
        assert (In lbl1 exports).
        subst.
        eapply MapsTo_In.
        eapply exports_mapsto_iff.
        descend; eauto.

        unfold label_in in H1.
        openhyp.
        assert (In lbl2 exports).
        subst.
        eapply MapsTo_In.
        eapply exports_mapsto_iff.
        descend; eauto.

        eapply augment_injective_exports; eauto.

        exfalso.
        eapply augment_injective_exports_imports; eauto.

        unfold label_in in H1.
        openhyp.
        assert (In lbl2 exports).
        subst.
        eapply MapsTo_In.
        eapply exports_mapsto_iff.
        descend; eauto.

        exfalso.
        eapply augment_injective_exports_imports; eauto.

        eapply augment_injective_imports; eauto.
      Qed.

      Lemma augment_env_good_to_use : forall specs stn, augment (fullImports bimports_diff_bexports stubs) specs stn accessible_labels -> env_good_to_use modules imports stn fs.
        intros.
        split.
        eapply augment_stn_good_to_use; eauto.
        split.
        eapply augment_stn_injective; eauto.
        eapply augment_fs_good_to_use; eauto.
      Qed.

      Lemma good_vcs : forall ls, (forall x, List.In x ls -> List.In x (Functions m)) -> vcs (makeVcs bimports_diff_bexports stubs (List.map make_stub ls)).
        induction ls; simpl; eauto.
        Opaque funcs_ok.
        Opaque spec_without_funcs_ok.
        wrap0.
        descend.

        eapply fs_funcs_ok; eauto.

        eapply Imply_sound.
        eauto.
        step auto_ext.
        descend; eauto.
        simpl in *.
        eapply augment_env_good_to_use; eauto.

        erewrite tgt_fullImports; eauto.
      Qed.

      (* Interface *)

      Theorem make_module_ok : XCAP.moduleOk make_module.
        eapply bmoduleOk.
        eapply module_name_not_in_imports.
        eapply no_dup_func_names.
        eapply good_vcs; eauto.
      Qed.

      Lemma make_module_Imports : Imports make_module === get_module_Imports m.
        intros.
        unfold make_module, bmodule_, Imports.
        rewrite importsMap_of_list.
        eapply to_blm_Equal.
        unfold bimports_diff_bexports.
        rewrite of_list_diff.
        unfold get_module_Imports.
        rewrite bimports_Equal_update_update by eauto.
        rewrite bexports_Equal_exports by eauto.
        reflexivity.
        eapply NoDupKey_bimports; eauto.
        eapply NoDupKey_bexports; eauto.
        eapply diff_NoDupKey.
        eapply NoDupKey_bimports; eauto.
      Qed.

      Lemma make_module_Exports : Exports make_module === get_module_Exports m.
        intros.
        unfold make_module, bmodule_, Imports; simpl.
        rewrite exps_spec.
        eapply to_blm_Equal.
        unfold stubs.
        unfold make_stub.
        rewrite map_map.
        unfold func_to_import.
        simpl.
        unfold module_exports.
        reflexivity.
      Qed.

      Lemma make_module_Modules : SS.Equal (Modules make_module) (singleton (MName m)).
        intros.
        unfold make_module, bmodule_, Modules.
        reflexivity.
      Qed.

    End module.

  End TopSection.

End Make.
