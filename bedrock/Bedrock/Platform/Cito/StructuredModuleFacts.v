Set Implicit Arguments.

Require Import Bedrock.Platform.AutoSep.
Require Import Bedrock.StructuredModule.

Require Import Bedrock.Labels.
Require Import Bedrock.LabelMap.
Require Bedrock.Platform.Cito.LabelMapFacts.
Require Import Bedrock.Platform.Cito.GLabel.
Require Import Bedrock.Platform.Cito.GLabelMap.
Import GLabelMap.
Require Import Bedrock.Platform.Cito.GLabelMapFacts.

Require Import Bedrock.Platform.Cito.ListFacts1.
Require Import Bedrock.Platform.Cito.ListFacts2.

Section TopSection.

  Definition importsMap' (imports : list import) base :=
    List.fold_left
      (fun m p =>
         let '(modl, f, pre) := p in
         LabelMap.LabelMap.add (modl, Global f) pre m) imports base.

  Require Import Bedrock.Platform.Cito.ConvertLabel.

  Lemma importsMap_spec' :
    forall imps2 imps1 base,
      NoDupKey (imps1 ++ imps2) ->
      (forall (k : glabel), LabelMap.LabelMap.find (k : label) base = find_list k imps1) ->
      forall (k : glabel), LabelMap.LabelMap.find (k : label) (importsMap' imps2 base) = find_list k (imps1 ++ imps2).
    induction imps2; simpl.
    intros.
    rewrite app_nil_r.
    eauto.
    intros.
    rewrite <- DepList.pf_list_simpl.
    eapply IHimps2.
    rewrite DepList.pf_list_simpl.
    eauto.
    destruct a; simpl.
    destruct k0; simpl.
    intros.
    destruct (LabelMap.LabelKey.eq_dec (k0 : Labels.label) (s, Global s0)).
    unfold LabelKey.eq in *.
    erewrite LabelMap.LabelMap.find_1.
    Focus 2.
    eapply LabelMap.LabelMap.add_1.
    eauto.
    destruct k0.
    injection e; intros; subst.
    erewrite In_find_list_Some_left.
    eauto.
    rewrite <- DepList.pf_list_simpl in H.
    eapply NoDupKey_unapp1.
    eauto.
    eapply InA_eqke_In; intuition.
    unfold LabelKey.eq in *.
    erewrite LabelMapFacts.add_4.
    rewrite H0.
    erewrite find_list_neq.
    eauto.
    eapply NoDupKey_unapp1.
    eauto.
    intuition.
    destruct k0.
    injection H1; intros; subst; intuition.
    eauto.
  Qed.

  Lemma importsMap_spec : forall imps (k : glabel), NoDupKey imps -> LabelMap.LabelMap.find (k : label) (importsMap imps) = find_list k imps.
    intros.
    unfold importsMap.
    erewrite importsMap_spec'.
    erewrite app_nil_l; eauto.
    erewrite app_nil_l; eauto.
    intros.
    unfold find_list.
    eauto.
  Qed.

  Definition fullImports' impsMap modName (functions : list (function modName)) : LabelMap.LabelMap.t assert :=
    List.fold_left
      (fun m p =>
         let '(f, pre, _) := p in
         LabelMap.LabelMap.add (modName, Global f) pre m) functions impsMap.

  Definition func_to_import mn (f : function mn) : import:= ((mn, fst (fst f)), snd (fst f)).

  Lemma fullImports_spec' :
    forall mn (fns : list (function mn)) imps impsMap,
      let fns' := List.map (@func_to_import _) fns in
      let whole := imps ++ fns' in
      NoDupKey whole ->
      (forall (k : glabel), LabelMap.LabelMap.find (k : label) impsMap = find_list k imps) ->
      forall (k : glabel), LabelMap.LabelMap.find (k : label) (fullImports' impsMap fns) = find_list k whole.
  Proof.
    unfold fullImports'.
    unfold func_to_import.
    induction fns; simpl; intros.
    rewrite app_nil_r in *.
    eauto.
    rewrite <- DepList.pf_list_simpl.
    eapply IHfns.
    rewrite DepList.pf_list_simpl.
    eauto.
    destruct a; simpl.
    destruct p; simpl.
    intros.
    destruct (LabelMap.LabelKey.eq_dec (k0 : Labels.label) (mn, Global s)).
    unfold LabelKey.eq in *.
    erewrite LabelMap.LabelMap.find_1.
    Focus 2.
    eapply LabelMap.LabelMap.add_1.
    eauto.
    destruct k0.
    injection e; intros; subst.
    erewrite In_find_list_Some_left.
    eauto.
    simpl in *.
    rewrite <- DepList.pf_list_simpl in H.
    eapply NoDupKey_unapp1.
    eauto.
    eapply InA_eqke_In; intuition.
    unfold LabelKey.eq in *.
    erewrite LabelMapFacts.add_4.
    rewrite H0.
    erewrite find_list_neq.
    eauto.
    eapply NoDupKey_unapp1.
    eauto.
    intuition.
    destruct k0.
    injection H1; intros; subst; intuition.
    eauto.
  Qed.

  Lemma fullImports_spec :
    forall (imps : list import) mn (fns : list (function mn)) (k : glabel),
      let fns' := List.map (@func_to_import _) fns in
      let whole := imps ++ fns' in
      NoDupKey whole ->
      LabelMap.LabelMap.find (k : label) (fullImports imps fns) = find_list k whole.
  Proof.
    unfold fullImports.
    specialize fullImports_spec'; intros.
    unfold fullImports' in *.
    eapply H; eauto.
    intros.
    eapply importsMap_spec; eauto.
    eapply NoDupKey_unapp1.
    eauto.
  Qed.

  Require Import Bedrock.Platform.Cito.ConvertLabelMap.
  Import Notations.
  Open Scope clm_scope.

  Require Import Bedrock.Platform.Cito.GeneralTactics.

  Lemma importsMap_of_list : forall ls, NoDupKey ls -> importsMap ls === of_list ls.
    intros.
    hnf.
    intros.
    destruct y.
    destruct l.
    specialize importsMap_spec; intros.
    unfold to_bedrock_label in *.
    erewrite H0 with (k := (s, s0)); eauto.
    unfold find_list.
    rewrite <- of_list_1b; eauto.
    symmetry.
    rewrite <- to_blm_spec; eauto.
    specialize importsMapGlobal; intros.
    unfold importsGlobal in *.
    eapply option_univalence.
    split; intros.
    eapply LabelMap.find_2 in H1.
    eapply H0 in H1.
    openhyp.
    simpl in *.
    discriminate.
    rewrite to_blm_no_local in H1.
    discriminate.
  Qed.

  Lemma exps_spec :
    forall mn (fns : list (function mn)),
      let fns' := List.map (@func_to_import _) fns in
      exps fns === of_list fns'.
    induction fns; simpl; intros.
    eapply to_blm_empty.
    simpl in *.
    destruct a; simpl in *.
    destruct p; simpl in *.
    unfold uncurry; simpl in *.
    rewrite IHfns.
    rewrite to_blm_add.
    eapply LabelMapFacts.add_m; eauto.
    reflexivity.
  Qed.

  Lemma importsOk_Compat_left : forall m1 m2, importsOk m1 m2 -> LabelMapFacts.Compat m1 m2.
    intros.
    unfold LabelMapFacts.Compat.
    intros.
    eapply LabelMapFacts.In_MapsTo in H0.
    openhyp.
    eapply LabelMapFacts.In_MapsTo in H1.
    openhyp.
    assert (x = x0).
    eapply use_importsOk; eauto.
    eapply LabelMap.find_1; eauto.
    subst.
    eapply LabelMap.find_1 in H1.
    eapply LabelMap.find_1 in H0.
    congruence.
  Qed.

  Require Import Coq.Setoids.Setoid.
  Require Import Coq.Classes.Morphisms.

  Lemma importsOk_f_Proper :
    forall m,
      Proper (Logic.eq ==> Logic.eq ==> iff ==> iff)
             (fun (l : LabelMap.LabelMap.key) (pre : assert) (P : Prop) =>
                match LabelMap.LabelMap.find (elt:=assert) l m with
                  | Some pre' => pre = pre' /\ P
                  | None => P
                end).
    intros.
    unfold Proper.
    unfold respectful.
    intros.
    subst.
    destruct (LabelMap.find y m); intuition.
  Qed.

  Lemma importsOk_f_transpose_neqkey :
    forall m,
      LabelMapFacts.transpose_neqkey
        iff
        (fun (l : LabelMap.LabelMap.key) (pre : assert) (P : Prop) =>
           match LabelMap.LabelMap.find (elt:=assert) l m with
             | Some pre' => pre = pre' /\ P
             | None => P
           end).
    unfold LabelMapFacts.transpose_neqkey.
    intros.
    destruct (LabelMap.find k m); destruct (LabelMap.find k' m); intuition.
  Qed.

  Global Add Morphism importsOk
      with signature LabelMap.Equal ==> Logic.eq ==> iff as importsOk_m.
    intros.
    unfold importsOk.
    eapply LabelMapFacts.fold_Equal; eauto.
    intuition.
    eapply importsOk_f_Proper.
    eapply importsOk_f_transpose_neqkey.
  Qed.

  Require Import Bedrock.Platform.Cito.Option.

  Lemma importsOk_Compat_right : forall m1 m2, LabelMapFacts.Compat m1 m2 -> importsOk m1 m2.
    induction m1 using LabelMapFacts.map_induction_bis.
    intros.
    rewrite <- H in H0.
    rewrite <- H.
    eauto.
    intros.
    unfold importsOk.
    rewrite LabelMap.fold_1.
    simpl.
    eauto.
    intros.
    unfold importsOk.
    rewrite LabelMapFacts.fold_add; eauto.
    destruct (option_dec (LabelMap.find (elt:=assert) x m2)).
    destruct s.
    rewrite e0.
    split.
    eapply LabelMapFacts.Compat_eq; eauto.
    eapply LabelMap.find_1.
    eapply LabelMapFacts.add_mapsto_iff.
    eauto.
    eapply IHm1.
    eapply LabelMapFacts.Compat_add_not_In; eauto.
    rewrite e0.
    eapply IHm1.
    eapply LabelMapFacts.Compat_add_not_In; eauto.
    intuition.
    eapply importsOk_f_Proper.
    eapply importsOk_f_transpose_neqkey.
  Qed.

  Lemma importsOk_Compat : forall m1 m2, importsOk m1 m2 <-> LabelMapFacts.Compat m1 m2.
    split; intros.
    eapply importsOk_Compat_left; eauto.
    eapply importsOk_Compat_right; eauto.
  Qed.

  Lemma XCAP_union_update : forall elt m1 m2, LabelMap.Equal (@XCAP.union elt m1 m2) (LabelMapFacts.update m2 m1).
    unfold XCAP.union.
    unfold LabelMapFacts.update.
    intros.
    reflexivity.
  Qed.

  Lemma XCAP_diff_diff : forall elt m1 m2, @LabelMap.Equal elt (XCAP.diff m1 m2) (LabelMapFacts.diff m1 m2).
    intros.
    unfold LabelMap.Equal.
    intros.
    eapply option_univalence.
    split; intros.
    eapply LabelMap.find_2 in H.
    eapply MapsTo_diff in H.
    Focus 2.
    instantiate (1 := @StructuredModule.bmodule_ nil "" nil).
    instantiate (1 := @StructuredModule.bmodule_ nil "" nil).
    simpl.
    unfold importsMap.
    simpl.
    rewrite LabelMap.fold_1.
    simpl.
    eauto.
    openhyp.
    eapply LabelMap.find_1.
    eapply LabelMapFacts.diff_mapsto_iff.
    eauto.
    eapply LabelMap.find_2 in H.
    eapply LabelMapFacts.diff_mapsto_iff in H.
    openhyp.
    eapply LabelMap.find_1.
    eapply MapsTo_diffr; eauto.
    eapply LabelMap.elements_3w.
  Qed.

End TopSection.
