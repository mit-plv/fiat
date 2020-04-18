Set Implicit Arguments.

Require Import Coq.Lists.List.

Require Import Bedrock.Labels.
Require Import Bedrock.LabelMap.
Require Bedrock.Platform.Cito.LabelMapFacts.
Require Import Bedrock.Platform.Cito.GLabel.
Require Import Bedrock.Platform.Cito.GLabelMap.
Import GLabelMap.
Require Import Bedrock.Platform.Cito.GLabelMapFacts.

Require Import Bedrock.Platform.Cito.ConvertLabel.

Definition to_bl_pair elt (p : glabel * elt) := (fst p : label, snd p).

Definition to_blm elt m := LabelMapFacts.of_list (List.map (@to_bl_pair _) (@elements elt m)).

Module Notations.
  Notation "m1 === m2" := (LabelMap.Equal m1 (to_blm m2)) (at level 70) : clm_scope.
End Notations.

Section TopSection.

  Import Notations.
  Open Scope clm_scope.
  Import ListNotations.
  Import FMapNotations.
  Open Scope fmap.

  Require Import Coq.Setoids.Setoid.
  Require Import Coq.Lists.SetoidList.
  Require Import Bedrock.Platform.Cito.GeneralTactics.
  Require Import Bedrock.Platform.Cito.ListFacts1.

  Set Printing Coercions.

  Lemma NoDupKey_to_bl_pair_elements : forall elt m, LabelMapFacts.NoDupKey (List.map (@to_bl_pair _) (@elements elt m)).
    intros.
    eapply LabelMapFacts.NoDupKey_NoDup_fst.
    rewrite map_map.
    unfold to_bl_pair; simpl in *.
    rewrite <- map_map.
    eapply Injection_NoDup.
    unfold to_bedrock_label.
    unfold IsInjection; intuition.
    destruct x; destruct y; simpl in *.
    injection H0; intros; subst.
    intuition.
    eapply NoDupKey_NoDup_fst.
    eapply elements_3w.
  Qed.

  Lemma to_blm_spec : forall elt (k : glabel) m, @LabelMap.find elt (k : label) (to_blm m) = find k m.
    unfold to_blm, LabelMapFacts.to_map.
    intros.
    eapply option_univalence; split; intros.
    eapply LabelMap.find_2 in H.
    eapply LabelMapFacts.of_list_1 in H.
    eapply LabelMapFacts.InA_eqke_In in H.
    eapply in_map_iff in H.
    openhyp.
    destruct x; simpl in *.
    unfold to_bl_pair, to_bedrock_label in *; simpl in *.
    destruct g; simpl in *.
    destruct k; simpl in *.
    injection H; intros; subst.
    eapply InA_eqke_In in H0.
    eapply elements_mapsto_iff in H0.
    eapply find_1; eauto.
    eapply NoDupKey_to_bl_pair_elements.

    eapply LabelMap.find_1.
    eapply LabelMapFacts.of_list_1.
    eapply NoDupKey_to_bl_pair_elements.
    eapply LabelMapFacts.InA_eqke_In.
    eapply in_map_iff.
    exists (k, v); split; eauto.
    eapply InA_eqke_In.
    eapply elements_1.
    eapply find_2.
    eauto.
  Qed.

  Lemma to_blm_no_local : forall elt s1 s2 m, @LabelMap.find elt (s1, Local s2) (to_blm m) = None.
    unfold to_blm, LabelMapFacts.to_map.
    intros.
    eapply LabelMapFacts.not_in_find.
    intuition.
    eapply LabelMapFacts.In_MapsTo in H.
    openhyp.
    eapply LabelMapFacts.of_list_1 in H.
    eapply LabelMapFacts.InA_eqke_In in H.
    eapply in_map_iff in H.
    openhyp.
    unfold to_bl_pair, to_bedrock_label in *; simpl in *.
    discriminate.
    eapply NoDupKey_to_bl_pair_elements.
  Qed.

  Lemma to_blm_local_not_in : forall elt s1 s2 m, ~ @LabelMap.In elt (s1, Labels.Local s2) (to_blm m).
    intros.
    eapply LabelMapFacts.not_find_in_iff.
    rewrite to_blm_no_local; eauto.
  Qed.

  Lemma to_blm_mapsto_iff : forall elt k (v : elt) m, LabelMap.MapsTo k v (to_blm m) <-> exists k' : glabel, MapsTo k' v m /\ k = (k' : label).
    split; intros.
    destruct k.
    destruct l.
    replace ((s, Labels.Global s0)) with (to_bedrock_label (s, s0)) in * by eauto.
    eapply LabelMap.find_1 in H.
    rewrite to_blm_spec in H.
    eapply find_2 in H.
    eexists; eauto.
    eapply LabelMapFacts.MapsTo_In in H.
    eapply to_blm_local_not_in in H; intuition.
    openhyp.
    subst.
    eapply LabelMap.find_2.
    rewrite to_blm_spec.
    eapply find_1; eauto.
  Qed.

  Lemma to_blm_Equal : forall elt m1 m2, @LabelMap.Equal elt (to_blm m1) (to_blm m2) <-> m1 == m2.
    unfold Equal, LabelMap.Equal.
    intuition.
    repeat erewrite <- to_blm_spec.
    eauto.
    destruct y.
    destruct l.
    replace ((s, Labels.Global s0)) with (to_bedrock_label (s, s0)) by eauto.
    repeat erewrite to_blm_spec.
    eauto.
    repeat rewrite to_blm_no_local.
    eauto.
  Qed.

  Global Add Parametric Morphism elt : (@to_blm elt)
      with signature Equal ==> LabelMap.Equal as to_blm_Equal_m.
    intros; eapply to_blm_Equal; eauto.
  Qed.

  Lemma to_blm_In : forall elt (k : glabel) m, @LabelMap.In elt (k : label) (to_blm m) <-> In k m.
    split; intros.
    eapply in_find_iff.
    eapply LabelMapFacts.in_find_iff in H.
    rewrite <- to_blm_spec.
    eauto.
    eapply in_find_iff in H.
    eapply LabelMapFacts.in_find_iff.
    rewrite to_blm_spec.
    eauto.
  Qed.

  Lemma to_blm_Compat : forall elt m1 m2, @LabelMapFacts.Compat elt (to_blm m1) (to_blm m2) <-> Compat m1 m2.
    unfold Compat, LabelMapFacts.Compat.
    intuition.
    repeat erewrite <- to_blm_spec.
    eapply H.
    eapply to_blm_In; eauto.
    eapply to_blm_In; eauto.
    destruct k.
    destruct l.
    replace ((s, Labels.Global s0)) with (to_bedrock_label (s, s0)) by eauto.
    repeat erewrite to_blm_spec.
    eapply H.
    eapply to_blm_In; eauto.
    eapply to_blm_In; eauto.
    repeat rewrite to_blm_no_local.
    eauto.
  Qed.

  Global Add Parametric Morphism elt : (@to_blm elt)
      with signature (@Compat elt) ==> (@LabelMapFacts.Compat elt) as to_blm_Compat_m.
    intros; eapply to_blm_Compat; eauto.
  Qed.

  Lemma to_blm_empty : forall elt, LabelMap.empty elt === {}.
    unfold Equal, LabelMap.Equal.
    intuition.
  Qed.

  Require Import Bedrock.Platform.Cito.GeneralTactics2.

  Lemma to_blm_update : forall elt m1 m2, @LabelMap.Equal elt (to_blm (update m1 m2)) (LabelMapFacts.update (to_blm m1) (to_blm m2)).
    unfold Equal, LabelMap.Equal.
    intros.
    destruct y.
    destruct l; simpl.
    replace ((s, Labels.Global s0)) with (to_bedrock_label (s, s0)) by eauto.
    repeat erewrite to_blm_spec.
    destruct (In_dec m2 (s, s0)).
    rewrite update_o_2 by eauto.
    rewrite LabelMapFacts.update_o_2.
    repeat erewrite to_blm_spec.
    eauto.
    eapply to_blm_In; eauto.
    rewrite update_o_1 by eauto.
    rewrite LabelMapFacts.update_o_1.
    repeat erewrite to_blm_spec.
    eauto.
    not_not.
    eapply to_blm_In; eauto.
    repeat rewrite to_blm_no_local.
    symmetry.
    eapply LabelMapFacts.not_in_find.
    intuition.
    eapply LabelMapFacts.update_in_iff in H.
    openhyp.
    eapply to_blm_local_not_in; eauto.
    eapply to_blm_local_not_in; eauto.
  Qed.

  Lemma to_blm_diff : forall elt m1 m2, @LabelMap.Equal elt (to_blm (diff m1 m2)) (LabelMapFacts.diff (to_blm m1) (to_blm m2)).
    unfold Equal, LabelMap.Equal.
    intros.
    destruct y.
    destruct l; simpl.
    replace ((s, Labels.Global s0)) with (to_bedrock_label (s, s0)) by eauto.
    repeat erewrite to_blm_spec.
    destruct (In_dec m2 (s, s0)).
    rewrite diff_o_none by eauto.
    rewrite LabelMapFacts.diff_o_none.
    eauto.
    eapply to_blm_In; eauto.
    rewrite diff_o by eauto.
    rewrite LabelMapFacts.diff_o.
    repeat erewrite to_blm_spec.
    eauto.
    not_not.
    eapply to_blm_In; eauto.
    repeat rewrite to_blm_no_local.
    symmetry.
    eapply LabelMapFacts.not_in_find.
    intuition.
    eapply LabelMapFacts.diff_in_iff in H.
    openhyp.
    eapply to_blm_local_not_in; eauto.
  Qed.

  Lemma to_blm_add : forall elt (k : glabel) v m, @LabelMap.Equal elt (to_blm (add k v m)) (LabelMap.add (k : label) v (to_blm m)).
    unfold Equal, LabelMap.Equal.
    intros.
    destruct y.
    destruct l; simpl.
    replace ((s, Labels.Global s0)) with (to_bedrock_label (s, s0)) by eauto.
    repeat erewrite to_blm_spec.
    rewrite add_o.
    destruct (eq_dec k (s, s0)).
    subst.
    symmetry.
    rewrite LabelMapFacts.add_eq_o; eauto.
    rewrite LabelMapFacts.add_neq_o.
    repeat erewrite to_blm_spec; eauto.
    not_not.
    unfold to_bedrock_label in *.
    destruct k; simpl in *.
    injection H; intros; subst.
    eauto.
    repeat rewrite to_blm_no_local.
    symmetry.
    eapply LabelMapFacts.not_in_find.
    intuition.
    eapply LabelMapFacts.add_in_iff in H.
    unfold to_bedrock_label in *.
    destruct k; simpl in *.
    openhyp.
    discriminate.
    eapply to_blm_local_not_in; eauto.
  Qed.

End TopSection.
