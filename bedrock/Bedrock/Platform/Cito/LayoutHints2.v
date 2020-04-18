Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.LayoutHintsUtil Bedrock.Platform.Cito.ADT.
Require Import Bedrock.Platform.Cito.RepInv Bedrock.Platform.Cito.WordMap.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Bedrock.Platform.Cito.Inv.
  Module Import InvMake := Inv.Make E.
  Module Import InvMake2 := InvMake.Make M.
  Import SemanticsMake.
  Require Import Bedrock.Platform.Cito.SemanticsFacts5.
  Require Import Bedrock.Platform.Cito.SemanticsUtil.

  Section TopSection.

    Definition heap_to_split h (_ : list (W * ArgIn)) := is_heap h.
    Require Import Bedrock.Platform.Cito.WordMapFacts.

    Lemma split_heap' : forall pairs h, good_inputs h pairs -> heap_to_split h pairs ===> let h1 := make_heap pairs in is_heap h1 * is_heap (heap_diff h h1).
      unfold heap_to_split; induction pairs; simpl; intros.

      unfold heap_diff, heap_empty.
      eapply Himp_trans; [ | apply Himp_star_Emp' ].
      unfold is_heap, heap_elements.
      apply starL_permute.

      apply NoDupA_NoDup.
      apply WordMap.elements_3w.

      apply NoDupA_NoDup.
      apply WordMap.elements_3w.

      intuition.
      apply In_InA' in H0.
      apply InA_In.
      apply WordMap.elements_1.
      apply WordMap.elements_2 in H0.
      apply diff_mapsto_iff.
      intuition.
      destruct H1.
      eapply WordMap.empty_1; eauto.
      apply In_InA' in H0.
      apply WordMap.elements_2 in H0.
      apply diff_mapsto_iff in H0.
      intuition.
      apply InA_In.
      apply WordMap.elements_1; auto.

      unfold is_heap, heap_elements.
      destruct H.
      inversion_clear H.
      hnf in H1.
      hnf in H0.
      case_eq (snd a); intros.
      rewrite H in *; subst.
      unfold make_heap; simpl.
      unfold store_pair at 2 4.
      unfold ArgIn, SemanticsMake.ArgIn.
      unfold WordMap.key in H.
      rewrite H.
      apply IHpairs.
      split; auto.
      hnf.
      simpl in H0.
      unfold ArgIn, SemanticsMake.ArgIn in H0.
      rewrite H in H0.
      auto.

      rewrite H in H1.
      generalize H1; intro Ho.
      apply WordMap.find_2 in Ho.
      apply WordMap.elements_1 in Ho.
      apply InA_In in Ho.
      eapply starL_out in Ho.
      destruct Ho; intuition.
      eapply Himp_trans; [ apply H4 | ].
      clear H4; simpl.
      2: apply NoDupA_NoDup; apply WordMap.elements_3w.
      assert (In (fst a, a0) (WordMap.elements (elt:=elt) (make_heap (a :: pairs)))).
      unfold make_heap; simpl.

      apply InA_In.
      apply elements_mapsto_iff.
      simpl in H0.
      unfold is_adt in H0.
      unfold WordMap.key, SemanticsMake.ArgIn in *.
      rewrite H in *; simpl in *.
      inversion_clear H0.
      apply preserve_store; auto.
      apply Forall_forall; intros.
      case_eq (snd x0); intuition idtac.
      unfold store_pair in H8.
      unfold WordMap.key, ArgIn, SemanticsMake.ArgIn in *.
      rewrite H in H8.
      unfold heap_upd in H8.
      eapply add_in_iff in H8; intuition idtac.
      2: destruct H9; eapply WordMap.empty_1; eauto.
      destruct a; simpl in *; subst.
      destruct x0; simpl in *; subst.

      eauto using keep_key.
      unfold store_pair.
      unfold WordMap.key, ArgIn, SemanticsMake.ArgIn in *.
      rewrite H.
      unfold heap_upd.
      apply WordMap.add_1; auto.

      simpl in *.
      destruct a; simpl in *; subst; simpl in *.
      rename w into k.
      inversion_clear H0.
      eapply Himp_trans; [ | apply Himp_star_frame; [ apply starL_permute | apply Himp_refl ] ].
      instantiate (1 := (k, a0) :: heap_elements (make_heap pairs)).
      Focus 2.
      constructor.
      intro.
      unfold heap_elements, make_heap in H0.
      apply In_InA' in H0.
      apply WordMap.elements_2 in H0.

      apply store_keys in H0; intuition idtac.
      apply H.
      change k with (fst (k, AxSpec.ADT a0)).
      apply in_map; apply filter_In; tauto.
      eapply WordMap.empty_1; eauto.
      apply NoDupA_NoDup; apply WordMap.elements_3w.
      2: apply NoDupA_NoDup; apply WordMap.elements_3w.
      Focus 2.
      simpl.
      split.
      destruct 1; subst.
      auto.
      unfold heap_elements in H0.

      apply InA_In.
      destruct x0.
      apply WordMap.elements_1.
      unfold make_heap; simpl.
      apply store_keys'; auto.
      apply In_InA' in H0.
      apply WordMap.elements_2 in H0.
      apply store_keys in H0; intuition idtac.
      exfalso; eapply WordMap.empty_1; eauto.

      intro.
      apply In_InA' in H0.
      destruct x0.
      apply WordMap.elements_2 in H0.
      unfold make_heap in H0; simpl in H0.
      apply store_keys in H0.
      intuition idtac.
      right.
      apply InA_In.
      apply WordMap.elements_1.
      apply store_keys'; auto.
      unfold store_pair in H7; simpl in H7.
      apply add_mapsto_iff in H7; intuition subst.
      auto.
      exfalso; eapply WordMap.empty_1; eauto.

      simpl.
      eapply Himp_trans; [ | apply Himp_star_assoc' ].
      apply Himp_star_frame; try apply Himp_refl.
      eapply Himp_trans; [ apply starL_permute | ].
      auto.
      instantiate (1 := WordMap.elements (WordMap.remove k h)).
      apply NoDupA_NoDup; apply WordMap.elements_3w.
      split; intro.
      apply InA_In.
      destruct x0.
      apply WordMap.elements_1.
      apply remove_mapsto_iff.
      apply H6 in H0.
      destruct H0; split; auto.
      2: apply WordMap.elements_2; apply In_InA'; auto.
      apply In_InA' in H7; apply WordMap.elements_2 in H7.
      apply WordMap.find_1 in H7.
      congruence.
      apply In_InA' in H0.
      destruct x0; apply WordMap.elements_2 in H0.
      apply remove_mapsto_iff in H0.
      apply H6; intuition (try congruence).
      apply InA_In; apply WordMap.elements_1; auto.

      eapply Himp_trans; [ apply IHpairs | ]; clear IHpairs.
      split; auto.
      apply Forall_forall; intros.
      eapply Forall_forall in H2; [ | apply H0 ].
      hnf in H2; hnf.
      destruct x0; simpl in *.
      rename w into k0.
      destruct v; auto.
      apply WordMap.find_1.
      apply remove_mapsto_iff.
      apply WordMap.find_2 in H2.
      intuition subst.
      apply H.
      change k0 with (fst (k0, AxSpec.ADT a)).
      apply in_map.
      apply filter_In; auto.

      apply Himp_star_frame; try apply Himp_refl.
      apply starL_permute; try (apply NoDupA_NoDup; apply WordMap.elements_3w); intros.
      intuition; apply InA_In; apply WordMap.elements_1;
        apply In_InA' in H0; apply WordMap.elements_2 in H0;
          apply diff_mapsto_iff; apply diff_mapsto_iff in H0; intuition idtac.
      apply remove_mapsto_iff in H7; tauto.
      apply remove_mapsto_iff in H7; intuition subst.
      destruct H0.
      eapply store_keys in H0; intuition idtac.
      simpl in *; intuition (try congruence).
      apply H8.
      eexists.
      eapply store_keys'; eauto.
      exfalso; eapply WordMap.empty_1; eauto.
      apply remove_mapsto_iff; intuition subst.
      apply H8.
      eexists; eapply store_keys'; eauto.
      simpl; eauto.
      auto.
      constructor; auto.
      apply H8.
      destruct H0.
      eapply store_keys in H0; intuition idtac.
      eexists.
      eapply store_keys'.
      simpl; eauto.
      constructor; auto.
      exfalso; eapply WordMap.empty_1; eauto.
    Qed.

    Lemma split_heap : forall h pairs, good_inputs h pairs -> heap_to_split h pairs ===> let h1 := make_heap pairs in is_heap h1 * is_heap (heap_diff h h1).
      eauto using split_heap'.
    Qed.

    Definition hints_split_heap : TacPackage.
      prepare split_heap tt.
    Defined.

  End TopSection.

End Make.
