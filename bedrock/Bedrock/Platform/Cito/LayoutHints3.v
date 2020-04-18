Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.LayoutHintsUtil Bedrock.Platform.Cito.ADT.
Require Import Bedrock.Platform.Cito.RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Bedrock.Platform.Cito.Inv.
  Module Import InvMake := Inv.Make E.
  Module Import InvMake2 := InvMake.Make M.
  Import SemanticsMake.
  Import WordMap.

  Section TopSection.

    Definition is_heap_upd_option h addr a := is_heap (heap_upd_option h addr a).

    Require Import Bedrock.Platform.Cito.SemanticsFacts5.

    Lemma pure_split : forall P Q R,
      (forall specs sm m, interp specs (P sm m ---> [|Q|]))%PropX
      -> P ===> R
      -> P ===> [|Q|] * R.
      intros; do 3 intro.
      apply existsR with smem_emp.
      apply existsR with m.
      apply andR.
      apply injR.
      apply split_a_semp_a.
      apply andR.
      eapply Imply_trans; [ apply H | ].
      apply injL; propxFo.
      reflexivity.
      apply H0.
    Qed.

    Lemma use_rep_inv_ptr' : forall addr a ls,
      rep_inv addr a * Bags.starL (fun p : W * ADTValue => rep_inv (fst p) (snd p)) ls
      ===> [|forall v, ~In (addr, v) ls|] * (rep_inv addr a
        * Bags.starL (fun p : W * ADTValue => rep_inv (fst p) (snd p)) ls).
      induction ls; simpl; intros.

      apply Himp_star_pure_cc; auto.
      apply Himp_refl.

      eapply Himp_trans; [ apply Himp_star_assoc' | ].
      eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_star_comm | apply Himp_refl ] | ].
      eapply Himp_trans; [ apply Himp_star_assoc | ].
      eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl | apply IHls ] | ].

      eapply Himp_trans; [ apply Himp_star_assoc' | ].
      eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_star_comm | apply Himp_refl ] | ].
      eapply Himp_trans; [ apply Himp_star_assoc | ].
      apply Himp_star_pure_c; intro.

      apply pure_split.
      Focus 2.
      eapply Himp_trans; [ apply Himp_star_assoc' | ].
      eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_star_comm | apply Himp_refl ] | ].
      eapply Himp_trans; [ apply Himp_star_assoc | ].
      apply Himp_refl.

      intros.
      apply Imply_trans with [| addr <> fst a0 |]%PropX.
      do 2 (apply existsL; intro).
      apply andL; apply injL; intro.
      apply andL.
      eapply Imply_trans.
      apply rep_inv_ptr.
      apply Imply_trans with [| smem_get_word (implode sm) (fst a0) x <> None |]%PropX.
      do 2 (apply existsL; intro).
      apply andL; apply injL; intro.
      apply andL.
      apply swap.
      apply Imply_I; apply interp_weaken.
      do 2 (apply existsL; intro).
      apply andL; apply injL; intro.
      apply andL.
      apply existsL; intro.
      apply injL; intuition idtac.
      apply andL.
      apply injL; intuition idtac.
      apply injL; intuition idtac.
      apply Inj_I; intros.
      erewrite split_smem_get_word in H7; try eassumption.
      discriminate.
      left.
      erewrite split_smem_get_word; try eassumption.
      eauto.
      eauto.
      apply injL; intro.
      do 2 (apply existsL; intro).
      apply andL; apply injL; intro.
      apply andL.
      eapply Imply_trans.
      apply rep_inv_ptr.
      apply Imply_trans with [| smem_get_word (implode sm) addr x1 <> None |]%PropX.
      do 2 (apply existsL; intro).
      apply andL; apply injL; intro.
      apply andL.
      apply swap.
      apply Imply_I; apply interp_weaken.
      do 2 (apply existsL; intro).
      apply andL; apply injL; intro.
      apply andL.
      apply existsL; intro.
      apply injL; intuition idtac.
      apply andL.
      apply injL; intuition idtac.
      apply injL; intuition idtac.
      apply Inj_I; intros.
      erewrite split_smem_get_word in H9; try eassumption.
      discriminate.
      left.
      erewrite split_smem_get_word; try eassumption.
      eauto.
      eauto.
      apply injL; intro.
      apply injR; intro; subst.
      case_eq (smem_get_word (implode sm) (fst a0) x); intros; try congruence.
      case_eq (smem_get_word (implode sm) (fst a0) x1); intros; try congruence.
      eapply smem_get_word_disjoint in H4; eauto.
      apply disjoint_comm.
      eapply split_split_disjoint.
      2: eauto.
      apply split_comm; eauto.
      apply injL; intro.
      apply Inj_I; intuition subst.
      tauto.
      eapply H.
      eauto.
    Qed.

    Lemma use_rep_inv_ptr : forall addr a h,
      rep_inv addr a * is_heap h ===> [|~WordMap.In addr h|] * (rep_inv addr a * is_heap h).
      intros; eapply Himp_trans; [ apply use_rep_inv_ptr' | ].
      apply Himp_star_frame; try apply Himp_refl.
      sepLemma.
      intro.
      destruct H0.
      eapply H.
      apply InA_In; apply WordMap.elements_1; eauto.
    Qed.
    Require Import Bedrock.Platform.Cito.WordMapFacts.

    Lemma is_heap_upd_option_bwd : forall h addr a, is_heap h * layout_option addr a ===> is_heap_upd_option h addr a.
      unfold is_heap_upd_option, heap_upd_option, Semantics.heap_upd_option, layout_option; intros.
      destruct a.
      2: sepLemma.
      unfold is_heap at 2.
      assert (In (addr, a) (SemanticsMake.heap_elements (WordMap.WordMap.add addr a h))).
      apply InA_In; apply WordMap.elements_1; apply WordMap.add_1; auto.
      eapply starL_in in H.
      2: apply NoDupA_NoDup; apply WordMap.elements_3w.
      destruct H; intuition idtac.
      eapply Himp_trans; [ | apply H0 ]; clear H0.
      simpl.
      eapply Himp_trans; [ apply Himp_star_comm | ].

      eapply Himp_trans; [ apply use_rep_inv_ptr | ].
      apply Himp_star_pure_c; intro.
      eapply Himp_star_frame; try apply Himp_refl.
      apply starL_permute; auto.
      apply NoDupA_NoDup; apply WordMap.elements_3w.
      split; intro.
      apply H2; clear H2.
      apply In_InA' in H1.
      destruct x0.
      apply WordMap.elements_2 in H1.
      split; intros.
      apply H0.
      eexists.
      injection H2; intros; subst; eauto.
      apply InA_In; apply WordMap.elements_1.
      apply add_mapsto_iff.
      right; intuition subst.
      apply H0; eexists; eauto.

      apply H2 in H1; clear H2.
      intuition idtac.
      destruct x0.
      apply In_InA' in H3; apply WordMap.elements_2 in H3.
      apply InA_In; apply WordMap.elements_1.
      apply add_mapsto_iff in H3.
      intuition subst.
      tauto.
    Qed.

    Definition is_heap_merge h1 h2 := is_heap (heap_merge h1 h2).

    Lemma starL_join : forall A (P : A -> _) ls2, NoDup ls2
      -> forall  ls1, NoDup ls1
        -> forall ls, NoDup ls
          -> (forall x, In x ls <-> In x ls1 \/ In x ls2)
          -> (forall x, In x ls1 -> ~In x ls2)
          -> Bags.starL P ls1 * Bags.starL P ls2 ===> Bags.starL P ls.
      induction 2; simpl; intros.

      eapply Himp_trans; [ apply Himp_star_Emp | ].
      apply starL_permute; auto.
      firstorder.

      assert (In x ls) by firstorder.
      eapply starL_in in H5; auto.
      destruct H5; intuition idtac.
      eapply Himp_trans; [ | apply H6 ]; clear H6.
      eapply Himp_trans; [ apply Himp_star_assoc | ].
      apply Himp_star_frame; try apply Himp_refl.
      apply IHNoDup; auto.
      split; intro.
      apply H8 in H6; clear H8; intuition idtac.
      apply H3 in H8; clear H3; intuition subst.
      tauto.

      intuition idtac.
      apply H8; clear H8; intuition subst.
      tauto.
      apply H3; clear H3.
      intuition idtac.
      apply H8; clear H8; intuition subst.
      eauto.
      apply H3; clear H3; intuition idtac.

      eauto.
    Qed.

    Ltac l := repeat match goal with
                       | [ H : _ |- _ ] => apply In_InA' in H; apply WordMap.elements_2 in H
                       | _ => apply InA_In; apply WordMap.elements_1
                     end.

    Lemma heaps_disjoint : forall ls2, NoDup ls2
      -> forall ls1,
        Bags.starL (fun p => rep_inv (fst p) (snd p)) ls1
        * Bags.starL (fun p => rep_inv (fst p) (snd p)) ls2
        ===> [|forall addr v1 v2, In (addr, v1) ls1 -> ~In (addr, v2) ls2|]
        * (Bags.starL (fun p => rep_inv (fst p) (snd p)) ls1
          * Bags.starL (fun p => rep_inv (fst p) (snd p)) ls2).
      induction ls1; simpl; intros.

      apply Himp_star_pure_cc.
      tauto.
      apply Himp_refl.

      eapply Himp_trans; [ apply Himp_star_assoc | ].

      eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl |
        apply IHls1 ] | ].
      eapply Himp_trans; [ apply Himp_star_assoc' | ].
      eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_star_comm | apply Himp_refl ] | ].
      eapply Himp_trans; [ apply Himp_star_assoc | ].
      apply Himp_star_pure_c; intro.

      eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl |
        apply Himp_star_comm ] | ].
      eapply Himp_trans; [ apply Himp_star_assoc' | ].
      eapply Himp_trans; [ apply Himp_star_frame; [ apply use_rep_inv_ptr' | apply Himp_refl ] | ].
      eapply Himp_trans; [ apply Himp_star_assoc | ].
      apply Himp_star_frame.
      sepLemma.
      intuition (subst; eauto).
      eapply Himp_trans; [ | apply Himp_star_assoc' ].
      eapply Himp_trans; [ | apply Himp_star_frame; [ apply Himp_refl |
        apply Himp_star_comm ] ].
      eapply Himp_trans; [ | apply Himp_star_assoc ].
      apply Himp_refl.
    Qed.

    Lemma is_heap_merge_bwd : forall h1 h2, is_heap h1 * is_heap h2 ===> is_heap_merge h1 h2.
      intros.
      eapply Himp_trans; [ apply heaps_disjoint | ].
      apply NoDupA_NoDup; apply WordMap.elements_3w.
      apply Himp_star_pure_c; intro.
      apply starL_join; try (apply NoDupA_NoDup; apply WordMap.elements_3w); intros.
      intuition idtac; l.
      apply update_mapsto_iff in H0; intuition idtac.
      right; l; auto.
      left; l; auto.
      apply update_mapsto_iff.
      right; intuition idtac.
      destruct H0.
      eapply H.
      apply InA_In; apply WordMap.elements_1; eauto.
      apply InA_In; apply WordMap.elements_1; eauto.
      apply update_mapsto_iff; intuition idtac.
      destruct x; eauto.
    Qed.

    Lemma change_hyp : forall P Q specs st,
      interp specs (![P] st)
      -> P ===> Q
      -> interp specs (![Q] st).
      intros.
      eapply Imply_sound.
      rewrite sepFormula_eq.
      apply H0.
      rewrite sepFormula_eq in *; auto.
    Qed.

    Lemma star_merge_separated : forall specs st other h1 h2 addr adt, interp specs (![is_heap h1 * is_heap h2 * layout_option addr adt * other] st) -> separated (heap_merge h1 h2) addr adt.
      intros.
      hnf.
      destruct adt; simpl in *; auto.
      right.
      intro.

      assert (is_heap h1 * is_heap h2 * rep_inv addr a * other
        ===> rep_inv addr a * is_heap_merge h1 h2 * other).
      generalize (is_heap_merge_bwd h1 h2).
      generalize (is_heap_merge h1 h2), (is_heap h1), (is_heap h2), (rep_inv addr a).
      clear.
      sepLemma.
      etransitivity; [ | apply H ].
      sepLemma.
      eapply change_hyp in H1; eauto.
      assert (rep_inv addr a * is_heap_merge h1 h2 * other
        ===> [| ~WordMap.In addr (update h1 h2) |] * rep_inv addr a * is_heap_merge h1 h2 * other).
      eapply Himp_trans; [ apply Himp_star_assoc | ].
      eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl | apply Himp_star_comm ] | ].
      eapply Himp_trans; [ apply Himp_star_assoc' | ].
      eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_star_comm | apply Himp_refl ] | ].
      eapply Himp_trans; [ apply Himp_star_assoc | ].

      eapply Himp_trans; [ | apply Himp_star_assoc' ].
      eapply Himp_trans; [ | apply Himp_star_frame; [ apply Himp_refl | apply Himp_star_comm ] ].
      eapply Himp_trans; [ | apply Himp_star_assoc' ].
      eapply Himp_trans; [ | apply Himp_star_frame; [ apply Himp_refl | apply Himp_star_assoc ] ].
      eapply Himp_trans; [ | apply Himp_star_frame; [ apply Himp_refl |
        apply Himp_star_frame; [ apply Himp_star_comm | apply Himp_refl ] ] ].
      eapply Himp_trans; [ | apply Himp_star_frame; [ apply Himp_refl |
        apply Himp_star_assoc' ] ].
      eapply Himp_trans; [ | apply Himp_star_assoc ].
      eapply Himp_trans; [ | apply Himp_star_frame; [ apply Himp_star_comm | apply Himp_refl ] ].
      eapply Himp_trans; [ | apply Himp_star_assoc' ].
      apply Himp_star_frame; try apply Himp_refl.
      apply use_rep_inv_ptr.
      eapply change_hyp in H2; eauto.
      rewrite sepFormula_eq in H2.
      propxFo.
    Qed.

    Definition hints_heap_upd_option : TacPackage.
      prepare tt is_heap_upd_option_bwd.
    Defined.

    Definition hints_heap_merge : TacPackage.
      prepare tt is_heap_merge_bwd.
    Defined.

  End TopSection.

End Make.
