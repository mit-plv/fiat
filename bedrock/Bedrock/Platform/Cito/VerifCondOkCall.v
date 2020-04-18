Require Import Coq.omega.Omega.
Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.ADT.
Require Import Bedrock.Platform.Cito.RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Bedrock.Platform.Cito.CompileStmtSpec.
  Module Import CompileStmtSpecMake := Make E M.
  Require Import Bedrock.Platform.Cito.CompileStmtImpl.
  Module Import CompileStmtImplMake := Make E M.
  Require Import Bedrock.Platform.Cito.LayoutHints.
  Module Import LayoutHintsMake := LayoutHints.Make E M.
  Require Import Bedrock.Platform.Cito.LayoutHints2.
  Module Import LayoutHints2Make := LayoutHints2.Make E M.
  Require Import Bedrock.Platform.Cito.CompileStmtTactics.
  Module Import CompileStmtTacticsMake := Make E M.
  Import InvMake.
  Import Semantics.
  Import SemanticsMake.
  Import InvMake2.

  Require Import Bedrock.Platform.Cito.WordMapFacts.
  Require Import Bedrock.Platform.Cito.InvFacts.
  Module Import InvFactsMake := Make E.
  Module Inner := InvFactsMake.Make(M).

  Section TopSection.

    Require Import Bedrock.Platform.Cito.Inv.

    Variable vars : list string.

    Variable temp_size : nat.

    Variable imports : LabelMap.t assert.

    Variable imports_global : importsGlobal imports.

    Variable modName : string.

    Require Import Bedrock.Platform.Cito.Syntax.
    Require Import Bedrock.Platform.Wrap.

    Variable rv_postcond : W -> vals -> Prop.

    Notation do_compile := (compile vars temp_size rv_postcond imports_global modName).

    Require Import Bedrock.Platform.Cito.SemanticsFacts.
    Require Import Bedrock.Platform.Cito.SynReqFacts.
    Require Import Bedrock.Platform.Cito.ListFacts4.
    Require Import Bedrock.Platform.Cito.ListFacts5.
    Require Import Bedrock.StringSet.
    Import StringSet.
    Require Import Bedrock.Platform.Cito.StringSetTactics.

    Hint Resolve Subset_syn_req_In.
    Hint Extern 0 (Subset _ _) => progress (simpl; subset_solver).
    Hint Resolve map_length.

    Set Printing Coercions.

    Require Import Bedrock.Platform.Cito.SemanticsExpr.
    Require Import Bedrock.Platform.Cito.SepHints.
    Require Import Bedrock.Platform.Cito.GeneralTactics.
    Require Import Bedrock.Platform.Cito.WordFacts.
    Require Import Coq.Arith.Arith.
    Require Import Bedrock.Platform.Cito.VerifCondOkTactics.

    Open Scope nat.

    Lemma replace1 : forall a b c d e : W, a ^+ b ^+ c ^+ d ^+ e = a ^+ (b ^+ c ^+ d ^+ e).
      intros; repeat rewrite wplus_assoc in *; eauto.
    Qed.

    Lemma replace_it3 : forall a b, 2 <= a -> b <= a - 2 -> $ (a) ^- $ (S (S b)) = natToW (a - 2 - b).
      intros; replace (a - 2 - b) with (a - (2 + b)) by omega; rewrite natToW_minus; eauto.
    Qed.

    Ltac inversion_Safe :=
      repeat match goal with
               | H : Safe _ _ _ |- _ => inversion H; clear H; subst
             end.

    Transparent funcs_ok.
    Ltac unfold_funcs_ok :=
      match goal with
        | H : interp _ (funcs_ok _ _) |- _ => generalize H; intro is_funcs_ok; unfold funcs_ok in H
      end.
    Opaque funcs_ok.

    Ltac specialize_funcs_ok :=
      match goal with
        | H : context [ (_ ---> _)%PropX ], H2 : _ = Some _ |- _ =>
          specialize (Imply_sound (H _ _ _) (Inj_I _ _ H2)); propxFo
      end.

    Ltac hide_map :=
      repeat match goal with
               | H : context [ map ?A _ ] |- _ => set (map A _) in *
             end.

    Ltac auto_apply :=
      match goal with
          H : _ |- _ => eapply H
      end.

    Lemma fold_2S_length : forall A (ls : list A), S (S (length ls)) = 2 + length ls.
      eauto.
    Qed.

    Ltac gen_le :=
      try rewrite fold_2S_length in *;
      match goal with
        | H : (natToW (2 + length ?ls) <= natToW (?n))%word |- _ => assert (2 + length ls <= n) by (eapply wle_goodSize_le; eauto; eapply syn_req_goodSize; eauto); assert (2 <= n) by omega; assert (length ls <= n - 2) by omega
      end.

    Opaque mult.
    Opaque star. (* necessary to use eapply_cancel *)
    Opaque funcs_ok.
    Opaque CompileStmtSpecMake.InvMake2.funcs_ok.
    Opaque CompileStmtImplMake.InvMake2.funcs_ok.
    Require Import Bedrock.Platform.Cito.SepHints2 Bedrock.Platform.Cito.SepHintsUtil.

    Lemma firstn_length : forall A B (l : list A) (l' : list B),
      length l <= length l'
      -> length l = length (firstn (length l) l').
      induction l; destruct l'; simpl; intuition.
    Qed.

    Hint Extern 1 (length _ = length _) => apply firstn_length.

    Hint Extern 1 (length ?L = _) => subst L; rewrite length_upd_sublist; assumption.
    Ltac inversion_Safe' :=
      repeat match goal with
               | H : Safe _ _ _ |- _ => unfold Safe in H
               | H : Semantics.Safe _ _ _ |- _ => inversion H; clear H; subst
             end.
    Opaque funcs_ok.
    Ltac specialize_funcs_ok' :=
      match goal with
        | H : context [ (_ ---> _)%PropX ], H2 : _ = Some _ |- _ =>
          specialize (Imply_sound (H _ _) (Inj_I _ _ H2)); propxFo
      end.
    Require Import Bedrock.Platform.Cito.SepHints3.
    Require Import Bedrock.Platform.Cito.SepHints4.
    Opaque funcs_ok.
    Require Import Bedrock.Platform.Cito.SemanticsUtil.
    Lemma forall_word_adt_match_good_scalars : forall h pairs, List.Forall (word_adt_match h) pairs -> List.Forall (@word_scalar_match ADTValue) pairs.
      intros.
      eapply Forall_weaken.
      2 : eassumption.
      intros.
      destruct x.
      unfold word_adt_match, Semantics.word_adt_match, word_scalar_match in *; simpl in *.
      destruct v; simpl in *; intuition.
    Qed.
    Require Import Bedrock.Platform.Cito.SemanticsFacts6.
    Require Import Bedrock.Platform.Cito.SemanticsFacts5.

    Definition are_the_same h0 x18 := is_heap h0 ===> is_heap x18.

    Lemma verifCond_ok :
      forall o e l k (pre : assert),
        let s := Syntax.Call o e l in
        vcs (verifCond vars temp_size s k rv_postcond pre) ->
        vcs
          (VerifCond (do_compile s k pre)).
    Proof.

      unfold verifCond, imply.

      (* call *)
      wrap0.

      (* vc 1 *)
      unfold stack_slot in *.
      rewrite fold_4_mult_1 in *.
      eapply H2 in H.
      unfold precond in *.
      change CompileStmtSpecMake.InvMake2.inv with inv in *.
      unfold inv, inv_template, is_state in *.
      unfold has_extra_stack in *.
      post.
      hiding ltac:(evaluate auto_ext).

      (* vc 2 *)
      unfold stack_slot in *.
      rewrite fold_4_mult_1 in *.
      eapply H2 in H3.
      unfold precond in *.
      change CompileStmtSpecMake.InvMake2.inv with inv in *.
      unfold inv, inv_template, is_state in *.
      unfold has_extra_stack in *.
      post.
      hiding ltac:(evaluate auto_ext).

      (* vc 3 *)
      unfold CompileExprs.imply in *.
      unfold CompileExprs.new_pre in *.
      unfold CompileExprs.is_state in *.
      post.
      eapply H2 in H0.
      unfold precond in *.
      change CompileStmtSpecMake.InvMake2.inv with inv in *.
      unfold inv, inv_template, is_state in *.
      unfold has_extra_stack in *.
      post.
      unfold stack_slot in *.
      rewrite fold_4_mult_1 in *.
      hiding ltac:(evaluate auto_ext).
      destruct_state.
      hide_evalInstrs.
      gen_le.
      hiding ltac:(evaluate hints_buf_2_fwd).
      hiding ltac:(evaluate hints_array).
      rewrite (@replace_array_to_split x8 _ (length l)) in H17.
      assert (splittable x8 (length l)) by (unfold splittable; omega).
      hiding ltac:(evaluate hints_array_split).
      fold (@firstn W) in *.
      fold (@skipn W) in *.
      (*rewrite fold_4_mult in *.*)
      intros.
      descend.
      unfold callee_stack_start in *.
      unfold frame_len in *.
      unfold temp_start in *.
      unfold vars_start in *.
      post.
      match goal with
        | H : _ = temp_size |- _ => rewrite H in *
      end.
      match goal with
        | H : Regs s0 Sp = _ |- _ => rewrite H in *
      end.
      rewrite fold_4_mult_2 in *.
      rewrite Mult.mult_plus_distr_l in *.
      rewrite_natToW_plus.
      repeat rewrite natToW_plus.
      repeat rewrite wplus_assoc in *.
      repeat hiding ltac:(step auto_ext).
      eauto.
      fold (@firstn W) in *.
      apply firstn_length; omega.

      (* vc 4*)
      eapply syn_req_Call_args; eauto.

      (* vc 5*)
      unfold CompileExpr.imply in *.
      unfold CompileExpr.new_pre in *.
      unfold CompileExpr.is_state in *.
      post.
      eapply H2 in H0.
      unfold precond in *.
      change CompileStmtSpecMake.InvMake2.inv with inv in *.
      unfold inv, inv_template, is_state in *.
      unfold has_extra_stack in *.
      post.
      unfold stack_slot in *.
      rewrite fold_4_mult_1 in *.
      hiding ltac:(evaluate auto_ext).
      destruct_state.
      unfold CompileExprs.post in *.
      unfold CompileExprs.runs_to in *.
      unfold CompileExprs.is_state in *.
      hide_evalInstrs.
      gen_le.
      hiding ltac:(evaluate hints_buf_2_fwd).
      hiding ltac:(evaluate hints_array).
      rewrite (@replace_array_to_split x9 _ (length l)) in H18.
      assert (splittable x9 (length l)) by (unfold splittable; omega).
      hiding ltac:(evaluate hints_array_split).
      fold (@firstn W) in *.
      fold (@skipn W) in *.
      (*rewrite fold_4_mult in *.*)
      unfold callee_stack_start in *.
      unfold frame_len in *.
      unfold temp_start in *.
      unfold vars_start in *.
      simpl in *.
      match goal with
        | H : _ = temp_size |- _ => rewrite H in *
      end.
      match goal with
        | H : Regs x0 Sp = _ |- _ => rewrite H in *
      end.
      rewrite fold_4_mult_2 in *.
      rewrite Mult.mult_plus_distr_l in *.
      rewrite_natToW_plus.
      repeat rewrite natToW_plus in H3.
      repeat rewrite wplus_assoc in *.

      transit.

      fold (@skipn W) in *.
      post.
      descend.
      hide_upd_sublist.
      hide_map.
      repeat hiding ltac:(step auto_ext).
      rewrite length_upd_sublist; eauto.

      (* vc 6 *)
      eapply syn_req_Call_f; eauto.

      (* vc 7 *)
      eapply H2 in H3.
      unfold precond in *.
      change CompileStmtSpecMake.InvMake2.inv with inv in *.
      unfold inv, inv_template, is_state in *.
      unfold has_extra_stack in *.
      post.
      unfold stack_slot in *.
      rewrite fold_4_mult_1 in *.
      hiding ltac:(evaluate auto_ext).
      destruct_state.
      unfold CompileExprs.runs_to in *.
      unfold CompileExprs.is_state in *.
      simpl in *.
      hide_evalInstrs.
      gen_le.
      hiding ltac:(evaluate hints_buf_2_fwd).
      hiding ltac:(evaluate hints_array).
      rewrite (@replace_array_to_split x10 _ (length l)) in H19.
      assert (splittable x10 (length l)) by (unfold splittable; omega).
      hiding ltac:(evaluate hints_array_split).
      fold (@firstn W) in *.
      fold (@skipn W) in *.
      (*rewrite fold_4_mult in *.*)
      unfold callee_stack_start in *.
      unfold frame_len in *.
      unfold temp_start in *.
      unfold vars_start in *.
      match goal with
        | H : _ = temp_size |- _ => rewrite H in *
      end.
      match goal with
        | H : Regs x0 Sp = _ |- _ => rewrite H in *
      end.
      rewrite fold_4_mult_2 in *.
      rewrite Mult.mult_plus_distr_l in *.
      rewrite_natToW_plus.
      repeat rewrite natToW_plus in H5.
      repeat rewrite wplus_assoc in *.
      transit.
      fold (@firstn W) in *.
      fold (@skipn W) in *.
      post.
      unfold CompileExpr.runs_to in *.
      unfold CompileExpr.is_state in *.
      simpl in *.
      hide_upd_sublist.
      hide_map.

      transit.

      fold (@firstn W) in *.
      fold (@skipn W) in *.
      post.
      unfold callee_stack_slot in *.
      unfold callee_stack_start in *.
      unfold frame_len in *.
      unfold temp_start in *.
      unfold vars_start in *.
      match goal with
        | H : _ = Regs x1 Sp |- _ => rewrite <- H in *
      end.
      match goal with
        | H : _ = Regs x Sp |- _ => rewrite <- H in *
      end.
      rewrite fold_4_mult_1 in *.
      rewrite fold_4_mult_2 in *.
      rewrite_natToW_plus.
      repeat rewrite wplus_assoc in *.
      repeat rewrite replace1 in *.
      generalize dependent H20.
      hide_evalInstrs.
      clear_all.
      intros.
      hiding ltac:(evaluate auto_ext).

      (* vc 8 *)
      eapply H2 in H3.
      unfold precond in *.
      change CompileStmtSpecMake.InvMake2.inv with inv in *.
      unfold inv, inv_template, is_state in *.
      unfold has_extra_stack in *.
      post.
      unfold stack_slot in *.
      rewrite fold_4_mult_1 in *.
      hiding ltac:(evaluate auto_ext).
      destruct_state.
      unfold CompileExprs.runs_to in *.
      unfold CompileExprs.is_state in *.
      simpl in *.
      hide_evalInstrs.
      gen_le.
      hiding ltac:(evaluate hints_buf_2_fwd).
      hiding ltac:(evaluate hints_array).
      rewrite (@replace_array_to_split x11 _ (length l)) in H20.
      assert (splittable x11 (length l)) by (unfold splittable; omega).
      hiding ltac:(evaluate hints_array_split).
      fold (@firstn W) in *.
      fold (@skipn W) in *.
      (*rewrite fold_4_mult in *.*)
      unfold callee_stack_start in *.
      unfold frame_len in *.
      unfold temp_start in *.
      unfold vars_start in *.
      match goal with
        | H : _ = temp_size |- _ => rewrite H in *
      end.
      match goal with
        | H : Regs x1 Sp = _ |- _ => rewrite H in *
      end.
      rewrite fold_4_mult_2 in *.
      rewrite Mult.mult_plus_distr_l in *.
      rewrite_natToW_plus.
      repeat rewrite natToW_plus in H6.
      repeat rewrite wplus_assoc in *.
      transit.
      fold (@firstn W) in *.
      fold (@skipn W) in *.
      post.
      unfold CompileExpr.runs_to in *.
      unfold CompileExpr.is_state in *.
      simpl in *.
      hide_upd_sublist.
      hide_map.
      transit.
      fold (@firstn W) in *.
      fold (@skipn W) in *.
      post.
      unfold callee_stack_slot in *.
      unfold callee_stack_start in *.
      unfold frame_len in *.
      unfold temp_start in *.
      unfold vars_start in *.
      rewrite fold_4_mult_1 in *.
      rewrite fold_4_mult_2 in *.
      rewrite_natToW_plus.
      repeat rewrite wplus_assoc in *.
      match goal with
        | H : _ = Regs x2 Sp |- _ => rewrite <- H in *
      end.
      match goal with
        | H : _ = Regs x0 Sp |- _ => rewrite <- H in *
      end.
      repeat rewrite replace1 in *.
      hide_all_eq_except H6.
      hiding ltac:(evaluate auto_ext).
      fold (@firstn W) in *.
      fold (@skipn W) in *.
      intros.

      inversion_Safe'.

      (* internal *)
      unfold_all.
      simpl in *.
      Transparent funcs_ok.
      unfold_funcs_ok.
      Opaque funcs_ok.
      simpl in *.
      repeat rewrite wplus_assoc in *.
      post.

      specialize_funcs_ok'.
      descend.
      rewriter.
      eauto.
      eapply Imply_sound.
      eauto.
      hiding ltac:(step auto_ext).

      hide_upd_sublist.
      set (arr := map _ _) in *.
      set (avars := ArgVars _) in *.
      rewrite (@replace_array_to_locals arr _ avars) in H7.
      Require Import ListFacts3.
      assert (array_to_locals_ok arr avars) by (unfold_all; unfold array_to_locals_ok; descend; [ rewrite map_length; eauto | eapply is_no_dup_sound; eapply (NoDupArgVars _) ]).
      hiding ltac:(evaluate hints_array_to_locals).
      fold (@skipn W) in *.

      unfold_all.
      set (ls := skipn _ _) in *.
      hide_map.
      assert (to_elim ls) by (unfold to_elim; eauto); hiding ltac:(evaluate hints_array_elim).
      unfold_all.
      rewrite CancelIL.skipn_length in *.

      descend.
      clear_Imply.
      clear_evalInstrs.
      unfold is_state in *.
      unfold has_extra_stack in *.
      unfold frame_len_w in *.
      unfold frame_len in *.
      unfold temp_start in *.
      unfold vars_start in *.
      simpl in *.
      rewrite H.
      rewrite fold_4_mult_2 in *.
      rewrite_natToW_plus.
      repeat rewrite wplus_assoc in *.
      clear_Forall_PreCond.

      set (array nil _) in *.
      unfold array in h0.
      simpl in h0.
      subst h0.

      instantiate (5 := (_, _)); simpl.

      match goal with
        | H : length _ = _ - 2 |- _ => rewrite H in *
      end.
      unfold toArray in *.
      erewrite (map_eq_length_eq _ (ArgVars _)) in * by eauto.

      rewrite replace_it3 in * by eauto.
      rewrite plus_0_r in *.
      rewrite_natToW_plus.
      repeat rewrite wplus_assoc in *.

      hide_upd_sublist.
      hide_map.
      set (ArgVars _) in *.
      set (_ - _ - _) in *.
      generalize dependent H37; clear_all; intros.

      repeat hiding ltac:(step auto_ext).

      auto_apply.
      eauto.
      eauto.

      (* post call *)
      eapply existsR.
      change CompileStmtImplMake.InvMake2.funcs_ok with funcs_ok in *.
      change CompileStmtImplMake.InvMake.SemanticsMake.Heap with Heap in *.
      change CompileStmtImplMake.InvMake2.is_state with is_state in *.
      change CompileStmtImplMake.InvMake2.is_heap with is_heap in *.
      change CompileStmtImplMake.InvMake2.layout_option with layout_option in *.
      change CompileStmtImplMake.InvMake.SemanticsMake.heap_merge with heap_merge in *.
      change CompileStmtImplMake.InvMake.SemanticsMake.State with State in *.
      apply andR.
      apply Imply_I.
      apply interp_weaken.
      eauto.

      descend.
      generalize H13.
      clear_Imply.

      hide_upd_sublist.
      intros.

      hiding ltac:(step auto_ext).
      hiding ltac:(step auto_ext).

      instantiate (2 := None).
      instantiate (2 := $0).
      simpl.
      instantiate (2 := heap_empty).

      unfold is_state in *.
      unfold has_extra_stack in *.
      unfold frame_len_w in *.
      unfold frame_len in *.
      unfold temp_start in *.
      unfold vars_start in *.
      simpl in *.
      openhyp.
      match goal with
        | H : Regs x15 Sp = _ |- _ => rewrite H in *
      end.
      rewrite H in *.
      rewrite wplus_wminus in *.

      set (array nil _) in *.
      unfold array in h0.
      simpl in h0.
      subst h0.

      instantiate (7 := l0).
      unfold_all.
      repeat rewrite length_upd_sublist in *.

      rewrite plus_0_r in *.
      rewrite fold_4_mult_2 in *.
      repeat rewrite Mult.mult_plus_distr_l in *.
      rewrite_natToW_plus.
      set (len1 := 4 * length vars) in *.
      set (len2 := 4 * length x6) in *.
      set (w := Regs x Sp ^+ $8) in *.
      replace (_ ^+ natToW (len1 + len2)) with (w ^+ $ (len1) ^+ $ (len2)) by (rewrite natToW_plus; rewrite wplus_assoc; eauto).
      unfold_all.
      repeat rewrite wplus_assoc in *.

      hide_upd_sublist.
      hide_le.
      unfold toArray in *.
      match goal with
        | H : map _ _ = map _ _ |- _ => eapply map_eq_length_eq in H
      end.

      match goal with
        | H : length (ArgVars _) = _ |- _ => rewrite H in *
      end.

      match goal with
        | H : length (ArgVars _) = _ |- _ => generalize dependent H
      end.

      clear_all.
      intros.

      hiding ltac:(step auto_ext).

      rewrite fold_first in *.
      set (Regs _ _ ^+ _ ^+ _ ^+ _) in *.
      set (length l) in *.
      set (_ - _ - _) in *.

      replace (w =?> x8)%Sep with (buf_to_split w x8 2) by (unfold buf_to_split; eauto).
      assert (buf_splittable x8 2) by (unfold buf_splittable; eauto).
      hiding ltac:(step hints_buf_split_bwd).
      post.
      hiding ltac:(step auto_ext).

      rewrite fold_first in *.
      unfold_all.
      set (w := Regs _ _ ^+ _ ^+ _ ^+ _ ^+ _) in *.
      set (big := x8 - _) in *.
      set (small := length l) in *.
      replace (w =?> big)%Sep with (buf_to_split w big small) by (unfold buf_to_split; eauto).
      assert (buf_splittable big small) by (unfold_all; unfold buf_splittable; eauto).
      hiding ltac:(step hints_buf_split_bwd).

      rewrite fold_first in *.
      (*rewrite fold_4_mult in *.*)
      hiding ltac:(step auto_ext).

      rewrite fold_first in *.
      set (avars := ArgVars _) in *.
      assert (locals_to_elim avars) by (unfold locals_to_elim; eauto).
      hiding ltac:(step hints_elim_locals).
      unfold_all.
      match goal with
        | H : length (ArgVars _) = _ |- _ => rewrite H in *
      end.
      hiding ltac:(step auto_ext).

      hiding ltac:(step hints_heap_empty_bwd).

      rewrite fold_second in *.
      simpl in *.
      openhyp.
      descend.
      match goal with
        | H : Regs _ Rv = _ |- _ => rewrite H
      end.
      auto_apply.
      econstructor; simpl in *.
      eauto.
      unfold toArray in *.
      match goal with
        | H : map _ _ = map _ _ |- _ => rewrite <- H
      end.
      reflexivity.
      unfold heap_merge in *.
      rewrite update_with_empty; eauto.
      unfold_all; repeat rewrite length_upd_sublist in *; eauto.

      eauto.

      destruct_state.

      unfold is_state in *.
      unfold has_extra_stack in *.
      simpl in *.
      hiding ltac:(step auto_ext).
      hiding ltac:(step auto_ext).
      hiding ltac:(step auto_ext).
      hiding ltac:(step auto_ext).
      instantiate (2 := (_, _)); simpl in *.
      clear_all.

      hiding ltac:(step auto_ext).

      descend.
      2 : words.

      econstructor.
      2 : eauto.
      match goal with
        | H : Regs _ Rv = _ |- _ => rewrite H
      end.
      econstructor; simpl in *.
      eauto.
      unfold toArray in *.
      match goal with
        | H : map _ _ = map _ _ |- _ => rewrite <- H
      end.
      reflexivity.
      unfold heap_merge in *; rewrite update_with_empty; eauto.

      (* foreign *)
      unfold_all.
      simpl in *.
      Transparent funcs_ok.
      unfold_funcs_ok.
      Opaque funcs_ok.
      simpl in *.
      repeat rewrite wplus_assoc in *.
      post.
      specialize_funcs_ok'.
      descend.
      rewriter.
      eauto.
      eapply Imply_sound.
      eauto.
      hiding ltac:(step auto_ext).

      descend.
      clear_Imply.
      clear_evalInstrs.
      instantiate (2 := pairs).
      unfold is_state in *.
      unfold has_extra_stack in *.
      unfold frame_len_w in *.
      unfold frame_len in *.
      unfold temp_start in *.
      unfold vars_start in *.
      simpl in *.
      rewrite H.
      match goal with
        | H : map _ _ = map _ _ |- _ => set (map_fst := map fst) in *; rewrite <- H; subst map_fst
      end.
      rewrite map_length in *.
      hide_upd_sublist.
      hide_all_eq.
      hide_upd_sublist.
      hide_map.
      set (ls := skipn _ _) in *.
      assert (to_elim ls) by (unfold to_elim; eauto); hiding ltac:(evaluate hints_array_elim).
      intros.
      unfold_all.
      rewrite CancelIL.skipn_length in *.
      match goal with
        | H : length _ = _ - 2 |- _ => rewrite H in *
      end.
      rewrite replace_it3 in * by eauto.
      rewrite Mult.mult_0_r in *.
      rewrite wplus_0 in *.
      rewrite fold_4_mult_2 in *.
      rewrite_natToW_plus.
      repeat rewrite wplus_assoc in *.

      hide_upd_sublist.
      hide_map.
      set (_ - _ - _) in *.

      set (locals nil _ _ _) in *.
      unfold locals in h0.
      unfold array in h0.
      simpl in h0.
      subst h0.

      repeat match goal with
               | H : interp _ _ |- _ => generalize dependent H
               | H : Semantics.good_inputs _ _ |- _ => generalize dependent H
             end.
      clear_all; intros.

      repeat hiding ltac:(step auto_ext).

      replace (is_heap h) with (heap_to_split h pairs) by (unfold heap_to_split; eauto).
      hiding ltac:(step hints_split_heap).
      unfold Semantics.good_inputs in *; openhyp; eauto.
      unfold Semantics.good_inputs in *; openhyp.
      Opaque funcs_ok.
      eapply forall_word_adt_match_good_scalars; eauto.
      eauto.
      eauto.

      (* post call *)
      eapply existsR.
      change LayoutHints2Make.InvMake2.is_heap with is_heap in *.
      change LayoutHints2Make.InvMake.SemanticsMake.heap_diff with heap_diff in *.
      change CompileStmtImplMake.InvMake2.funcs_ok with funcs_ok in *.
      change CompileStmtImplMake.InvMake.SemanticsMake.Heap with Heap in *.
      change CompileStmtImplMake.InvMake2.is_state with is_state in *.
      change CompileStmtImplMake.InvMake2.is_heap with is_heap in *.
      change CompileStmtImplMake.InvMake2.layout_option with layout_option in *.
      change CompileStmtImplMake.InvMake.SemanticsMake.heap_merge with heap_merge in *.
      change CompileStmtImplMake.InvMake.SemanticsMake.State with State in *.
      apply andR.
      apply Imply_I.
      apply interp_weaken.
      eauto.

      descend.
      generalize H13.
      clear_Imply.

      hide_upd_sublist.
      intros.

      hiding ltac:(step auto_ext).

      unfold is_state in *.
      unfold has_extra_stack in *.
      unfold frame_len_w in *.
      unfold frame_len in *.
      unfold temp_start in *.
      unfold vars_start in *.
      simpl in *.
      match goal with
        | H : Regs x14 Sp = _ |- _ => rewrite H in *
      end.
      rewrite H in *.
      rewrite wplus_wminus in *.

      set (locals nil _ _ _) in *.
      unfold locals in h0.
      unfold array in h0.
      simpl in h0.
      subst h0.

      hide_upd_sublist.
      instantiate (10 := l0).
      unfold_all.
      repeat rewrite length_upd_sublist in *.

      rewrite Mult.mult_0_r in *.
      rewrite wplus_0 in *.
      rewrite fold_4_mult_2 in *.
      rewrite Mult.mult_plus_distr_l in *.
      rewrite_natToW_plus.
      set (len1 := 4 * length vars) in *.
      set (len2 := 4 * length x6) in *.
      set (w := Regs x Sp ^+ $8) in *.
      replace (_ ^+ natToW (len1 + len2)) with (w ^+ $ (len1) ^+ $ (len2)) by (rewrite natToW_plus; rewrite wplus_assoc; eauto).
      unfold_all.
      repeat rewrite wplus_assoc in *.

      hide_upd_sublist.
      match goal with
        | H : map _ _ = map _ _ |- _ => generalize H; eapply map_eq_length_eq in H; intro
      end.
      rewrite make_triples_length in * by eauto.
      assert (length x15 = length l) by (rewriter; eauto).
      repeat match goal with
               | H : length _ = length l |- _ => generalize dependent H
             end.
      hide_le.
      clear_all.
      intros.
      set (fold_left _ _ _) in *.
      set (heap_diff _ _) in *.
      hiding ltac:(step auto_ext).
      assert (to_elim x15) by (unfold to_elim; eauto).
      hiding ltac:(step hints_array_elim).
      match goal with
        | H : length _ = length l |- _ => rewrite H in *
      end.
      set (Regs _ _ ^+ _ ^+ _ ^+ _) in *.
      set (length l) in *.
      set (_ - _ - _) in *.

      replace (w =?> x8)%Sep with (buf_to_split w x8 2) by (unfold buf_to_split; eauto).
      assert (buf_splittable x8 2) by (unfold buf_splittable; eauto).
      hiding ltac:(step hints_buf_split_bwd).
      post.
      hiding ltac:(step auto_ext).

      unfold_all.
      set (w := Regs _ _ ^+ _ ^+ _ ^+ _ ^+ _) in *.
      set (big := x8 - _) in *.
      set (small := length l) in *.
      replace (w =?> big)%Sep with (buf_to_split w big small) by (unfold buf_to_split; eauto).
      assert (buf_splittable big small) by (unfold_all; unfold buf_splittable; eauto).
      hiding ltac:(step hints_buf_split_bwd).

      rewrite fold_first in *.
      rewrite fold_second in *.
      simpl in *.

      descend.
      match goal with
        | H : Regs _ Rv = _ |- _ => rewrite H
      end.
      eapply Safe_Equal; eauto.
      auto_apply.
      econstructor; simpl in *.
      eauto.
      match goal with
        | H : map _ _ = map _ _ |- _ => rewrite H
      end.
      rewrite make_triples_Word; eauto.
      rewrite make_triples_Word_ADTIn; eauto.
      rewrite make_triples_ADTIn; eauto.
      eauto.
      eapply separated_Equal; eauto.
      apply heap_merge_store_out; eauto.
      apply heap_upd_option_Equal.
      2 : reflexivity.
      eapply heap_merge_store_out; eauto.

      unfold_all; repeat rewrite length_upd_sublist in *; eauto.

      eauto.

      destruct_state.

      unfold is_state in *.
      unfold has_extra_stack in *.
      simpl in *.
      hiding ltac:(step auto_ext).
      hiding ltac:(step auto_ext).
      eapply RunsTo_Equal in H36.
      simpl in H36; destruct H36; intuition idtac.
      hiding ltac:(step auto_ext).
      hiding ltac:(step auto_ext).

      Focus 2.
      rewrite fold_first in *.
      rewrite fold_second in *.
      simpl in *.
      descend.
      econstructor.
      eapply RunsToCallForeign; simpl in *.
      eauto.
      match goal with
        | H : map _ _ = map _ _ |- _ => rewrite H
      end.
      rewrite make_triples_Word; eauto.
      rewrite make_triples_Word_ADTIn; eauto.
      rewrite make_triples_ADTIn; eauto.
      eauto.
      eapply separated_Equal; eauto.
      apply heap_merge_store_out; eauto.
      reflexivity.
      simpl.
      match goal with
        | H : Regs _ Rv = _ |- _ => rewrite H in H41
      end.
      eassumption.
      Unfocus.
      assert (Hheap : are_the_same h0 x18) by (apply Inner.is_heap_Equal; assumption).
      generalize Hheap; clear_all.
      intros; hiding ltac:(step auto_ext).
      hiding ltac:(step auto_ext).

      words.
      words.
      eauto.
      apply heap_upd_option_Equal.
      eapply heap_merge_store_out; eauto.

      (* vc 9 *)
      post.
      generalize H4.
      hide_evalInstrs; clear_all; intros.
      hiding ltac:(evaluate auto_ext).

      (* vc 10 *)
      unfold SaveRet.imply in *.
      wrap0.
      change CompileStmtImplMake.InvMake.SemanticsMake.Callee with Callee in *.
      change CompileStmtImplMake.InvMake2.funcs_ok with funcs_ok in *.
      change CompileStmtImplMake.InvMake.SemanticsMake.Heap with Heap in *.
      change CompileStmtImplMake.InvMake2.is_state with is_state in *.
      change CompileStmtImplMake.InvMake2.is_heap with is_heap in *.
      change CompileStmtImplMake.InvMake2.layout_option with layout_option in *.
      change CompileStmtImplMake.InvMake.SemanticsMake.heap_merge with heap_merge in *.
      change CompileStmtImplMake.InvMake.SemanticsMake.State with State in *.
      post.
      destruct_state.
      hiding ltac:(evaluate auto_ext).
      unfold is_state in *.
      unfold SaveRet.is_state in *.
      match goal with
        | H : _ = Regs _ _ ^- _ |- _ => rewrite <- H in *
      end.
      simpl in *.
      descend.
      repeat hiding ltac:(step auto_ext).

      (* vc 11 *)
      eapply syn_req_Call_ret; eauto.
    Qed.

  End TopSection.

End Make.
