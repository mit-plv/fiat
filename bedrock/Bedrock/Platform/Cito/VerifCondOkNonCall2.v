Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.ADT.
Require Import Bedrock.Platform.Cito.RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Bedrock.Platform.Cito.CompileStmtSpec.
  Module Import CompileStmtSpecMake := Make E M.
  Require Import Bedrock.Platform.Cito.CompileStmtImpl.
  Module Import CompileStmtImplMake := Make E M.
  Require Import Bedrock.Platform.Cito.CompileStmtTactics.
  Module Import CompileStmtTacticsMake := Make E M.
  Import InvMake.
  Import Semantics.
  Import SemanticsMake.
  Import InvMake2.

  Require Import Bedrock.Platform.Cito.SemanticsFacts.
  Module Import SemanticsFactsMake := Make E.

  Section TopSection.

    Variable vars : list string.

    Variable temp_size : nat.

    Variable imports : LabelMap.t assert.

    Variable imports_global : importsGlobal imports.

    Variable modName : string.

    Require Import Bedrock.Platform.Cito.Syntax.
    Require Import Bedrock.Platform.Wrap.

    Variable rv_postcond : W -> vals -> Prop.

    Notation do_compile := (compile vars temp_size rv_postcond imports_global modName).

    Require Import Bedrock.Platform.Cito.SynReqFacts.
    Require Import Bedrock.Platform.Cito.ListFacts5.
    Require Import Bedrock.StringSet.
    Import StringSet.
    Require Import Bedrock.Platform.Cito.StringSetTactics.

    Opaque mult.
    Opaque star. (* necessary to use eapply_cancel *)
    Opaque funcs_ok.
    Opaque CompileStmtSpecMake.InvMake2.funcs_ok.
    Opaque CompileStmtImplMake.InvMake2.funcs_ok.

    Hint Resolve Subset_syn_req_In.
    Hint Extern 0 (Subset _ _) => progress (simpl; subset_solver).
    Hint Resolve map_length.

    Set Printing Coercions.

    Require Import Bedrock.Platform.Cito.SemanticsExpr.
    Require Import Bedrock.Platform.Cito.GeneralTactics.
    Require Import Bedrock.Platform.Cito.VerifCondOkTactics.
    Require Import Bedrock.Platform.Cito.WordFacts.
    Require Import Bedrock.Platform.Cito.SynReqFacts2.
    Require Import Bedrock.Platform.Cito.SynReqFacts3.

    Open Scope nat.
    Ltac inversion_Safe :=
      repeat match goal with
               | H : Safe _ _ _ |- _ => unfold Safe in H
               | H : Semantics.Safe _ _ _ |- _ => inversion H; clear H; subst
             end.
    Ltac auto_apply_in t :=
      match goal with
          H : _ |- _ => eapply t in H
      end.
    Transparent evalInstrs.
    Require Import Bedrock.Platform.Cito.ConvertLabel.
    Opaque evalInstrs.

    Lemma verifCond_ok_label :
      forall x lbl k (pre : assert),
        let s := Syntax.Label x lbl in
        vcs (verifCond vars temp_size s k rv_postcond pre) ->
        vcs
          (VerifCond (do_compile s k pre)).
    Proof.

      unfold verifCond, imply.
      wrap0.
      eapply H2 in H.
      unfold precond in *.
      change CompileStmtSpecMake.InvMake2.inv with inv in *.
      unfold inv in *.
      unfold inv_template in *.
      unfold is_state in *.
      post.
      unfold var_slot in *.
      unfold vars_start in *.
      destruct_state.

      inversion_Safe.

      auto_apply_in ex_up.
      openhyp.
      simpl in *.
      rewrite_natToW_plus.
      assert (List.In x vars) by (eapply syn_req_Label_in; eauto).
      assert (
          evalInstrs stn st
                     (IL.Assign
                        (LvMem (Imm (Regs st Sp ^+ $8 ^+ $ (variablePosition vars x))))
                        (RvImm x2) :: nil) =
          None
        ) ; [ | clear H0 ].
      rewrite <- H0.
      Transparent evalInstrs.
      simpl.
      repeat rewrite wplus_assoc in *.
      unfold from_bedrock_label_map in *.
      rewrite H.
      eauto.
      Opaque evalInstrs.
      unfold from_bedrock_label_map in *.
      hiding ltac:(evaluate auto_ext).
    Qed.

    Lemma verifCond_ok_assign :
      forall x e k (pre : assert),
        let s := Syntax.Assign x e in
        vcs (verifCond vars temp_size s k rv_postcond pre) ->
        vcs
          (VerifCond (do_compile s k pre)).
    Proof.

      unfold verifCond, imply.
      wrap0.
      unfold CompileExpr.imply in *.
      unfold CompileExpr.new_pre in *.
      unfold CompileExpr.is_state in *.
      intros.
      eapply H2 in H.
      unfold precond in *.
      change CompileStmtSpecMake.InvMake2.inv with inv in *.
      unfold inv in *.
      unfold inv_template in *.
      unfold is_state in *.
      post.
      descend.
      repeat hiding ltac:(step auto_ext).
      eauto.
      eapply syn_req_Assign_e; eauto.

      eapply H2 in H3.
      unfold precond in *.
      change CompileStmtSpecMake.InvMake2.inv with inv in *.
      unfold inv in *.
      unfold inv_template in *.
      unfold CompileExpr.runs_to in *.
      unfold is_state in *.
      unfold CompileExpr.is_state in *.
      post.

      transit.

      destruct_state.
      post.
      unfold var_slot in *.
      unfold vars_start in *.
      rewrite_natToW_plus.
      assert (List.In x vars) by (eapply syn_req_Assign_in; eauto).
      assert (
          evalInstrs stn st
                     (IL.Assign
                        (LvMem (Imm (Regs st Sp ^+ $8 ^+ $ (variablePosition vars x))))
                        Rv :: nil) =
          None
        ) ; [ | clear H0 ].
      rewrite <- H0.
      Transparent evalInstrs.
      simpl.
      repeat rewrite wplus_assoc in *.
      eauto.
      Opaque evalInstrs.
      hiding ltac:(evaluate auto_ext).
    Qed.

  End TopSection.

End Make.
