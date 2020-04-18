Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.ADT.
Require Import Bedrock.Platform.Cito.RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Bedrock.Platform.Cito.VerifCondOkNonCall.
  Module Import VerifCondOkNonCallMake := Make E M.
  Require Import Bedrock.Platform.Cito.VerifCondOkNonCall2.
  Module Import VerifCondOkNonCall2Make := Make E M.
  Require Import Bedrock.Platform.Cito.VerifCondOkCall.
  Module Import VerifCondOkCallMake := Make E M.
  Import CompileStmtSpecMake.
  Import InvMake.
  Import Semantics.
  Import SemanticsMake.
  Import InvMake2.

  Section TopSection.

    Require Import Bedrock.Platform.AutoSep.

    Variable vars : list string.

    Variable temp_size : nat.

    Variable imports : LabelMap.t assert.

    Variable imports_global : importsGlobal imports.

    Variable modName : string.

    Variable rv_postcond : W -> vals -> Prop.

    Notation do_compile := (CompileStmtImplMake.compile vars temp_size rv_postcond imports_global modName).

    Lemma verifCond_ok :
      forall s k (pre : assert),
        vcs (verifCond vars temp_size s k rv_postcond pre) ->
        vcs
          (VerifCond (do_compile s k pre)).
    Proof.

      unfold verifCond, imply; induction s.

      eapply verifCond_ok_skip; eauto.
      eapply verifCond_ok_seq; eauto.
      eapply verifCond_ok_if; eauto.
      eapply verifCond_ok_while; eauto.

      eapply verifCond_ok; eauto.

      eapply verifCond_ok_label; eauto.
      eapply verifCond_ok_assign; eauto.

    Qed.

  End TopSection.

End Make.
