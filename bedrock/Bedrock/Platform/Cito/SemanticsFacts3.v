Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.ADT.

Module Make (Import E : ADT).

  Require Import Bedrock.Platform.Cito.Semantics.
  Module Import SemanticsMake := Semantics.Make E.

  Section TopSection.

    Local Infix ";;" := Syntax.Seq (right associativity, at level 95).

    Lemma RunsTo_Seq_Label :
      forall lbls fs x lbl k vs h v' w,
        lbls lbl = Some w ->
        RunsTo (lbls, fs) k (Locals.upd vs x w, h) v' ->
        RunsTo (lbls, fs) (Syntax.Label x lbl ;; k) (vs, h) v'.
      intros.
      econstructor.
      econstructor; eauto.
      eauto.
    Qed.

    Lemma RunsTo_Seq_Assign :
      forall env x e k vs h v',
        RunsTo env k (Locals.upd vs x (SemanticsExpr.eval vs e), h) v' ->
        RunsTo env (Syntax.Assign x e ;; k) (vs, h) v'.
      intros.
      econstructor.
      econstructor; eauto.
      eauto.
    Qed.

  End TopSection.

End Make.
