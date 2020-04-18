Require Import Bedrock.Platform.Cito.CompileStmtSpec.
Require Import Bedrock.StringSet.
Require Import Bedrock.Platform.Cito.FreeVars.
Require Import Bedrock.Platform.Cito.SynReqFactsUtil.

Local Infix ";;" := Syntax.Seq (right associativity, at level 95).

Lemma syn_req_Label_in : forall vars temp_size x lbl k, syn_req vars temp_size (Syntax.Label x lbl ;; k) -> List.In x vars.
  unfold syn_req, in_scope; simpl; intuition.
  apply Subset_union_left in H; intuition.
  apply Subset_singleton in H0.
  apply to_set_In; auto.
Qed.

Lemma syn_req_Assign_in : forall vars temp_size x e k, syn_req vars temp_size (Syntax.Assign x e ;; k) -> List.In x vars.
  unfold syn_req, in_scope; simpl; intuition.
  apply Subset_union_left in H; intuition.
  apply Subset_union_left in H0; intuition.
  apply Subset_singleton in H.
  apply to_set_In; auto.
Qed.
