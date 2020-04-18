Require Import Coq.Lists.List.
Require Import Bedrock.Expr Bedrock.Env.
Require Import Bedrock.Prover.
Require Import Bedrock.Reflection.

Set Implicit Arguments.
Set Strict Implicit.

Local Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

(** * The Assumption Prover **)

Section AssumptionProver.
  Variable types : list type.
  Variable fs : functions types.

  Definition assumption_summary : Type := list (expr types).

  Definition assumptionSummarize (hyps : list (expr types)) : assumption_summary := hyps.

  Fixpoint assumptionProve (hyps : assumption_summary)
    (goal : expr types) : bool :=
    match hyps with
      | nil => false
      | exp :: b => if expr_seq_dec exp goal
        then true
        else assumptionProve b goal
    end.

  Definition assumptionLearn (sum : assumption_summary) (hyps : list (expr types)) : assumption_summary :=
    sum ++ hyps.

  Definition assumptionValid (uvars vars : env types) (sum : assumption_summary) : Prop :=
    AllProvable fs uvars vars sum.

  Lemma assumptionValid_extensible : forall u g f ue ge,
    assumptionValid u g f -> assumptionValid (u ++ ue) (g ++ ge) f.
  Proof.
    unfold assumptionValid. eauto using AllProvable_weaken.
  Qed.

  Lemma assumptionSummarizeCorrect : forall uvars vars hyps,
    AllProvable fs uvars vars hyps ->
    assumptionValid uvars vars (assumptionSummarize hyps).
  Proof.
    auto.
  Qed.

  Lemma assumptionLearnCorrect : forall uvars vars sum,
    assumptionValid uvars vars sum -> forall hyps,
    AllProvable fs uvars vars hyps ->
    assumptionValid uvars vars (assumptionLearn sum hyps).
  Proof.
    unfold assumptionLearn, assumptionValid. intuition.
    apply AllProvable_app; auto.
  Qed.

  Theorem assumptionProverCorrect : ProverCorrect fs assumptionValid assumptionProve.
    t; induction sum; t.
  Qed.

  Definition assumptionProver : ProverT types :=
  {| Facts := assumption_summary
   ; Summarize := assumptionSummarize
   ; Learn := assumptionLearn
   ; Prove := assumptionProve
   |}.
  Definition assumptionProver_correct : ProverT_correct (types := types) assumptionProver fs.
  eapply Build_ProverT_correct with (Valid := assumptionValid);
    eauto using assumptionValid_extensible, assumptionSummarizeCorrect, assumptionLearnCorrect, assumptionProverCorrect.
  Qed.

End AssumptionProver.

Definition AssumptionProver : ProverPackage :=
{| ProverTypes := nil_Repr EmptySet_type
 ; ProverFuncs := fun ts => nil_Repr (Default_signature ts)
 ; Prover_correct := fun ts fs => assumptionProver_correct fs
|}.
