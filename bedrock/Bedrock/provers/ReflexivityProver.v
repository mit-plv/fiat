Require Import Coq.Lists.List.
Require Import Bedrock.Expr Bedrock.Env.
Require Import Bedrock.Word Bedrock.Prover.

Set Implicit Arguments.
Set Strict Implicit.

Local Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

(** * The Reflexivity Prover **)

Section ReflexivityProver.
  Context {types : list type}.
  Variable fs : functions types.

  Definition reflexivityValid (_ _ : env types) (_ : unit) := True.

  Definition reflexivitySummarize (_ : list (expr types)) := tt.

  Definition reflexivityProve (_ : unit) (goal : expr types) :=
    match goal with
      | Equal _ x y => if expr_seq_dec x y then true else false
      | _ => false
    end.

  Definition reflexivityLearn (sum : unit) (hyps : list (expr types)) := sum.

  Lemma reflexivitySummarizeCorrect : forall uvars vars hyps,
    AllProvable fs uvars vars hyps ->
    reflexivityValid uvars vars (reflexivitySummarize hyps).
  Proof.
    unfold reflexivityValid; auto.
  Qed.

  Lemma reflexivityLearnCorrect : forall uvars vars sum,
    reflexivityValid uvars vars sum -> forall hyps,
    AllProvable fs uvars vars hyps ->
    reflexivityValid uvars vars (reflexivityLearn sum hyps).
  Proof.
    unfold reflexivityValid; auto.
  Qed.

  Theorem reflexivityProverCorrect : ProverCorrect fs reflexivityValid reflexivityProve.
    unfold reflexivityProve; t.
  Qed.

  Definition reflexivityProver : ProverT types :=
  {| Facts := unit
   ; Summarize := fun _ => tt
   ; Learn := fun x _ => x
   ; Prove := reflexivityProve
   |}.
  Definition reflexivityProver_correct : ProverT_correct reflexivityProver fs.
  eapply Build_ProverT_correct with (Valid := reflexivityValid);
    eauto using reflexivitySummarizeCorrect, reflexivityLearnCorrect, reflexivityProverCorrect.
  Qed.

End ReflexivityProver.

Definition ReflexivityProver : ProverPackage :=
{| ProverTypes := nil_Repr EmptySet_type
 ; ProverFuncs := fun ts => nil_Repr (Default_signature ts)
 ; Prover_correct := fun ts fs => reflexivityProver_correct fs
|}.

Ltac unfold_reflexivityProver H :=
  match H with
    | tt =>
      cbv delta [
        reflexivityProver
        reflexivitySummarize reflexivityLearn reflexivityProve
        expr_seq_dec
      ]
    | _ =>
      cbv delta [
        reflexivityProver
        reflexivitySummarize reflexivityLearn reflexivityProve
        expr_seq_dec
      ] in H
  end.
