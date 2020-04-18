Require Import Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Require Import Bedrock.Expr Bedrock.Env.
Require Import Coq.Classes.EquivDec Bedrock.EqdepClass.
Require Import Bedrock.DepList.
Require Import Bedrock.Word Bedrock.Prover.
Require Import Bedrock.provers.ReflexivityProver Bedrock.sep.Locals.

Set Implicit Arguments.
Set Strict Implicit.

(** * The Word Prover **)

Require Import Coq.Arith.Arith Bedrock.ILEnv Bedrock.Memory.

Section LocalsProver.
  Variable types' : list type.
  Definition types := Locals.types types'.
  Variable funcs' : functions types.
  Definition funcs := Locals.funcs funcs'.

  Definition localsSimplify (e : expr types) : expr types :=
    match e with
      | Func 11 (vs :: Const t nm :: nil) =>
        match t return tvarD types t -> _ with
          | tvType 6 => fun nm => sym_sel vs nm
          | _ => fun _ => e
        end nm
      | _ => e
    end.

  Definition localsProve (_ : unit) (goal : expr types) :=
    match goal with
      | Equal _ x y => expr_seq_dec (localsSimplify x) (localsSimplify y)
      | _ => false
    end.

  Lemma localsSimplify_correct : forall uvars vars (e : expr types) t v,
    exprD funcs uvars vars e t = Some v
    -> exprD funcs uvars vars (localsSimplify e) t = Some v.
    destruct e; simpl; intuition idtac.
    do 12 (destruct f; try assumption).
    do 2 (destruct l; try assumption).
    destruct e0; try assumption.
    destruct l; try assumption.
    destruct t0; try assumption.
    do 7 (destruct n; try assumption).
    simpl in *.
    destruct (equiv_dec (tvType 0) t); try discriminate.
    hnf in e0; subst.
    generalize (sym_sel_correct funcs' uvars vars t1 e).
    unfold funcs in *.
    match type of H with
      | match ?E with Some _ => _ | _ => _ end _ _ = _ => destruct E; try discriminate
    end.
    injection H; clear H; intros; subst.
    auto.
  Qed.

  Theorem localsProveCorrect : ProverCorrect funcs reflexivityValid localsProve.
    unfold localsProve; hnf; simpl; intros.

    destruct goal; try discriminate.
    destruct H1.
    apply expr_seq_dec_correct in H0.
    hnf.
    simpl in *.
    generalize (localsSimplify_correct uvars vars goal1 t).
    generalize (localsSimplify_correct uvars vars goal2 t).
    destruct (exprD funcs uvars vars goal1 t); try discriminate.
    destruct (exprD funcs uvars vars goal2 t); try discriminate.
    intros.
    specialize (H2 _ (refl_equal _)).
    specialize (H3 _ (refl_equal _)).
    congruence.
  Qed.

  Definition localsProver : ProverT types :=
    {| Facts := unit
      ; Summarize := reflexivitySummarize
      ; Learn := reflexivityLearn
      ; Prove := localsProve |}.

  Definition localsProver_correct : ProverT_correct localsProver funcs.
    eapply Build_ProverT_correct with (Valid := reflexivityValid : _ -> _ -> Facts localsProver -> Prop); unfold reflexivityValid; eauto.
    apply localsProveCorrect.
  Qed.

End LocalsProver.

Definition LocalsProver : ProverPackage :=
{| ProverTypes := Locals.types_r
 ; ProverFuncs := Locals.funcs_r
 ; Prover_correct := localsProver_correct
|}.
