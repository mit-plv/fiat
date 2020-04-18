Require Import Coq.omega.Omega.
Require Import Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Require Import Bedrock.Expr Bedrock.Env.
Require Import Coq.Classes.EquivDec Bedrock.EqdepClass.
Require Import Bedrock.DepList.
Require Import Bedrock.Word Bedrock.Prover.
Require Import Bedrock.sep.Array Bedrock.IL.
Require Import Bedrock.Arrays.

Set Implicit Arguments.


Local Notation pcT := (tvType 0).
Local Notation stT := (tvType 1).
Local Notation wordT := (tvType 0).
Local Notation natT := (tvType 4).
Local Notation listWT := (tvType 5).

Local Notation wltF := 4.
Local Notation natToWF := 5.
Local Notation lengthF := 6.
Local Notation selF := 7.
Local Notation updF := 8.


Section ArrayBoundProver.
  Variable types' : list type.
  Definition types := Array.types types'.
  Variable funcs' : functions types.
  Definition funcs := Array.funcs funcs'.

  Fixpoint deupd (e : expr types) : expr types :=
    match e with
      | Func updF (e' :: _ :: _ :: nil) => deupd e'
      | _ => e
    end.

  Definition factIn (e : expr types) : option (expr types * expr types) :=
    match e with
      | Func wltF (i :: Func natToWF (Func lengthF (a :: nil) :: nil) :: nil) =>
        Some (i, deupd a)
      | _ => None
    end.

  Definition boundSummary := list (expr types * expr types).

  Definition boundLearn1 (summ : boundSummary) (e : expr types) : boundSummary :=
    match factIn e with
      | None => summ
      | Some fact => fact :: summ
    end.

  Fixpoint boundLearn (summ : boundSummary) (es : list (expr types)) : boundSummary :=
    match es with
      | nil => summ
      | e :: es => boundLearn1 (boundLearn summ es) e
    end.

  Definition boundSummarize := boundLearn nil.

  Fixpoint hypMatches (fact : expr types * expr types) (summ : boundSummary) : bool :=
    match summ with
      | nil => false
      | (i, a) :: summ' => (expr_seq_dec i (fst fact) && expr_seq_dec a (snd fact)) || hypMatches fact summ'
    end.

  Definition boundProve (summ : boundSummary) (goal : expr types) :=
    match factIn goal with
      | None => false
      | Some fact => hypMatches fact summ
    end.

  Fixpoint size (e : expr types) : nat :=
    match e with
      | Const _ _ => O
      | Var _ => O
      | UVar _ => O
      | Func _ es => fold_left plus (map size es) 1
      | Equal _ e1 e2 => size e1 + size e2
      | Not e1 => size e1
    end.

  Lemma plus_monotone : forall ls n, (fold_left plus ls n >= n)%nat.
    induction ls; simpl; intuition.
    specialize (IHls (n + a)); omega.
  Qed.

  Lemma repr_nth_error : forall A (v : A) r ls n,
    nth_error r.(footprint) n = Some (Some v)
    -> nth_error (repr r ls) n = Some v.
    destruct r; simpl; induction footprint; simpl; intuition.
    destruct n; simpl in *; discriminate.
    destruct n; simpl in *.
    injection H; clear H; intros; subst; reflexivity.
    eapply IHfootprint in H; clear IHfootprint.
    destruct a; eauto.
  Qed.

  Lemma deupd_correct : forall uvars vars sz (e : expr types),
    (size e <= sz)%nat
    -> match exprD funcs uvars vars e listWT with
         | None => True
         | Some ev =>
           match exprD funcs uvars vars (deupd e) listWT with
             | None => False
             | Some dv => length dv = length ev
           end
       end.
    induction sz; destruct e; simpl size; simpl deupd; simpl exprD; intuition eauto; try discriminate;
      try solve [ destruct (equiv_dec t listWT); auto
        | match goal with
            | [ |- match ?E with Some _ => _ | None => _ end ] => destruct E; auto
          end ].

    specialize (plus_monotone (map size l) 1); omega.
    do 8 (destruct f; [ t | ]).
    destruct f; [ | t ].

    replace (nth_error funcs 8) with (Some (upd_r types'))
      by (unfold funcs, Array.funcs; erewrite repr_nth_error; reflexivity).
    simpl.
    do 3 (destruct l; [ t | ]).
    destruct l; [ | t ].
    simpl.
    specialize (IHsz e).
    simpl in H.
    assert (size e <= sz)%nat by omega; intuition.
    destruct (exprD funcs uvars vars e listWT); auto.
    destruct (exprD funcs uvars vars (deupd e) listWT); try tauto.
    destruct (exprD funcs uvars vars e0 wordT); auto.
    destruct (exprD funcs uvars vars e1 wordT); auto.
    rewrite upd_length; assumption.
  Qed.

  Ltac duh' := match goal with
                 | [ |- match ?E with Some _ => _ | _ => _ end ] => destruct E
               end; try tauto.

  Ltac duh := solve [ repeat duh' ].

  Lemma factIn_correct : forall uvars vars (e : expr types),
    match exprD funcs uvars vars e tvProp with
      | None => True
      | Some P => match factIn e with
                    | None => True
                    | Some (i, a) =>
                      exists iv, exprD funcs uvars vars i wordT = Some iv
                        /\ exists av, exprD funcs uvars vars a listWT = Some av
                          /\ (P = (iv < $ (length av)))
                  end
    end.
    destruct e; simpl factIn; simpl exprD; intuition; try duh.
    do 5 (destruct f; try duh).
    do 3 (destruct l; try duh).

    Focus 2.
    destruct (nth_error funcs 4); auto.
    destruct (equiv_dec (Range s) tvProp); auto.
    destruct s; simpl in e2.
    hnf in e2; subst.

    simpl applyD.
    duh'.
    destruct e0; auto.
    do 6 (destruct f; auto).
    destruct l0; auto.
    destruct e0; auto.
    do 7 (destruct f; auto).
    do 2 (destruct l1; auto).
    destruct l0; auto.

    replace (nth_error funcs 4) with (Some (ILEnv.wlt_r types))
      by (unfold funcs, Array.funcs; erewrite repr_nth_error; reflexivity).
    match goal with
      | [ |- match ?E with None => _ | Some _ => _ end ] =>
        let E' := eval simpl in E in change E with E'
    end.
    case_eq (exprD funcs uvars vars e wordT); intuition.
    case_eq (exprD funcs uvars vars e0 wordT); intuition.
    destruct e0; auto.
    do 6 (destruct f; auto).
    destruct l; auto.
    destruct e0; auto.
    do 7 (destruct f; auto).
    do 2 (destruct l0; auto).
    destruct l; auto.
    simpl in H0.
    specialize (deupd_correct uvars vars (sz := size e0) e0).
    assert (size e0 <= size e0)%nat by auto; intuition.
    destruct (exprD funcs uvars vars e0 listWT); try discriminate.
    destruct (exprD funcs uvars vars (deupd e0) listWT); try tauto.
    do 2 esplit; eauto.
    do 2 esplit; eauto.
    injection H0; clear H0; intros; subst.
    rewrite H3.
    reflexivity.
  Qed.

  Section vars.
    Variables uvars vars : env types.

    Definition pairValid (p : expr types * expr types) :=
      exists i, exprD funcs uvars vars (fst p) wordT = Some i
        /\ exists a, exprD funcs uvars vars (snd p) listWT = Some a
          /\ i < $ (length a).

    Definition boundValid (summ : boundSummary) :=
      List.Forall pairValid summ.

    Theorem boundLearn1Correct : forall sum,
      boundValid sum
      -> forall hyp, Provable funcs uvars vars hyp
        -> boundValid (boundLearn1 sum hyp).
    Proof.
      unfold Provable, boundLearn1, boundValid; intros.
      specialize (factIn_correct uvars vars hyp).
      destruct (exprD funcs uvars vars hyp tvProp); try tauto.
      destruct (factIn hyp); intuition.
      destruct p.
      do 2 destruct H1.
      do 2 destruct H2.
      subst.
      unfold pairValid.
      constructor; eauto.
    Qed.

    Hint Resolve boundLearn1Correct.

    Theorem boundLearnCorrect : forall sum,
      boundValid sum
      -> forall hyps, AllProvable funcs uvars vars hyps
        -> boundValid (boundLearn sum hyps).
    Proof.
      induction hyps; simpl; intuition.
    Qed.

    Theorem boundSummarizeCorrect : forall hyps,
      AllProvable funcs uvars vars hyps
      -> boundValid (boundSummarize hyps).
      intros; apply boundLearnCorrect; hnf; auto.
    Qed.

    Lemma hypMatchesCorrect : forall p sum,
      boundValid sum
      -> hypMatches p sum = true
      -> pairValid p.
      induction sum as [ | [ ] ]; simpl; intuition.
      apply orb_prop in H0; intuition.
      apply andb_prop in H1; intuition.
      apply expr_seq_dec_correct in H0.
      apply expr_seq_dec_correct in H2.
      subst.
      inversion H; auto.
      inversion H; auto.
    Qed.
  End vars.

  Hint Resolve boundLearnCorrect boundSummarizeCorrect.

  Theorem boundProverCorrect : ProverCorrect funcs boundValid boundProve.
    hnf; intros.
    unfold boundProve in H0.
    hnf.
    specialize (factIn_correct uvars vars goal).
    destruct H1.
    rewrite H1 in *.
    destruct (factIn goal); try discriminate.
    eapply hypMatchesCorrect in H0; eauto.
    destruct H0.
    destruct p.
    destruct H0.
    destruct H2.
    destruct H2.
    intro.
    destruct H4.
    destruct H4.
    destruct H5.
    destruct H5.
    subst.
    unfold fst, snd in *.
    congruence.
  Qed.

  Hint Resolve boundProverCorrect.

  Lemma boundValid_weaken : forall (u g : env types) (f : boundSummary)
    (ue ge : list (sigT (tvarD types))),
    boundValid u g f -> boundValid (u ++ ue) (g ++ ge) f.
    induction 1; simpl; intuition; constructor; auto.
    hnf in H; hnf.
    do 2 destruct H.
    do 2 destruct H1.
    eauto 10 using exprD_weaken.
  Qed.

  Hint Resolve boundValid_weaken.

  Definition boundProver : ProverT types :=
    {| Facts := boundSummary
      ; Summarize := boundSummarize
      ; Learn := boundLearn
      ; Prove := boundProve |}.

  Definition boundProver_correct : ProverT_correct boundProver funcs.
    eapply Build_ProverT_correct with (Valid := boundValid); eauto.
  Qed.

End ArrayBoundProver.

Definition BoundProver : ProverPackage :=
{| ProverTypes := Array.types_r
 ; ProverFuncs := Array.funcs_r
 ; Prover_correct := boundProver_correct
|}.
