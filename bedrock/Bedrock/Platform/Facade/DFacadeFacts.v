Set Implicit Arguments.

Require Import Bedrock.Platform.Facade.FacadeFacts.
Export FacadeFacts.
Require Import Bedrock.Platform.Facade.Facade.
Require Import Bedrock.Platform.Facade.DFacade.

Require Import Bedrock.Platform.Cito.GeneralTactics.
Require Import Bedrock.Platform.Cito.GeneralTactics2.
Require Import Bedrock.Platform.Cito.GeneralTactics4.

Require Import Coq.Bool.Bool.

Require Import Bedrock.StringSet.
Import StringSet.
Require Import Bedrock.Platform.Cito.StringSetFacts.

Lemma is_syntax_ok_seq_elim a b : is_syntax_ok (Seq a b) = true -> is_syntax_ok a = true /\ is_syntax_ok b = true.
Proof.
  intros H.
  unfold is_syntax_ok in *.
  unfold is_good_varnames in *.
  simpl in *.
  eapply andb_true_iff in H.
  openhyp.
  eapply andb_true_iff in H.
  openhyp.
  eapply for_all_union_elim in H0.
  openhyp.
  intuition.
Qed.

Require Import Bedrock.Platform.Facade.NameDecoration.

Definition is_syntax_ok_e e := StringSet.for_all is_good_varname (FreeVarsExpr.free_vars e).

Lemma is_syntax_ok_if_elim e a b : is_syntax_ok (If e a b) = true -> is_syntax_ok_e e = true /\ is_syntax_ok a = true /\ is_syntax_ok b = true.
Proof.
  intros H.
  unfold is_syntax_ok in *.
  unfold is_good_varnames in *.
  simpl in *.
  eapply andb_true_iff in H.
  openhyp.
  eapply andb_true_iff in H.
  openhyp.
  eapply for_all_union_elim in H0.
  openhyp.
  eapply for_all_union_elim in H0.
  openhyp.
  intuition.
Qed.

Lemma is_syntax_ok_while_elim e b : is_syntax_ok (While e b) = true -> is_syntax_ok_e e = true /\ is_syntax_ok b = true.
Proof.
  intros H.
  unfold is_syntax_ok in *.
  unfold is_good_varnames in *.
  simpl in *.
  eapply andb_true_iff in H.
  openhyp.
  eapply for_all_union_elim in H0.
  openhyp.
  intuition.
Qed.

Lemma is_syntax_ok_assign_elim x e : is_syntax_ok (Assign x e) = true -> is_good_varname x = true /\ is_syntax_ok_e e = true.
Proof.
  intros H.
  unfold is_syntax_ok in *.
  unfold is_good_varnames in *.
  simpl in *.
  eapply for_all_union_elim in H.
  openhyp.
  eapply for_all_singleton_elim in H.
  intuition.
Qed.

Require Import Bedrock.Platform.Cito.ListFacts3.

Lemma is_syntax_ok_call_elim x f args : is_syntax_ok (Call x f args) = true -> is_good_varname x = true /\ List.forallb is_good_varname args = true /\ is_no_dup args = true.
Proof.
  intros H.
  unfold is_syntax_ok in *.
  unfold is_good_varnames in *.
  simpl in *.
  eapply andb_true_iff in H.
  openhyp.
  eapply for_all_union_elim in H0.
  openhyp.
  eapply for_all_singleton_elim in H0.
  eapply for_all_of_list_elim in H1.
  intuition.
Qed.

Require Import Bedrock.Platform.Cito.SyntaxExpr.

Lemma is_syntax_ok_e_var_elim x : is_syntax_ok_e (Var x) = true -> is_good_varname x = true.
Proof.
  intros H.
  unfold is_syntax_ok_e in *.
  simpl in *.
  eapply for_all_singleton_elim in H.
  intuition.
Qed.

Lemma is_syntax_ok_e_binop_elim op a b : is_syntax_ok_e (Binop op a b) = true -> is_syntax_ok_e a = true /\ is_syntax_ok_e b = true.
Proof.
  intros H.
  unfold is_syntax_ok_e in *.
  simpl in *.
  eapply for_all_union_elim in H.
  openhyp.
  intuition.
Qed.

Lemma is_syntax_ok_e_test_elim op a b : is_syntax_ok_e (TestE op a b) = true -> is_syntax_ok_e a = true /\ is_syntax_ok_e b = true.
Proof.
  intros H.
  unfold is_syntax_ok_e in *.
  simpl in *.
  eapply for_all_union_elim in H.
  openhyp.
  intuition.
Qed.

Section ADTValue.

  Variable ADTValue : Type.

  Require Import Bedrock.Platform.Cito.Option.

  Notation State := (@State ADTValue).
  Notation Env := (@Env ADTValue).
  Notation Value := (@Value ADTValue).
  Notation Sca := (@SCA ADTValue).

  Lemma safe_if_true : forall (env : Env) e t f st, Safe env (If e t f) st -> is_true st e -> Safe env t st.
  Proof.
    intros.
    inversion H; subst.
    eauto.
    exfalso; eapply is_true_is_false; eauto.
  Qed.

  Lemma safe_if_is_bool : forall (env : Env) e t f st, Safe env (If e t f) st -> is_bool st e.
  Proof.
    intros.
    inversion H; subst.
    eapply is_true_is_bool; eauto.
    eapply is_false_is_bool; eauto.
  Qed.

  Lemma safe_if_false : forall (env : Env) e t f st, Safe env (If e t f) st -> is_false st e -> Safe env f st.
  Proof.
    intros.
    inversion H; subst.
    exfalso; eapply is_true_is_false; eauto.
    eauto.
  Qed.

  Require Import Bedrock.Platform.Cito.SyntaxExpr.

  (* test boolean deciders *)
  Open Scope string_scope.
  Require Import Coq.Lists.List.
  Import ListNotations.

  Require Import Bedrock.StringSet.
  Import StringSet.
  Require Import Bedrock.Platform.Cito.StringSetFacts.

  Import Logic.

  Goal equal (assigned (Seq (Assign "x" (Var "a")) (Assign "y" (Var "b")))) (of_list ["x"; "y"]) = true. Proof. exact eq_refl. Qed.

  Require Import Coq.Strings.String.
  Require Import Coq.Lists.List.
  Require Import Bedrock.Platform.Cito.StringMap.
  Import StringMap.
  Require Import Bedrock.Platform.Cito.StringMapFacts.

  Require Import Bedrock.Platform.Cito.ListFacts3.
  Require Import Bedrock.Platform.Cito.ListFacts4.

  Lemma NoDup_ArgVars : forall spec, NoDup (ArgVars spec).
    intros; destruct spec; simpl; eapply is_no_dup_sound; eauto.
  Qed.

  Lemma not_incl_spec : forall spec, ~ List.In (RetVar spec) (ArgVars spec).
    intros; destruct spec; simpl; eapply negb_is_in_iff; eauto.
  Qed.

  Lemma in_args_not_assigned spec x : List.In x (ArgVars spec) -> ~ StringSet.In x (assigned (Body spec)).
  Proof.
    destruct spec; simpl in *; nintro.
    eapply is_disjoint_iff; eauto.
    split; eauto.
    eapply StringSetFacts.of_list_spec; eauto.
  Qed.

  Lemma safe_seq_1 : forall (env : Env) a b st, Safe env (Seq a b) st -> Safe env a st.
  Proof.
    intros.
    inversion H; subst.
    openhyp.
    eauto.
  Qed.

  Lemma safe_seq_2 : forall (env : Env) a b st, Safe env (Seq a b) st -> forall st', RunsTo env a st st' -> Safe env b st'.
  Proof.
    intros.
    inversion H; subst.
    openhyp.
    eauto.
  Qed.

  Require Import Bedrock.Platform.Cito.GeneralTactics3.

  Lemma safe_while_is_bool (env : Env) e s st : Safe env (While e s) st -> is_bool st e.
  Proof.
    intros H.
    inversion H; unfold_all; subst.
    eapply is_true_is_bool; eauto.
    eapply is_false_is_bool; eauto.
  Qed.

  Notation RunsTo := (@RunsTo ADTValue).

  Lemma not_free_vars_no_change env s st st' x : RunsTo env s st st' -> ~ StringSet.In x (free_vars s) -> find x st' = find x st.
  Proof.
    induction 1; simpl; intros Hnin.
    {
      eauto.
    }
    {
      eapply union_not_iff in Hnin.
      openhyp; rewrite IHRunsTo2; eauto.
    }
    {
      eapply union_not_iff in Hnin.
      destruct Hnin as [Hnin ?].
      eapply union_not_iff in Hnin.
      openhyp; eauto.
    }
    {
      eapply union_not_iff in Hnin.
      destruct Hnin as [Hnin ?].
      eapply union_not_iff in Hnin.
      openhyp; eauto.
    }
    {
      unfold_all.
      simpl in *.
      copy_as Hnin Hnin'.
      eapply union_not_iff in Hnin.
      openhyp; rewrite IHRunsTo2; eauto.
    }
    {
      eauto.
    }
    {
      rename H1 into Hst'.
      eapply union_not_iff in Hnin.
      destruct Hnin as [Hnin1 Hnin2].
      eapply singleton_not_iff in Hnin1.
      rewrite Hst'.
      rewrite add_neq_o by eauto.
      eauto.
    }
    {
      unfold_all.
      simpl in *.
      rename H5 into Hst''.
      eapply union_not_iff in Hnin.
      destruct Hnin as [Hnin1 Hnin2].
      eapply singleton_not_iff in Hnin1.
      eapply of_list_not_iff in Hnin2.
      rewrite Hst''.
      rewrite add_neq_o by eauto.
      eapply not_in_add_remove_many; eauto.
    }
    {
      unfold_all.
      simpl in *.
      rename H6 into Hst''.
      eapply union_not_iff in Hnin.
      destruct Hnin as [Hnin1 Hnin2].
      eapply singleton_not_iff in Hnin1.
      eapply of_list_not_iff in Hnin2.
      rewrite Hst''.
      rewrite add_neq_o by eauto.
      eapply not_in_add_remove_many; eauto.
    }
  Qed.

End ADTValue.
