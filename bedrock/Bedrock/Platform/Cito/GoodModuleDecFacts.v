Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.GoodModuleDec.

Section TopSection.

  Notation MName := SyntaxModule.Name.
  Notation FName := SyntaxFunc.Name.
  Notation Funcs := SyntaxModule.Functions.

  Require Import Bedrock.Platform.Cito.IsGoodModule.
  Require Import Bedrock.Platform.Cito.GoodModule.

  Require Import Bedrock.Platform.Cito.ListFacts4.
  Require Import Coq.Lists.List.

  Require Import Coq.Bool.Bool.
  Require Import Bedrock.Platform.Cito.GeneralTactics.
  Require Import Bedrock.Platform.Cito.GeneralTactics2.

  Require Import Coq.Program.Basics.
  Require Import Bedrock.Platform.Cito.GoodFunc.

  Require Import Bedrock.Platform.Cito.WellFormed.

  Lemma is_good_size_sound : forall n, is_good_size n = true -> goodSize n.
    intros.
    unfold is_good_size in *.
    Local Open Scope N_scope.
    destruct (ZArith_dec.Dcompare_inf (N.of_nat n ?= Npow2 32)) as [ [Hc | Hc] | Hc ]; rewrite Hc in *.
    discriminate.
    eapply N.compare_lt_iff in Hc; eauto.
    discriminate.
  Qed.

  Hint Constructors args_not_too_long.

  Lemma is_arg_len_ok_sound : forall s, is_arg_len_ok s = true -> wellformed s.
    unfold wellformed.
    induction s; simpl; intuition eauto.
    eapply andb_true_iff in H; openhyp; eauto.
    eapply andb_true_iff in H; openhyp; eauto.
    econstructor.
    eapply is_good_size_sound; eauto.
  Qed.
  Require Import Bedrock.Platform.Cito.ListFacts3.
  Require Import Bedrock.Platform.Cito.NoUninitDecFacts.

  Lemma is_good_func_sound : forall f, is_good_func f = true -> GoodFunc f.
    unfold is_good_func.
    intros.
    repeat (eapply andb_true_iff in H; openhyp).
    econstructor.
    eauto.
    split.
    eapply is_no_uninited_sound; eauto.
    split.
    eapply is_arg_len_ok_sound; eauto.
    eapply is_good_size_sound; eauto.
  Qed.

  Lemma is_good_funcs_sound : forall ls, is_good_funcs (map Core ls) = true -> Forall (compose GoodFunc Core) ls.
    intros.
    unfold is_good_funcs in *.
    eapply Forall_forall.
    intros.
    eapply forallb_forall in H.
    2 : eapply in_map; eauto.
    unfold compose.
    eapply is_good_func_sound; eauto.
  Qed.
  Require Import Bedrock.Platform.Cito.NameDecoration.

  Lemma is_good_module_sound : forall m, is_good_module m = true -> IsGoodModule m.
    intros.
    unfold is_good_module in *.
    destruct m; simpl in *.
    eapply andb_true_iff in H.
    openhyp.
    eapply andb_true_iff in H.
    openhyp.
    econstructor; simpl.
    eapply is_good_module_name_sound; eauto.
    split.
    eapply is_good_funcs_sound; eauto.
    eapply is_no_dup_sound; eauto.
  Qed.

End TopSection.
