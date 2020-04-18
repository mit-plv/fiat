Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.NoUninitDec.

Require Bedrock.Platform.Cito.Wf.
Require Import Coq.Bool.Bool.

Require Import Bedrock.Platform.Cito.GeneralTactics2.

Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Require Import Bedrock.StringSet.
Import StringSet.
Require Import Bedrock.Platform.Cito.StringSetFacts.
Import FSetNotations.
Import FSetNotationsTrial.
Local Open Scope fset_scope.

Lemma inits_elim stmt : forall x, In x (inits stmt) -> Wf.writes stmt x.
Proof.
  induction stmt; simpl; intros x Hin.
  - eapply empty_iff in Hin; eauto.
  - eapply union_iff in Hin.
    destruct Hin as [Hin | Hin].
    + left; eauto.
    + right; eauto.
  - eapply inter_iff in Hin.
    destruct Hin as [Hin1 Hin2].
    eauto.
  - eapply empty_iff in Hin; eauto.
  - destruct o as [lhs|]; simpl in *.
    + eapply singleton_iff in Hin.
      eauto.
    + eapply empty_iff in Hin; eauto.
  - eapply singleton_iff in Hin.
    eauto.
  - eapply singleton_iff in Hin.
    eauto.
Qed.

Require Import Bedrock.Platform.Cito.GeneralTactics Bedrock.Platform.Cito.GeneralTactics4.

Require Import Bedrock.Platform.Cito.FreeVarsExpr.

Lemma expReads_free_vars e : forall uninited x, Wf.expReads uninited e x -> In x (free_vars e) /\ uninited x.
Proof.
  induction e; simpl; intros uninited x Hr.
  - openhyp.
    split; eauto.
    eapply singleton_iff; eauto.
  - intuition.
  - destruct Hr as [Hr | Hr].
    + eapply IHe1 in Hr.
      openhyp.
      split; eauto.
      eapply union_iff; eauto.
    + eapply IHe2 in Hr.
      openhyp.
      split; eauto.
      eapply union_iff; eauto.
  - destruct Hr as [Hr | Hr].
    + eapply IHe1 in Hr.
      openhyp.
      split; eauto.
      eapply union_iff; eauto.
    + eapply IHe2 in Hr.
      openhyp.
      split; eauto.
      eapply union_iff; eauto.
Qed.

Definition disj uninited inited := forall x, uninited x -> In x inited -> False.

Lemma expReads_free_vars_diff e x uninited inited : Wf.expReads uninited e x -> disj uninited inited -> In x (free_vars e - inited).
Proof.
  intros Hr Hdisj.
  eapply diff_iff.
  eapply expReads_free_vars in Hr.
  openhyp; split; eauto.
Qed.

Require Import Coq.Strings.String.

Definition sub_set (a : string -> Prop) b := forall x, a x -> In x b.

Lemma ExistsR_fold_left' elt (ls : list elt) : forall a0 b0 a b all, sub_set a0 b0 -> (forall e, sub_set (a e) (b e)) -> (forall x, all x <-> (a0 x \/ Wf.ExistsR (fun e => a e x) ls)) -> sub_set all (fold_left (fun acc e => b e + acc) ls b0).
Proof.
  induction ls; simpl; intros a0 b0 af bf all Hss0 Hss Heq.
  - unfold sub_set in *.
    intros x Hin.
    eapply Heq in Hin.
    openhyp; intuition.
  - eapply IHls; eauto.
    + instantiate (1 := fun x => a0 x \/ af a x).
      unfold sub_set in *.
      intros x Ha.
      eapply union_iff.
      intuition.
    + intros x.
      etransitivity.
      eauto.
      intuition.
Qed.

Lemma ExistsR_fold_left elt (ls : list elt) : forall a0 b0 a b, sub_set a0 b0 -> (forall e, sub_set (a e) (b e)) -> sub_set (fun x => a0 x \/ Wf.ExistsR (fun e => a e x) ls) (fold_left (fun acc e => b e + acc) ls b0).
Proof.
  intros.
  eapply ExistsR_fold_left'; eauto.
  intuition.
Qed.

Lemma uninited_reads_intro' stmt : forall x uninited inited, Wf.reads uninited stmt x -> disj uninited inited -> In x (uninited_reads inited stmt).
Proof.
  induction stmt; simpl; intros x uninited inited Hr Hdisj.
  - eapply empty_iff; eauto.
  - eapply union_iff.
    destruct Hr as [Hr1 | Hr2].
    + left.
      eauto.
    + right.
      eapply IHstmt2; eauto.
      intros x' Hu Hi.
      simpl in *.
      eapply union_iff in Hi.
      destruct Hu as [Hu Hnw].
      destruct Hi as [Hi | Hi].
      * eauto.
      * contradict Hnw.
        eapply inits_elim; eauto.
  - eapply union_iff.
    destruct Hr as [Hr | [Hr | Hr]].
    + left.
      eapply union_iff.
      left.
      eapply expReads_free_vars_diff; eauto.
    + left.
      eapply union_iff.
      right.
      eauto.
    + right.
      eauto.
  - eapply union_iff.
    destruct Hr as [Hr | Hr].
    + left.
      eapply expReads_free_vars_diff; eauto.
    + right.
      eauto.
  - eapply ExistsR_fold_left; eauto; unfold sub_set in *.
    intros; eapply expReads_free_vars_diff; eauto.
    intros; eapply expReads_free_vars_diff; eauto.
  - eapply empty_iff; eauto.
  - eapply expReads_free_vars_diff; eauto.
Qed.

Lemma uninited_reads_intro stmt : forall x inited, Wf.reads (fun x => ~ List.In x inited) stmt x -> In x (uninited_reads (of_list inited) stmt).
Proof.
  intros.
  eapply uninited_reads_intro'; eauto.
  unfold disj.
  intros x' Hni Hi.
  eapply of_list_fwd in Hi.
  intuition.
Qed.

Require Import Bedrock.Platform.Cito.FuncCore.

Lemma is_no_uninited_reads_sound f : is_no_uninited_reads f = true -> forall x, ~ Wf.reads (fun x => ~ List.In x (ArgVars f)) (Body f) x.
Proof.
  intros Hb x.
  unfold is_no_uninited_reads in *.
  nintro.
  eapply uninited_reads_intro in H.
  eapply is_empty_iff in Hb.
  contradict H.
  eauto.
Qed.

Lemma is_no_uninited_sound f : is_no_uninited f = true -> Wf.NoUninitialized (ArgVars f) (RetVar f) (Body f).
Proof.
  intros Hb.
  unfold is_no_uninited, Wf.NoUninitialized in *.
  eapply andb_true_iff in Hb.
  destruct Hb as [Hnur Hr].
  split.
  eapply is_no_uninited_reads_sound; eauto.
  eapply mem_iff in Hr.
  eapply inits_elim; eauto.
Qed.
