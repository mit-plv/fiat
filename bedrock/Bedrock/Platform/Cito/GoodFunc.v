Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.Wf.
Export Wf.

Section TopSection.

  Require Import Bedrock.Platform.Cito.SyntaxFunc.
  Require Bedrock.Platform.Cito.CompileStmtSpec.
  Require Import Bedrock.Platform.Cito.GetLocalVars.
  Require Import Bedrock.Platform.Cito.Depth.
  Require Import Bedrock.Platform.Cito.WellFormed.
  Require Import Bedrock.Platform.Cito.ListFacts3.

  Definition GoodFunc f :=
    let body := Body f in
    let local_vars := get_local_vars body (ArgVars f) (RetVar f) in
    is_no_dup (ArgVars f) = true /\
    NoUninitialized (ArgVars f) (RetVar f) body /\
    wellformed body /\
    goodSize (length local_vars + depth body).

  Hint Constructors NoDup.

  Require Import Bedrock.Platform.Cito.GeneralTactics.
  Require Import Bedrock.Platform.Cito.GetLocalVarsFacts.

  Lemma GoodFunc_syn_req :
    forall f,
      GoodFunc f ->
      let body := Body f in
      let local_vars := get_local_vars body (ArgVars f) (RetVar f) in
      let all_vars := ArgVars f ++ local_vars in
      CompileStmtSpec.syn_req all_vars (depth body) body.
    simpl; intros.
    unfold CompileStmtSpec.syn_req.
    destruct H; openhyp.
    split; eauto.
    unfold CompileStmtSpec.in_scope.
    split; eauto.
    eapply get_local_vars_subset; eauto.
  Qed.

  Lemma NoDup_app : forall A (ls2 ls1 : list A),
    NoDup ls1
    -> NoDup ls2
    -> (forall x, In x ls1 -> ~In x ls2)
    -> NoDup (ls1 ++ ls2).
    induction 1; simpl; intuition.
    constructor; auto.
    intro.
    apply in_app_or in H4; intuition eauto.
    eauto.
  Qed.

  Lemma In_InA : forall A (x : A) ls,
    List.In x ls
    -> SetoidList.InA (@Logic.eq A) x ls.
    induction ls; simpl; intuition.
  Qed.

  Lemma NoDupA_NoDup : forall A ls,
    SetoidList.NoDupA (@Logic.eq A) ls
    -> List.NoDup ls.
    induction 1; intuition auto using In_InA.
  Qed.

  Require Import Bedrock.Platform.Cito.GetLocalVars.
  Require Import Bedrock.Platform.Cito.GeneralTactics2.
  Require Import Bedrock.Platform.Cito.SetoidListFacts.
  Require Import Bedrock.Platform.Cito.GeneralTactics.
  Require Import Bedrock.Platform.Cito.StringSetFacts.
  Lemma GoodFunc_NoDup_vars : forall f, GoodFunc f -> forall s r, NoDup (ArgVars f ++ get_local_vars s (ArgVars f) r).
    unfold GoodFunc; intuition.
    apply NoDup_app; auto.
    {
      eapply is_no_dup_sound; eauto.
    }
    {
      apply NoDupA_NoDup.
      apply StringSet.StringSet.elements_3w.
    }
    intros.
    nintro.
    unfold get_local_vars in H4.
    eapply InA_eq_In_iff in H4.
    eapply StringSet.StringSet.elements_2 in H4.
    eapply StringSet.StringFacts.diff_iff in H4.
    openhyp.
    contradict H5.
    eapply of_list_spec; eauto.
  Qed.

End TopSection.

Require Import Bedrock.Platform.Cito.ADT.

Module Make (Import E : ADT).

  Module Import WfMake := Wf.Make E.
  Require Import Bedrock.Platform.Cito.Semantics.
  Import SemanticsMake.

  Require Import Bedrock.Platform.Cito.GeneralTactics.

  Section TopSection.

    Lemma GoodFunc_Safe : forall f, GoodFunc f -> let s := Body f in forall fs vs h, Safe fs s (vs, h) -> forall vs', agree_in vs vs' (ArgVars f) -> Safe fs s (vs', h).
      intros.
      eapply NoUninitialized_Safe; eauto.
      destruct H; openhyp; eauto.
    Qed.

    Lemma GoodFunc_RunsTo : forall f, GoodFunc f -> let s := Body f in forall fs vs h v', RunsTo fs s (vs, h) v' -> forall vs', agree_in vs vs' (ArgVars f) -> exists vs'', RunsTo fs s (vs', h) (vs'', snd v') /\ sel vs'' (RetVar f) = sel (fst v') (RetVar f).
      intros.
      eapply NoUninitialized_RunsTo in H0; eauto.
      destruct H; intuition.
    Qed.

  End TopSection.

End Make.
