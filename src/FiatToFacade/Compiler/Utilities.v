Require Import Fiat.FiatToFacade.SupersetUtilities.
Require Import Fiat.FiatToFacade.StringMapNotations.
Require Import Fiat.FiatToFacade.StringMapUtilities.
Require Import Fiat.FiatToFacade.Superset.
Require Import Fiat.FiatToFacade.FacadeNotations.
Require Import Fiat.FiatToFacade.FacadeUtilities.
Require Import Fiat.FiatToFacade.Prog.
Require Import Bedrock.Platform.Facade.DFacade Bedrock.Platform.Cito.SyntaxExpr Bedrock.Platform.Cito.StringMap Bedrock.Platform.Cito.GLabelMap.
Require Import Fiat.ADT.Core.

Ltac safe_seq :=
  constructor;
  split; [ specialize_states; assumption | ].

Require Import Bedrock.Platform.Facade.DFacade.
Lemma safe_call_1 :
  forall {av} env state adts f spec varg arg vout,
    state[varg >> arg] ->
    GLabelMap.find f env = Some (Axiomatic spec) ->
    AllADTs state adts ->
    ~ StringMap.In (elt:=Value av) vout adts ->
    PreCond spec (arg :: nil) ->
    @Safe av env (Call vout f (varg :: nil)) state.
Proof.
  intros.
  econstructor.

  eassumption.
  eauto using mapM_MapsTo_1.
  eapply not_in_adts_not_mapsto_adt; eassumption.
  assumption.
Qed.

Lemma assign_safe :
  forall {av} state scas adts k w,
    @SomeSCAs av state scas ->
    @AllADTs av state adts ->
    scas[k >> SCA _ w] ->
    forall k' env,
      ~ StringMap.In k' adts ->
      Safe env (Assign k' k) state.
Proof.
  intros. specialize (H _ _ H1).
  econstructor; unfold_coercions.
  + eauto using mapsto_eval.
  + eauto using not_in_adts_not_mapsto_adt.
Qed.

Lemma assign_expr_safe {av} :
  forall k env expr state adts,
    (forall k, List.In k (AllVariables expr) -> exists v, state[k >> SCA av v]) ->
    ~ StringMap.In k adts ->
    AllADTs state adts ->
    Safe env (Assign k expr) state.
Proof.
  intros * h.
  destruct (@eval_expr_some_sca _ expr state h).
  econstructor; try eassumption.
  eapply not_in_adts_not_mapsto_adt; eauto.
Qed.

Lemma drop_retvar :
  forall av env knowledge scas adts adts' prog vret,
    ~ StringMap.In vret scas ->
    (refine (@Prog av env knowledge
                   scas ([vret >sca> 0]::scas)
                   adts adts')
            prog) ->
    (refine (@Prog av env knowledge
                   scas scas
                   adts adts')
            prog).
Proof.
  unfold refine, Prog, ProgOk; intros * ? h ** .
  specialize (h v H0); inversion_by computes_to_inv.
  constructor; intros.

  destruct_pairs.
  repeat (split; specialize_states; intros; eauto).

  erewrite not_in_remove_eq;
  try eapply SomeSCAs_remove; eassumption.
Qed.
