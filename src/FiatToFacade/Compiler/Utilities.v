Require Import FiatToFacade.SupersetUtilities.
Require Import FiatToFacade.StringMapNotations.
Require Import FiatToFacade.StringMapUtilities.
Require Import FiatToFacade.Superset.
Require Import FiatToFacade.FacadeNotations.
Require Import FiatToFacade.FacadeUtilities.
Require Import Facade.DFacade SyntaxExpr StringMap GLabelMap.

Ltac safe_seq :=
  constructor;
  split; [ specialize_states; assumption | ].

Require Import Facade.DFacade.
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
  destruct (eval_expr_some_sca expr state h).
  econstructor; try eassumption.
  eapply not_in_adts_not_mapsto_adt; eauto.
Qed.
