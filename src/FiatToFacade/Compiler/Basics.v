Require Import FiatToFacade.Compiler.Prerequisites.

Unset Implicit Arguments.

Lemma start_compiling' :
  forall {av env} init_state vret v,
    AllADTs init_state (StringMap.empty _) ->
    refine (ret v)
           (prog <- (@Prog av env True
                           ∅ ([vret >sca> v]::∅)
                           ∅ ∅);
            final_state <- {final_state | Safe env prog init_state /\
                                          RunsTo env prog init_state final_state};
            {x | final_state[vret >> SCA av x]})%comp.
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv.

  pose proof I.
  pose proof (SomeSCAs_empty init_state).
  specialize_states.
  scas_adts_mapsto.
  auto_mapsto_unique;
    autoinj.
Qed.

Lemma start_compiling_sca_with_precondition : (* TODO: Supersedes start_compiling *)
  forall {av env} init_state scas adts vret v,
    SomeSCAs init_state scas ->
    AllADTs init_state adts ->
    refine (ret v)
           (prog <- (@Prog av env True
                           scas ([vret >sca> v]::∅)
                           adts ∅);
            final_state <- {final_state | Safe env prog init_state /\
                                          RunsTo env prog init_state final_state};
            {x | final_state[vret >> SCA av x]})%comp.
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv.
  pose proof I.
  specialize_states;
  scas_adts_mapsto;
  auto_mapsto_unique;
  autoinj.
Qed.

Lemma start_compiling_adt_with_precondition : (* TODO: Supersedes start_compiling *)
  forall {av env} init_state scas adts vret ret_type (v: ret_type) wrapper,
    (forall x y, wrapper x = wrapper y -> x = y) ->
    SomeSCAs init_state scas ->
    AllADTs init_state adts ->
    refine (ret v)
           (prog <- (@Prog av env True
                           scas (∅)
                           adts ([vret >adt> wrapper v]::∅));
            final_state <- {final_state | Safe env prog init_state /\
                                          RunsTo env prog init_state final_state};
            {x | final_state[vret >> ADT (wrapper x)]})%comp.
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv.
  pose proof I.
  specialize_states;
  scas_adts_mapsto;
  auto_mapsto_unique;
  autoinj;
  erewrite H; eauto.

Qed.
