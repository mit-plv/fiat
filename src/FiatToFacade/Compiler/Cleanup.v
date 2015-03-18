Require Import FiatToFacade.Compiler.Prerequisites.

Unset Implicit Arguments.

Lemma drop_sca :
  forall {av env} k v
         init_knowledge
         init_scas final_scas
         init_adts final_adts,
    ~ StringMap.In k init_scas ->
    refine (@Prog av env init_knowledge
                  ([k >sca> v]::init_scas) final_scas
                  init_adts final_adts)
           (@Prog av env init_knowledge
                  init_scas final_scas
                  init_adts final_adts).
Proof.
  unfold Prog, ProgOk, refine; intros.
  inversion_by computes_to_inv.
  constructor; intros.
  destruct_pairs;
    match goal with
      | [ H: SomeSCAs _ _ |- _ ] =>
        apply SomeSCAs_remove in H;
          rewrite <- not_in_remove_eq in H by assumption
    end; specialize_states; split.

  (* Safe *)
  assumption.

  (* RunsTo *)
  intros; specialize_states; split; assumption.
Qed.

Lemma compile_add_intermediate_step_with_ret :
  forall (av : Type) (env : Env av) (knowledge : Prop)
         (k : StringMap.key) (v : Memory.W)
         (init_scas inter_scas final_scas init_adts inter_adts final_adts : StringMap.t (Value av)),
    refine
      (@Prog av env knowledge init_scas ([k >> SCA av v]::final_scas) init_adts
             final_adts)
      (p <- (@Prog av env knowledge
                   init_scas ([k >> SCA av v]::inter_scas)
                   init_adts inter_adts);
       q <- (@Prog av env knowledge
                   ([k >> SCA av v]::inter_scas) ([k >> SCA av v]::final_scas)
                   inter_adts final_adts);
       ret (p;
            q)%facade)%comp.
Proof.
  unfold refine, Prog, ProgOk; intros;
  inversion_by computes_to_inv; subst;
  constructor; intros; destruct_pairs.

  split; intros; specialize_states; repeat inversion_facade; specialize_states; intuition.
  repeat (safe_seq; intros; specialize_states; intuition).
Qed.

Lemma compile_add_intermediate_adts_with_ret :
  forall av env knowledge k v init_scas final_scas init_adts inter_adts final_adts,
    refine (@Prog av env knowledge
                  init_scas final_scas
                  init_adts ([k >adt> v]::final_adts))
           (p <- (@Prog av env knowledge
                        init_scas final_scas
                        init_adts ([k >adt> v]::inter_adts));
            q <- (@Prog av env knowledge
                        final_scas final_scas
                        ([k >adt> v]::inter_adts) ([k >adt> v]::final_adts));
            ret (Seq p q))%comp.
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv; subst.
  constructor; intros; destruct_pairs.

  split; intros.

  (* Safe *)
  constructor; split; intros; specialize_states; assumption.

  (* RunsTo *)
  inversion_facade; specialize_states; intuition.
Qed.


Lemma compile_add_intermediate_scas_with_ret :
  forall av env knowledge k v init_scas inter_scas final_scas init_adts final_adts,
    refine (@Prog av env knowledge
                  init_scas ([k >sca> v]::final_scas)
                  init_adts final_adts)
           (p <- (@Prog av env knowledge
                        init_scas ([k >sca> v]::inter_scas)
                        init_adts final_adts);
            q <- (@Prog av env knowledge
                        ([k >sca> v]::inter_scas) ([k >sca> v]::final_scas)
                        final_adts final_adts);
            ret (Seq p q))%comp.
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv; subst.
  constructor; intros; destruct_pairs.

  split; intros.

  (* Safe *)
  constructor; split; intros; specialize_states; try assumption.

  (* RunsTo *)
  inversion_facade; specialize_states; intuition.
Qed.

Lemma compile_add_intermediate_scas :
  forall av env knowledge init_scas inter_scas final_scas init_adts final_adts,
    refine (@Prog av env knowledge
                  init_scas final_scas
                  init_adts final_adts)
           (p <- (@Prog av env knowledge
                        init_scas inter_scas
                        init_adts final_adts);
            q <- (@Prog av env knowledge
                        inter_scas final_scas
                        final_adts final_adts);
            ret (Seq p q))%comp.
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv; subst.
  constructor; intros; destruct_pairs.

  split; intros.

  (* Safe *)
  constructor; split; intros; specialize_states; try assumption.

  (* RunsTo *)
  inversion_facade; specialize_states; intuition.
Qed.


Lemma drop_scas_from_precond : (* TODO: Convert this to a morphism *)
  forall {av env} knowledge scas scas' scas'' adts adts',
    SomeSCAs scas scas'' ->
    refine (@Prog av env knowledge
                  scas scas'
                  adts adts')
           (@Prog av env knowledge
                  scas'' scas'
                  adts adts').
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv; subst.
  constructor; intros; destruct_pairs.

  assert (SomeSCAs initial_state scas'') by
      (eapply some_scas_Transitive; eauto).

  split; intros; specialize_states; intuition.
Qed.

Lemma drop_second_sca_from_precond :
  forall {av env} knowledge scas scas' adts adts' k v k' v',
    refine (@Prog av env knowledge
                  ([k >sca> v]::[k' >sca> v']::scas) scas'
                  adts adts')
           (@Prog av env knowledge
                  ([k >sca> v]::(StringMap.remove k' scas)) scas'
                  adts adts').
Proof.
  intros;
  apply drop_scas_from_precond, SomeSCAs_chomp, SomeSCAs_remove, SomeSCAs_chomp;
  reflexivity.
Qed.

Lemma compile_add_intermediate_adts :
  forall av env knowledge init_scas final_scas init_adts inter_adts final_adts,
    refine (@Prog av env knowledge
                  init_scas final_scas
                  init_adts final_adts)
           (p <- (@Prog av env knowledge
                        init_scas final_scas
                        init_adts inter_adts);
            q <- (@Prog av env knowledge
                        final_scas final_scas
                        inter_adts final_adts);
            ret (Seq p q))%comp.
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv; subst.
  constructor; intros; destruct_pairs.

  split; intros.

  (* Safe *)
  constructor; split; intros; specialize_states; assumption.

  (* RunsTo *)
  inversion_facade; specialize_states; intuition.
Qed.

Lemma add_scas_in_postcond :
  forall {av env} knowledge scas adts adts' vret v,
    refine (@Prog av env knowledge
                  scas ([vret >sca> v]::∅)
                  adts adts')
           (@Prog av env knowledge
                  scas ([vret >sca> v]::scas)
                  adts adts').
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv.
  constructor; intros; destruct_pairs;
  split; intros; specialize_states.
  + intuition.
  + split; scas_adts_mapsto;
    eauto using SomeSCAs_mapsto_inv, SomeSCAs_empty.
Qed.

Lemma compile_scas_then_adts :
  forall av env knowledge init_scas final_scas init_adts final_adts,
    refine (@Prog av env knowledge
                  init_scas final_scas
                  init_adts final_adts)
           (p <- (@Prog av env knowledge
                        init_scas final_scas
                        init_adts init_adts);
            q <- (@Prog av env knowledge
                        final_scas final_scas
                        init_adts final_adts);
            ret (Seq p q))%comp.
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv; subst.
  constructor; intros; destruct_pairs.

  split; intros.

  (* Safe *)
  constructor; split; intros; specialize_states; try assumption.

  (* RunsTo *)
  inversion_facade; specialize_states; intuition.
Qed.
