Require Import FiatToFacade.Compiler.Prerequisites.
Require Import Facade.examples.FiatADTs.
Require Import GLabelMap List.

Unset Implicit Arguments.

Require Import Ensembles.
Require Import AdditionalEnsembleDefinitions.

Require Import ADT.
Require Import ADTRefinement.
Require Import ADTSynthesis.ADTNotation.
Require Import ADTSynthesis.FiniteSetADTs.FiniteSetADT.

Open Scope string_scope.

Section runsto_FiniteSet.

(* Inversion lemmas *)
Require Import Facade.DFacade.

Ltac runsto_prelude :=
  intros;
  inversion_facade; simpl in *; autoinj; [ | congruence];
  eq_transitive; autoinj;
  unfold sel in *; simpl in *;
  autodestruct; subst;
  try subst_find; simpl in *; autoinj; (* TODO Make autoinj call simpl in * first *)
  repeat (match goal with
            | H: 0 = length ?a |- _ => destruct a; [|discriminate]
            | H: S _ = length ?a |- _ => destruct a; [congruence|]
          end; simpl in *; autoinj; simpl in *).

  (* Specification of state after running sEmpty. *)
  Lemma runsto_sEmpty
  : forall f
           env
           x_label
           (st st' : State _),
      GLabelMap.find (elt:=FuncSpec _) f env = Some (Axiomatic FEnsemble_sEmpty) ->
      RunsTo env (Call x_label f nil) st st' ->
      StringMap.Equal st' (StringMap.add x_label (AxSpec.ADT (FEnsemble (Empty_set _))) st).
  Proof.
    runsto_prelude.
  Qed.
  
  (* Specification of state after running sAdd. *)
  Lemma runsto_sAdd
  : forall (s_model : Ensemble W)
           (w_label : StringMap.key)
           (w_value : W)
           (s_label : StringMap.key)
           (x_label : StringMap.key)
           env
           (st st' : State ADTValue) f,
      s_label <> x_label ->
      st [s_label >> AxSpec.ADT (FEnsemble s_model)] ->
      st [w_label >> SCA _ w_value] ->
      GLabelMap.find (elt:=FuncSpec _) f env = Some (Axiomatic FEnsemble_sAdd) ->
      RunsTo env (Call x_label f (s_label :: w_label :: nil)) st st' ->
      StringMap.Equal st'
                      (StringMap.add x_label SCAZero
                                     (StringMap.add s_label (AxSpec.ADT (FEnsemble (Add _ s_model w_value))) st)).
  Proof.
    runsto_prelude.
    subst_find; simpl in *; autoinj.
  Qed.

  (* Specification of state after running sRemove. *)
  Lemma runsto_sRemove
  : forall (s_model : Ensemble W)
           (w_label : StringMap.key)
           (w_value : W)
           (s_label : StringMap.key)
           (x_label : StringMap.key)
           env (st st' : State ADTValue) f,
      s_label <> x_label ->
      st [s_label >> AxSpec.ADT (FEnsemble s_model)] ->
      st [w_label >> SCA _ w_value] ->
      GLabelMap.find (elt:=FuncSpec _) f env = Some (Axiomatic FEnsemble_sRemove) ->
      RunsTo env (Call x_label f (s_label :: w_label :: nil)) st st' ->
      StringMap.Equal st'
                      (StringMap.add x_label SCAZero
                                     (StringMap.add s_label (AxSpec.ADT (FEnsemble (Subtract _ s_model w_value))) st)).
  Proof.
    runsto_prelude.
    subst_find; simpl in *; autoinj.
  Qed.

  (* Specification of state after running sDelete. *)
  Lemma runsto_sDelete
  : forall (s_label x_label : StringMap.key)
           env (st st' : State ADTValue) f,
      GLabelMap.find (elt:=FuncSpec _) f env = Some (Axiomatic FEnsemble_sDelete) ->
      RunsTo env (Call x_label f (s_label :: nil)) st st' ->
      StringMap.Equal st'
                      (StringMap.add x_label SCAZero
                                     (StringMap.remove s_label st)).
  Proof.
    runsto_prelude.
  Qed.

  (* Specification of state after running sIn. *)
  Lemma runsto_sIn
  : forall (s_model : Ensemble W)
           (w_label : StringMap.key)
           (w_value : W)
           (s_label : StringMap.key)
           (x_label : StringMap.key)
           (env : Env ADTValue)
           (st st' : State ADTValue) f,
      s_label <> x_label ->
      st [s_label >> AxSpec.ADT (FEnsemble s_model)] ->
      st [w_label >> SCA _ w_value] ->
      GLabelMap.find (elt:=FuncSpec _) f env = Some (Axiomatic FEnsemble_sIn) ->
      RunsTo env (Call x_label f (s_label :: w_label :: nil)) st st' ->
      exists ret,
        (ret = SCAOne <-> Ensembles.In _ s_model w_value)
        /\ (ret = SCAZero <-> ~ Ensembles.In _ s_model w_value)
        /\ StringMap.Equal st'
                           (StringMap.add x_label ret
                                          (StringMap.add s_label (AxSpec.ADT (FEnsemble s_model)) st)).
  Proof.
    runsto_prelude.
    subst_find; simpl in *; autoinj.
    unfold Programming.propToWord, IF_then_else in *; intuition;
    [eexists SCAOne
    | eexists SCAZero];
    eexists; repeat split; intros; subst; eauto 2; intuition; discriminate.
  Qed.

  Arguments Word.natToWord : simpl never. (* simplifying natToWord causes crazy slowdown. *)

  (* Specification of state after running sSize. *)
  Lemma runsto_sSize
  : forall (s_model : Ensemble W)
           (s_label : StringMap.key)
           (x_label : StringMap.key)
           (env : Env ADTValue)
           (st st' : State ADTValue) f,
      s_label <> x_label ->
      st [s_label >> AxSpec.ADT (FEnsemble s_model)] ->
      GLabelMap.find (elt:=FuncSpec _) f env = Some (Axiomatic FEnsemble_sSize) ->
      RunsTo env (Call x_label f (s_label :: nil)) st st' ->
      exists ret n,
        FiatADTs.cardinal _ s_model n
        /\ ret = SCA _ (Word.natToWord 32 n)
        /\ StringMap.Equal st'
                           (StringMap.add x_label ret
                                          (StringMap.add s_label (AxSpec.ADT (FEnsemble s_model)) st)).
  Proof.
    runsto_prelude.
    eauto.
  Qed.

End runsto_FiniteSet.

Section compile_FiniteSet_Methods.

  Variable FiniteSetImpl : FullySharpened FiniteSetSpec.

  (* [AbsImpl] maps the state of the sharpend ADT to the Spec. *)
  Definition AbsImpl r :=
    fun x => exists s, AbsR (projT2 FiniteSetImpl) s r /\ In _ s x.

  Lemma AbsImpl_SameSet :
    forall s s' r,
      AbsR (projT2 FiniteSetImpl) s r
      -> AbsR (projT2 FiniteSetImpl) s' r
      -> Same_set _ s s'.
  Proof.
    intros; split;
    unfold Included, In; intros;
    pose proof (ADTRefinementPreservesMethods
                  (projT2 FiniteSetImpl)
                  {| bindex := sIn |} _ _ x H (ReturnComputes _)) as ref;
      unfold refineMethod in ref;
      pose proof (ADTRefinementPreservesMethods
                    (projT2 FiniteSetImpl)
                    {| bindex := sIn |} _ _ x H0 (ReturnComputes _)) as ref';
      unfold refineMethod in ref';
      inversion_by computes_to_inv; injections; subst.
    - rewrite <- H5 in *; injections; rewrite <- H3, H7; eauto.
    - rewrite <- H5 in *; injections; rewrite <- H7, H3; eauto.
  Qed.

  (* First we show how to break down the components of an
     [Add] method call. *)

  Lemma compile_AbsImpl_Add
  : forall {env},
    forall vensemble velt,
    forall init_scas inter_scas final_scas init_adts inter_adts final_adts knowledge rep new_w,
      velt <> vensemble ->
      refine (@Prog _ env knowledge
                    init_scas final_scas
                    init_adts ([vensemble >adt>
                                FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sAdd rep new_w))) ] :: final_adts))
             (pnew_w <- (@Prog _ env knowledge
                               init_scas ([velt >sca> new_w]::init_scas)
                               init_adts init_adts);
              p_rep <- (@Prog _ env knowledge
                              ([velt >sca> new_w]::init_scas) ([velt >sca> new_w]::init_scas)
                              init_adts ([vensemble >adt> FEnsemble (AbsImpl rep) ]::inter_adts));
              pAdd <- (@Prog _ env knowledge
                             ([velt >sca> new_w]::init_scas) inter_scas
                             ([vensemble >adt> FEnsemble (AbsImpl rep) ]::inter_adts)
                             ([vensemble >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sAdd rep new_w)))]::final_adts));
              pclean <- (@Prog _ env knowledge
                               inter_scas final_scas
                               ([vensemble >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sAdd rep new_w)))]::final_adts)
                               ([vensemble >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sAdd rep new_w)))]::final_adts));
              ret (pnew_w; p_rep; pAdd; pclean)%facade)%comp.
  Proof.
    unfold refine, Prog, ProgOk; unfold_coercions; intros;
    inversion_by computes_to_inv; constructor;
    split; subst; destruct_pairs.

    (* Safe *)
    repeat (constructor; split; intros);
      try (solve [specialize_states;
                   try assumption]).

    (* RunsTo *)
    intros;
      repeat inversion_facade;
      specialize_states;
      intuition.
  Qed.

  (* Next we show that we can push AbsImpl through the spec of [Add].  *)
  Lemma AbsImpl_Add :
    forall s r w'
           (s_r_eqv : AbsR (projT2 FiniteSetImpl) s r),
      Add W (AbsImpl r) w'
      = AbsImpl (fst ((CallMethod (projT1 FiniteSetImpl) sAdd) r w')).
  Proof.
    intros; apply Extensionality_Ensembles; unfold AbsImpl, Same_set, Included, In, Add; intuition.
    - pose proof (ADTRefinementPreservesMethods
                    (projT2 FiniteSetImpl)
                    {| bindex := sAdd |} _ _ w' s_r_eqv (ReturnComputes _)) as ref;
      unfold refineMethod in ref; inversion_by computes_to_inv; injections; subst; simpl in *.
      rewrite <- H3; simpl; eexists; split; eauto.
      destruct H.
      constructor;  unfold In in *; destruct_ex; intuition; eapply AbsImpl_SameSet; eauto.
      constructor 2; eauto.
    - destruct_ex.
      intuition.
      pose proof (ADTRefinementPreservesMethods
                    (projT2 FiniteSetImpl)
                    {| bindex := sAdd |} _ _ w' s_r_eqv (ReturnComputes _)) as ref;
        unfold refineMethod in ref;
      inversion_by computes_to_inv; injections; subst; simpl in *.
      rewrite <- H4 in H0; simpl in *.
      eapply (AbsImpl_SameSet _ _ _ H0 H3) in H1; destruct H1.
      constructor; exists s; eauto.
      constructor 2; eauto.
  Qed.

  (* Finally we show how to compile the method call, once we have method bodies for its two arguments. *)

  Ltac compile_helper runs_to :=
  unfold refine, Prog, ProgOk; intros;
  inversion_by computes_to_inv;
  subst; constructor; split; intros;
  destruct_pairs; scas_adts_mapsto;
  [ econstructor; eauto 2 using mapsto_eval;
    [ scas_adts_mapsto;
      eauto using mapM_MapsTo_0, mapM_MapsTo_1, mapM_MapsTo_2
    | eapply not_in_adts_not_mapsto_adt;
      [ eassumption | map_iff_solve intuition ]
    | simpl; repeat eexists; reflexivity ]
  | match goal with
      | H: context[RunsTo] |- _ => eapply runs_to in H; eauto
    end; split; repeat rewrite_Eq_in_goal
  ].

  Lemma compile_sAdd
  : forall {env},
    forall vens velt vpointer vdiscard r s f,
    forall scas adts knowledge w'
           (s_r_eqv : AbsR (projT2 FiniteSetImpl) s r),
      GLabelMap.find f env = Some (Axiomatic FEnsemble_sAdd) ->
      ~ StringMap.In vpointer adts ->
      ~ StringMap.In vdiscard adts ->
      ~ StringMap.In vens scas ->
      vpointer <> vens ->
      vpointer <> velt ->
      velt <> vens ->
      vens <> vdiscard ->
      adts[vens >> AxSpec.ADT (FEnsemble s)] ->
      scas[velt >> SCA _ w'] ->
      refine (@Prog _ env knowledge
                    scas
                    ([vdiscard >sca> 0]::scas)
                    ([vens >adt> FEnsemble (AbsImpl r) ] :: adts)
                    ([vens >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sAdd r w'))) ] :: adts))
             (ret (Call vdiscard f (vens :: velt :: nil))%facade).
  Proof.
    compile_helper runsto_sAdd.
    eauto using  SomeSCAs_chomp, add_sca_pop_adts.
    apply add_adts_pop_sca; map_iff_solve trivial.
    erewrite AbsImpl_Add by eauto.
    apply AllADTs_chomp_remove.
    rewrite H12; trickle_deletion; reflexivity.
  Qed.
  
  Lemma compile_sAdd_no_ret :
    forall  vdiscard
            (env : GLabelMap.t (FuncSpec ADTValue))
            (vens velt : StringMap.key)
            (r : Core.Rep (ComputationalADT.LiftcADT (projT1 FiniteSetImpl)))
            (s : Core.Rep FiniteSetSpec) (f : GLabelMap.key)
            (scas adts : StringMap.t (Value ADTValue))
            (knowledge : Prop) (w' : Memory.W),
      Core.AbsR (projT2 FiniteSetImpl) s r ->
      GLabelMap.find (elt:=FuncSpec ADTValue) f env =
      Some (Axiomatic FEnsemble_sAdd) ->
      ~ StringMap.In (elt:=Value ADTValue) vdiscard adts ->
      ~ StringMap.In (elt:=Value ADTValue) vens scas ->
      ~ StringMap.In (elt:=Value ADTValue) vdiscard scas ->
      velt <> vens ->
      vens <> vdiscard ->
      velt <> vdiscard ->
      (adts) [vens >> ADT (FEnsemble s)] ->
      (scas) [velt >> SCA ADTValue w'] ->
      refine
        (Prog (env := env) knowledge scas scas
              ([vens >> ADT (FEnsemble (AbsImpl r))]::adts)
              ([vens >>
                     ADT
                     (FEnsemble
                        (AbsImpl (fst ((CallMethod (projT1 FiniteSetImpl) sAdd) r w'))))]
                 ::adts)) (ret (Call vdiscard f (cons vens (cons velt nil)))).
  Proof.
    intros.
    apply (drop_retvar (vret := vdiscard)); eauto.
    eapply compile_sAdd; eauto.
  Qed.

    (* Rinse, Wash, Repeat *)

  Lemma AbsImpl_sEmpty u:
    Empty_set _ = AbsImpl ((CallConstructor (projT1 FiniteSetImpl) sEmpty) u).
  Proof.
    intros; apply Extensionality_Ensembles; unfold AbsImpl, Same_set, Included, In, Add; intuition.
    destruct_ex.
    - pose proof (ADTRefinementPreservesConstructors
                    (projT2 FiniteSetImpl)
                    {| bindex := sEmpty |} u (ReturnComputes _)) as ref;
      unfold refineMethod in ref; inversion_by computes_to_inv; injections; subst; simpl in *.
      eapply (AbsImpl_SameSet _ _ _ H3 H0); eauto.
  Qed.

  Lemma AbsImpl_sRemove
  : forall s r w
           (s_r_eqv : AbsR (projT2 FiniteSetImpl) s r),
      Subtract W (AbsImpl r) w = AbsImpl (fst ((CallMethod (projT1 FiniteSetImpl) sRemove) r w)).
  Proof.
    intros.
        intros; apply Extensionality_Ensembles; unfold AbsImpl, Same_set, Included, In, Subtract; intuition.
    - pose proof (ADTRefinementPreservesMethods
                    (projT2 FiniteSetImpl)
                    {| bindex := sRemove |} _ _ w s_r_eqv (ReturnComputes _)) as ref;
      unfold refineMethod in ref; inversion_by computes_to_inv; injections; subst; simpl in *.
      rewrite <- H3; simpl; eexists; split; eauto.
      destruct H.
      constructor;  unfold In in *; destruct_ex; intuition; eapply AbsImpl_SameSet; eauto.
    - destruct_ex.
      intuition.
      pose proof (ADTRefinementPreservesMethods
                    (projT2 FiniteSetImpl)
                    {| bindex := sRemove |} _ _ w s_r_eqv (ReturnComputes _)) as ref;
        unfold refineMethod in ref;
      inversion_by computes_to_inv; injections; subst; simpl in *.
      rewrite <- H4 in H0; simpl in *.
      eapply (AbsImpl_SameSet _ _ _ H0 H3) in H1; destruct H1.
      unfold Setminus; intuition; exists s; eauto.
  Qed.

  Lemma compile_AbsImpl_sDelete
  : forall {env},
    forall vensemble vdiscard f,
    forall scas adts knowledge u,
      vensemble <> vdiscard ->
      GLabelMap.find f env = Some (Axiomatic FEnsemble_sDelete) ->
      ~ StringMap.In vensemble adts ->
      ~ StringMap.In vdiscard adts ->
      ~ StringMap.In vdiscard scas ->
      ~ StringMap.In vensemble scas ->
      refine (@Prog _ env knowledge scas scas
                    ([vensemble >adt> FEnsemble (AbsImpl u)]::adts) adts)
             (ret (Call vdiscard f (vensemble :: nil))).
  Proof.
    compile_helper runsto_sDelete.
    eauto using SomeSCAs_chomp_left, SomeSCAs_not_In_remove.
    eapply add_adts_pop_sca; try eassumption.
    rewrite H8; trickle_deletion. rewrite <- not_in_remove_eq; first [ eassumption | reflexivity ].
  Qed.

  Lemma compile_AbsImpl_sEmpty
  : forall {env},
    forall vensemble f,
    forall scas adts knowledge u,
      GLabelMap.find f env = Some (Axiomatic FEnsemble_sEmpty) ->
      ~ StringMap.In vensemble adts ->
      ~ StringMap.In vensemble scas ->
      refine (@Prog _ env knowledge scas scas
                    adts ([vensemble >adt>
                           FEnsemble (AbsImpl (CallConstructor (projT1 FiniteSetImpl) sEmpty u)) ] :: adts))
             (ret (Call vensemble f nil)).
  Proof.
    compile_helper runsto_sEmpty.
    eauto using add_sca_pop_adts.
    setoid_rewrite AbsImpl_sEmpty;  apply AllADTs_chomp_remove.
    rewrite H5; trickle_deletion; reflexivity.
  Qed.

  Lemma compile_AbsImpl_Remove
  : forall {env},
    forall vensemble velt,
    forall init_scas inter_scas final_scas init_adts inter_adts final_adts knowledge rep new_w,
      velt <> vensemble ->
      refine (@Prog _ env knowledge
                    init_scas final_scas
                    init_adts ([vensemble >adt>
                                FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sRemove rep new_w))) ] :: final_adts))
             (pnew_w <- (@Prog _ env knowledge
                               init_scas ([velt >sca> new_w]::init_scas)
                               init_adts init_adts);
              p_rep <- (@Prog _ env knowledge
                              ([velt >sca> new_w]::init_scas) ([velt >sca> new_w]::init_scas)
                              init_adts ([vensemble >adt> FEnsemble (AbsImpl rep) ]::inter_adts));
              pRemove <- (@Prog _ env knowledge
                             ([velt >sca> new_w]::init_scas) inter_scas
                             ([vensemble >adt> FEnsemble (AbsImpl rep) ]::inter_adts)
                             ([vensemble >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sRemove rep new_w)))]::final_adts));
              pclean <- (@Prog _ env knowledge
                               inter_scas final_scas
                               ([vensemble >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sRemove rep new_w)))]::final_adts)
                               ([vensemble >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sRemove rep new_w)))]::final_adts));
              ret (pnew_w; p_rep; pRemove; pclean)%facade)%comp.
  Proof.
    unfold refine, Prog, ProgOk; unfold_coercions; intros;
    inversion_by computes_to_inv; constructor;
    split; subst; destruct_pairs.

    (* Safe *)
    repeat (constructor; split; intros);
      try (solve [specialize_states;
                   try assumption]).

    (* RunsTo *)
    intros;
      repeat inversion_facade;
      specialize_states;
      intuition.
  Qed.

  Lemma compile_sRemove
  : forall {env},
    forall vens velt vpointer vdiscard r s f,
    forall scas adts knowledge w'
           (s_r_eqv : AbsR (projT2 FiniteSetImpl) s r),
      GLabelMap.find f env = Some (Axiomatic FEnsemble_sRemove) ->
      ~ StringMap.In vpointer adts ->
      ~ StringMap.In vdiscard adts ->
      ~ StringMap.In vens scas ->
      vpointer <> vens ->
      vpointer <> velt ->
      velt <> vens ->
      vens <> vdiscard ->
      adts[vens >> AxSpec.ADT (FEnsemble s)] ->
      scas[velt >> SCA _ w'] ->
      refine (@Prog _ env knowledge
                    scas
                    ([vdiscard >sca> 0]::scas)
                    ([vens >adt> FEnsemble (AbsImpl r) ] :: adts)
                    ([vens >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sRemove r w'))) ] :: adts))
             (ret (Call vdiscard f (vens :: velt :: nil))%facade).
  Proof.
    compile_helper runsto_sRemove.
    eauto using  SomeSCAs_chomp, add_sca_pop_adts.
    apply add_adts_pop_sca; map_iff_solve trivial.
    erewrite AbsImpl_sRemove by eauto.
    apply AllADTs_chomp_remove.
    rewrite H12; trickle_deletion; reflexivity.
  Qed.

  Lemma compile_AbsImpl_In
  : forall {env},
    forall vensemble velt vin,
    forall init_scas inter_scas final_scas init_adts inter_adts final_adts knowledge rep new_w,
      velt <> vensemble ->
      refine (@Prog _ env knowledge
                    init_scas final_scas
                    init_adts ([vensemble >adt>
                                FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sIn rep new_w))) ] :: final_adts))
             (pnew_w <- (@Prog _ env knowledge
                               init_scas ([velt >sca> new_w]::init_scas)
                               init_adts init_adts);
              p_rep <- (@Prog _ env knowledge
                              ([velt >sca> new_w]::init_scas) ([velt >sca> new_w]::init_scas)
                              init_adts ([vensemble >adt> FEnsemble (AbsImpl rep) ]::inter_adts));
              pRemove <- (@Prog _ env knowledge
                                ([velt >sca> new_w]::init_scas)
                                ([vin >sca> (BoolToW (snd (CallMethod (projT1 FiniteSetImpl) sIn rep new_w)))]::inter_scas)
                                ([vensemble >adt> FEnsemble (AbsImpl rep) ]::inter_adts)
                                ([vensemble >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sIn rep new_w)))]::final_adts));
              pclean <- (@Prog _ env knowledge
                               ([vin >sca> (BoolToW (snd (CallMethod (projT1 FiniteSetImpl) sIn rep new_w)))]::inter_scas)
                               final_scas
                               ([vensemble >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sIn rep new_w)))]::final_adts)
                               ([vensemble >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sIn rep new_w)))]::final_adts));
              ret (pnew_w; p_rep; pRemove; pclean)%facade)%comp.
  Proof.
    unfold refine, Prog, ProgOk; unfold_coercions; intros;
    inversion_by computes_to_inv; constructor;
    split; subst; destruct_pairs.

    (* Safe *)
    repeat (constructor; split; intros);
      try (solve [specialize_states;
                   try assumption]).

    (* RunsTo *)
    intros;
      repeat inversion_facade;
      specialize_states;
      intuition.
  Qed.

  Lemma AbsImpl_sIn
  : forall s r w
           (s_r_eqv : AbsR (projT2 FiniteSetImpl) s r),
      AbsImpl r = AbsImpl (fst ((CallMethod (projT1 FiniteSetImpl) sIn) r w)) /\
      (BoolToW (snd ((CallMethod (projT1 FiniteSetImpl) sIn) r w)) = Word.natToWord 32 1 <-> (w ∈ AbsImpl r)%ensemble) /\
      (BoolToW (snd ((CallMethod (projT1 FiniteSetImpl) sIn) r w)) = Word.natToWord 32 0 <-> ~ (w ∈ AbsImpl r)%ensemble).
  Proof.
    intros; intuition.
    - pose proof (ADTRefinementPreservesMethods
                    (projT2 FiniteSetImpl)
                    {| bindex := sIn |} _ _ w s_r_eqv (ReturnComputes _)) as ref;
      unfold refineMethod in ref; inversion_by computes_to_inv; injections; subst; simpl in *.
    apply Extensionality_Ensembles; unfold AbsImpl, Same_set, Included, In; intuition.
    destruct_ex; intuition; eexists; split; eauto.
    rewrite <- H2; simpl; eauto.
    assert (x2 = s) by
        (apply Extensionality_Ensembles; eapply AbsImpl_SameSet; eauto).
    subst; eauto.
    destruct_ex; intuition; eexists; split; eauto.
    eapply f_equal with (f := fst) in H2; simpl in *; subst.
    assert (x2 = s) by
        (apply Extensionality_Ensembles; eapply AbsImpl_SameSet; eauto).
    subst; eauto.
    - pose proof (ADTRefinementPreservesMethods
                    (projT2 FiniteSetImpl)
                    {| bindex := sIn |} _ _ w s_r_eqv (ReturnComputes _)) as ref;
      unfold refineMethod in ref; inversion_by computes_to_inv; injections; subst; simpl in *.
      rewrite <- H3 in H; destruct x1; simpl in *; try discriminate.
      assert (s = AbsImpl r); subst; eauto; intuition.
      apply Extensionality_Ensembles; unfold AbsImpl, Same_set, Included, In; intuition.
      eexists; eauto.
      destruct_ex; intuition; eauto.
      assert (x1 = s) by
          (apply Extensionality_Ensembles; eapply AbsImpl_SameSet; eauto); subst; eauto.
    - pose proof (ADTRefinementPreservesMethods
                    (projT2 FiniteSetImpl)
                    {| bindex := sIn |} _ _ w s_r_eqv (ReturnComputes _)) as ref;
      unfold refineMethod in ref; inversion_by computes_to_inv; injections; subst; simpl in *.
      rewrite <- H3; simpl; rewrite (proj2 H1); eauto.
      assert (s = AbsImpl r); subst; eauto; intuition.
      apply Extensionality_Ensembles; unfold AbsImpl, Same_set, Included, In; intuition.
      eexists; eauto.
      destruct_ex; intuition; eauto.
      assert (x2 = s) by
          (apply Extensionality_Ensembles; eapply AbsImpl_SameSet; eauto); subst; eauto.
    - pose proof (ADTRefinementPreservesMethods
                    (projT2 FiniteSetImpl)
                    {| bindex := sIn |} _ _ w s_r_eqv (ReturnComputes _)) as ref;
      unfold refineMethod in ref; inversion_by computes_to_inv; injections; subst; simpl in *.
      rewrite <- H4 in H; simpl in *.
      assert (s = AbsImpl r); subst; eauto; intuition.
      apply Extensionality_Ensembles; unfold AbsImpl, Same_set, Included, In; intuition.
      eexists; eauto.
      destruct_ex; intuition; eauto.
      assert (x2 = s) by
          (apply Extensionality_Ensembles; eapply AbsImpl_SameSet; eauto); subst; eauto.
      subst; discriminate.
    - pose proof (ADTRefinementPreservesMethods
                    (projT2 FiniteSetImpl)
                    {| bindex := sIn |} _ _ w s_r_eqv (ReturnComputes _)) as ref;
      unfold refineMethod in ref; inversion_by computes_to_inv; injections; subst; simpl in *.
      rewrite <- H3; simpl in *.
      assert (s = AbsImpl r); subst; eauto; intuition.
      apply Extensionality_Ensembles; unfold AbsImpl, Same_set, Included, In; intuition.
      eexists; eauto.
      destruct_ex; intuition; eauto.
      assert (x2 = s) by
          (apply Extensionality_Ensembles; eapply AbsImpl_SameSet; eauto); subst; eauto.
      destruct x1; eauto.
      exfalso; eauto.
  Qed.

    Lemma compile_sIn
  : forall {env},
    forall vens velt vpointer vin r s f,
    forall scas adts knowledge w'
           (s_r_eqv : AbsR (projT2 FiniteSetImpl) s r),
      GLabelMap.find f env = Some (Axiomatic FEnsemble_sIn) ->
      ~ StringMap.In vpointer adts ->
      ~ StringMap.In vin adts ->
      ~ StringMap.In vens scas ->
      vpointer <> vens ->
      vpointer <> velt ->
      velt <> vens ->
      vens <> vin ->
      scas[velt >> SCA _ w'] ->
      refine (@Prog _ env knowledge
                    scas
                    ([vin >sca> (BoolToW (snd (CallMethod (projT1 FiniteSetImpl) sIn r w')))] ::scas)
                    ([vens >adt> FEnsemble (AbsImpl r) ] :: adts)
                    ([vens >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sIn r w'))) ] :: adts))
             (ret (Call vin f (vens :: velt :: nil))%facade).

    Proof.
    compile_helper runsto_sIn.
    destruct_ex; split_and; subst.
    rewrite H15.
    destruct (AbsImpl_sIn _ _ w' s_r_eqv) as [r_eqv [x_eq x_neq]].
      pose ((CallMethod (projT1 FiniteSetImpl) sIn) r w') as p; simpl in *;
      case_eq p; unfold p in *; intros ? ? H'; rewrite H' in *; clear p; simpl in *.
    destruct b; simpl in *.
    rewrite (proj2 H13) by intuition; eauto using SomeSCAs_chomp, add_sca_pop_adts.
    rewrite (proj2 H9) by intuition; eauto using SomeSCAs_chomp, add_sca_pop_adts.
    destruct_ex; split_and; subst.
    destruct (AbsImpl_sIn _ _ w' s_r_eqv) as [r_eqv [x_eq x_neq]];
      pose ((CallMethod (projT1 FiniteSetImpl) sIn) r w') as p; simpl in *;
      case_eq p; unfold p in *; intros ? ? H'; rewrite H' in *; clear p; simpl in *.
    rewrite H15; destruct x.
    - apply add_adts_pop_sca; map_iff_solve trivial.
      rewrite r_eqv; apply AllADTs_chomp_remove.
      rewrite H11; trickle_deletion; reflexivity.
    - destruct b.
      pose proof ((proj1 x_eq) (refl_equal _)) as H''; rewrite <- H13 in H''; discriminate.
      pose proof ((proj1 x_neq) (refl_equal _)) as H''; rewrite <- H9 in H''; discriminate.
  Qed.

  Lemma AbsImpl_sSize
  : forall s r u
           (s_r_eqv : AbsR (projT2 FiniteSetImpl) s r),
      AbsImpl r = AbsImpl (fst ((CallMethod (projT1 FiniteSetImpl) sSize) r u)) /\
      forall n,
        FiatADTs.cardinal _ s n
        -> Word.natToWord _ n = snd ((CallMethod (projT1 FiniteSetImpl) sSize) r u).
  Proof.
    intros.
    pose proof (ADTRefinementPreservesMethods
                  (projT2 FiniteSetImpl)
                  {| bindex := sSize |} _ _ u s_r_eqv (ReturnComputes _)) as ref;
      unfold refineMethod in ref; inversion_by computes_to_inv; injections; subst; simpl in *.
    split.
    - apply Extensionality_Ensembles; unfold AbsImpl, Same_set, Included, In, Add; intuition.
      destruct_ex; intuition; eexists; split; eauto.
      rewrite <- H2; simpl.
      assert (x2 = s)  by
          (apply Extensionality_Ensembles; eapply AbsImpl_SameSet; eauto); subst; eauto.
      exists s; destruct_ex; intuition.
      rewrite <- H2 in H3; simpl in *.
      assert (x2 = s)  by
          (apply Extensionality_Ensembles; eapply AbsImpl_SameSet; eauto); subst; eauto.
    - rewrite <- H2; simpl in *.
      unfold cardinal in *.
      apply computes_to_inv in H0; destruct_ex; intuition.
      apply computes_to_inv in H0; unfold FiatADTs.cardinal, AdditionalEnsembleDefinitions.cardinal in *.
      destruct_ex; split_and; subst;
      inversion_by computes_to_inv; subst.
      unfold from_nat in *.
      repeat match goal with
               | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
               | [ H : (_, _) = ?x |- _ ] => destruct x
               | _ => progress subst
             end.
      (* Problem with switching from nats to words. *)
      admit.
  Qed.

  Require Import Common.AdditionalEnsembleLemmas Permutation.

  Lemma EnsembleListEquivalence_length {A} :
    forall l s s' l',
      EnsembleListEquivalence s l ->
      EnsembleListEquivalence s' l' ->
      Same_set A s s' ->
      length l = length l'.
  Proof.
    intros; apply Permutation_length.
    eapply EnsembleListEquivalence_Permutation; eauto.
    eapply EnsembleListEquivalence_Same_set; eauto.
    symmetry; auto.
  Qed.

  Lemma Same_set_AbsImpl
  : forall s r,
      AbsR (projT2 FiniteSetImpl) s r
      -> Same_set _ s (AbsImpl r).
  Proof.
    intros; split;
    unfold Included, In; intros;
    pose proof (ADTRefinementPreservesMethods
                  (projT2 FiniteSetImpl)
                  {| bindex := sIn |} _ _ x H (ReturnComputes _)) as ref;
      unfold refineMethod in ref;
      inversion_by computes_to_inv; injections; subst; simpl in *.
    - unfold AbsImpl; eauto.
    - destruct H0; intuition; subst.
      eapply AbsImpl_SameSet with (s' := x0) (r := r); eauto.
  Qed.

  Lemma compile_sSize
  : forall {env},
    forall vens vpointer vsize r s f u,
    forall scas adts knowledge
           (s_r_eqv : AbsR (projT2 FiniteSetImpl) s r),
      GLabelMap.find f env = Some (Axiomatic FEnsemble_sSize) ->
      ~ StringMap.In vpointer adts ->
      ~ StringMap.In vsize adts ->
      ~ StringMap.In vens scas ->
      vpointer <> vens ->
      vens <> vsize ->
      adts[vens >> AxSpec.ADT (FEnsemble s)] ->
      refine (@Prog _ env knowledge
                    scas
                    ([vsize >sca> snd (CallMethod (projT1 FiniteSetImpl) sSize r u)] ::scas)
                    ([vens >adt> FEnsemble (AbsImpl r) ] :: adts)
                    ([vens >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sSize r u))) ] :: adts))
             (ret (Call vsize f (vens :: nil))%facade).
  Proof.
    compile_helper runsto_sSize.
    destruct_ex; split_and; subst.
    rewrite H12.
    destruct (AbsImpl_sSize _ _ u s_r_eqv).
    unfold cardinal in *; destruct_ex; split_and; subst; simpl in *.
    rewrite H11. rewrite SomeSCAs_chomp; eauto; try reflexivity.
    admit.
    (* Similar problems with word / nat mismatch. *)
  Admitted.
  (*
    rewrite <- H14.
    unfold nat_as_word.
    erewrite EnsembleListEquivalence_length with (l := x1) (l' := x); eauto.
    eauto using SomeSCAs_chomp, add_sca_pop_adts.
    symmetry; eapply Same_set_AbsImpl; eauto.
    destruct_ex; split_and; subst.
    rewrite H12.
    apply add_adts_pop_sca; map_iff_solve trivial.
    destruct (AbsImpl_sSize _ _ u s_r_eqv) as [r_eqv _].
    rewrite r_eqv; apply AllADTs_chomp_remove.
    rewrite H9; trickle_deletion; reflexivity.
  Qed.
*)


End compile_FiniteSet_Methods.

Lemma pull_if_FEnsemble :
  forall {T} {c: bool} {a b} (f: T -> _),
    FEnsemble (f (if c then a else b)) = FEnsemble (if c then f a else f b).
Proof.
  intros; f_equal; eauto using pull_if.
Qed.
