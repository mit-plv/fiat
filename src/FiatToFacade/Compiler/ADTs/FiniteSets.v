Require Import FiatToFacade.Compiler.Prerequisites.
Require Import Facade.FacadeADTs.
Require Import List.

Unset Implicit Arguments.

Require Import Ensembles.
Require Import AdditionalEnsembleDefinitions.

Require Import ADT.
Require Import ADTRefinement.
Require Import ADTSynthesis.ADTNotation.
Open Scope string_scope.
Definition sEmpty := "Empty".
Definition sAdd := "Add".
Definition sRemove := "Remove".
Definition sIn := "In".
Definition sSize := "Size".
Definition sToEnsemble := "ToEnsemble".

Definition FiniteSetSig : ADTSig :=
  ADTsignature {
      Constructor sEmpty : unit -> rep,
      Method sAdd : rep x W -> rep x unit,
      Method sRemove : rep x W -> rep x unit,
      Method sIn : rep x W -> rep x bool,
      Method sSize : rep x unit -> rep x nat,
      Method sToEnsemble : rep x unit -> rep x Ensemble W
    }%ADTSig.

(** And now the spec *)
Definition FiniteSetSpec : ADT FiniteSetSig :=
  ADTRep (Ensemble W) {
    Def Constructor sEmpty (_ : unit) : rep := ret (Empty_set _),

    Def Method sAdd (xs : rep , x : W) : unit :=
      ret (Add _ xs x, tt),

    Def Method sRemove (xs : rep , x : W) : unit :=
      ret (Subtract _ xs x, tt),

    Def Method sIn (xs : rep , x : W) : bool :=
        (b <- { b : bool | b = true <-> Ensembles.In _ xs x };
         ret (xs, b)),

    Def Method sSize (xs : rep , _ : unit) : nat :=
          (n <- { n : nat | cardinal _ xs n };
           ret (xs, n)),

    Def Method sToEnsemble (xs : rep , _ : unit) : Ensemble W :=
            (ret (xs, xs))
  }.

Section runsto_FiniteSet.

  (* Specification of state after running sEmpty. *)
  Lemma runsto_sEmpty
  : forall (x_label : StringMap.key)
           (env : Env FacadeADT)
           (st st' : State FacadeADT)
           (sEmpty_pointer : W),
      Word2Spec env sEmpty_pointer = Some (Axiomatic FEnsemble_sEmpty) ->
      RunsTo env (Call x_label sEmpty_pointer nil) st st' ->
      StringMap.Equal st' (StringMap.add x_label (AxSpec.ADT (FEnsemble (Empty_set _))) st).
  Proof.
    intros * sEmpty_Pointer_is_sEmpty runs_to.
    inversion_clear' runs_to; simpl in *; autoinj;
    [ | congruence].

    rewrite sEmpty_Pointer_is_sEmpty in *; autoinj.
    unfold FEnsemble_sEmpty in *; simpl in *; autodestruct; subst; eauto.
  Qed.

  (* Specification of state after running sAdd. *)
  Lemma runsto_sAdd
  : forall (s_model : Ensemble W)
           (w_label : StringMap.key)
           (w_value : W)
           (s_label : StringMap.key)
           (x_label : StringMap.key)
           (env : Env FacadeADT)
           (st st' : State FacadeADT)
           (sAdd_pointer : W),
      s_label <> x_label ->
      st [s_label >> AxSpec.ADT (FEnsemble s_model)] ->
      st [w_label >> SCA _ w_value] ->
      Word2Spec env sAdd_pointer  = Some (Axiomatic FEnsemble_sAdd) ->
      RunsTo env (Call x_label sAdd_pointer (s_label :: w_label :: nil)) st st' ->
      StringMap.Equal st'
                      (StringMap.add x_label SCAZero
                                     (StringMap.add s_label (AxSpec.ADT (FEnsemble (Add _ s_model w_value))) st)).
  Proof.
    intros * label_neq s_init w_init sAdd_Pointer_is_sAdd runs_to.
    inversion_clear' runs_to; simpl in *; autoinj;
    [ | congruence].

    rewrite sAdd_Pointer_is_sAdd in *; autoinj.
    unfold FEnsemble_sAdd in *; clear sAdd_Pointer_is_sAdd; simpl in *;
    autodestruct; subst;
    rewrite StringMapFacts.find_mapsto_iff in * |- ;
    unfold sel in *.

    subst_find; simpl in *; setoid_rewrite w_init in H5; simpl in *; (* subst_find doesn't work on w_label *)
    autoinj.

    destruct output; [congruence|].
    destruct output; [congruence|].
    simpl in *; autoinj.
  Qed.

  (* Specification of state after running sRemove. *)
  Lemma runsto_sRemove
  : forall (s_model : Ensemble W)
           (w_label : StringMap.key)
           (w_value : W)
           (s_label : StringMap.key)
           (x_label : StringMap.key)
           (env : Env FacadeADT)
           (st st' : State FacadeADT)
           (sRemove_pointer : W),
      s_label <> x_label ->
      st [s_label >> AxSpec.ADT (FEnsemble s_model)] ->
      st [w_label >> SCA _ w_value] ->
      Word2Spec env sRemove_pointer  = Some (Axiomatic FEnsemble_sRemove) ->
      RunsTo env (Call x_label sRemove_pointer (s_label :: w_label :: nil)) st st' ->
      StringMap.Equal st'
                      (StringMap.add x_label SCAZero
                                     (StringMap.add s_label (AxSpec.ADT (FEnsemble (Subtract _ s_model w_value))) st)).
  Proof.
    intros * label_neq s_init w_init sRemove_Pointer_is_sRemove runs_to.
    inversion_clear' runs_to; simpl in *; autoinj;
    [ | congruence].

    rewrite sRemove_Pointer_is_sRemove in *; autoinj.
    unfold FEnsemble_sRemove in *; clear sRemove_Pointer_is_sRemove; simpl in *;
    autodestruct; subst;
    rewrite StringMapFacts.find_mapsto_iff in * |- ;
    unfold sel in *.

    subst_find; simpl in *; setoid_rewrite w_init in H5; simpl in *; (* subst_find doesn't work on w_label *)
    autoinj.

    destruct output; [congruence|].
    destruct output; [congruence|].
    simpl in *; autoinj.
  Qed.

  (* Specification of state after running sIn. *)
  Lemma runsto_sIn
  : forall (s_model : Ensemble W)
           (w_label : StringMap.key)
           (w_value : W)
           (s_label : StringMap.key)
           (x_label : StringMap.key)
           (env : Env FacadeADT)
           (st st' : State FacadeADT)
           (sIn_pointer : W),
      s_label <> x_label ->
      st [s_label >> AxSpec.ADT (FEnsemble s_model)] ->
      st [w_label >> SCA _ w_value] ->
      Word2Spec env sIn_pointer  = Some (Axiomatic FEnsemble_sIn) ->
      RunsTo env (Call x_label sIn_pointer (s_label :: w_label :: nil)) st st' ->
      exists ret,
        (ret = SCAZero <-> Ensembles.In _ s_model w_value)
        /\ (ret = SCAOne <-> ~ Ensembles.In _ s_model w_value)
        /\ StringMap.Equal st'
                           (StringMap.add x_label ret
                                          (StringMap.add s_label (AxSpec.ADT (FEnsemble s_model)) st)).
  Proof.
    intros * label_neq s_init w_init sIn_Pointer_is_sIn runs_to.
    inversion_clear' runs_to; simpl in *; autoinj;
    [ | congruence].

    rewrite sIn_Pointer_is_sIn in *; autoinj.
    unfold FEnsemble_sIn in *; clear sIn_Pointer_is_sIn; simpl in *;
    autodestruct; subst;
    rewrite StringMapFacts.find_mapsto_iff in * |- ;
    unfold sel in *.

    subst_find; simpl in *; setoid_rewrite w_init in H5; simpl in *; (* subst_find doesn't work on w_label *)
    autoinj.

    destruct output; [congruence|].
    destruct output; [congruence|].

    simpl in *; autoinj; eauto.
  Qed.

  Arguments Word.natToWord : simpl never. (* simplifying natToWord causes crazy slowdown. *)

  (* Specification of state after running sSize. *)
  Lemma runsto_sSize
  : forall (s_model : Ensemble W)
           (s_label : StringMap.key)
           (x_label : StringMap.key)
           (env : Env FacadeADT)
           (st st' : State FacadeADT)
           (sSize_pointer : W),
      s_label <> x_label ->
      st [s_label >> AxSpec.ADT (FEnsemble s_model)] ->
      Word2Spec env sSize_pointer  = Some (Axiomatic FEnsemble_sSize) ->
      RunsTo env (Call x_label sSize_pointer (s_label :: nil)) st st' ->
      exists ret n,
        cardinal _ s_model n
        /\ ret = SCA _ (Word.natToWord 32 n)
        /\ StringMap.Equal st'
                           (StringMap.add x_label ret
                                          (StringMap.add s_label (AxSpec.ADT (FEnsemble s_model)) st)).
  Proof.
    intros * label_neq s_init sSize_Pointer_is_sSize runs_to.
    inversion_clear' runs_to; simpl in *; autoinj;
    [ | congruence].

    rewrite sSize_Pointer_is_sSize in *; autoinj.
    unfold FEnsemble_sSize in *; clear sSize_Pointer_is_sSize; simpl in *;
    autodestruct; subst;
    rewrite StringMapFacts.find_mapsto_iff in * |- ;
    unfold sel in *.

    subst_find; simpl in *; autoinj.

    destruct output; [congruence|].
    simpl in *; autoinj; eauto.
  Qed.

End runsto_FiniteSet.

Section compile_FiniteSet_Methods.

  Variable FiniteSetImpl : FullySharpened FiniteSetSpec.

  (* [AbsImpl] maps the state of the sharpend ADT to the Spec. *)
  Definition AbsImpl r :=
    fun x => exists s, AbsR (projT2 FiniteSetImpl) s r /\ In _ s x.

  (* First we show how to break down the components of an
     [Add] method call. *)

  Lemma compile_AbsImpl_Add
  : forall {env},
    forall vseq vhead,
    forall init_scas inter_scas final_scas init_adts inter_adts final_adts knowledge rep new_w,
      vhead <> vseq ->
      refine (@Prog _ env knowledge
                    init_scas final_scas
                    init_adts ([vseq >adt>
                                FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sAdd rep new_w))) ] :: final_adts))
             (pnew_w <- (@Prog _ env knowledge
                               init_scas ([vhead >sca> new_w]::init_scas)
                               init_adts init_adts);
              p_rep <- (@Prog _ env knowledge
                              ([vhead >sca> new_w]::init_scas) ([vhead >sca> new_w]::init_scas)
                              init_adts ([vseq >adt> FEnsemble (AbsImpl rep) ]::inter_adts));
              pAdd <- (@Prog _ env knowledge
                             ([vhead >sca> new_w]::init_scas) inter_scas
                             ([vseq >adt> FEnsemble (AbsImpl rep) ]::inter_adts)
                             ([vseq >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sAdd rep new_w)))]::final_adts));
              pclean <- (@Prog _ env knowledge
                               inter_scas final_scas
                               ([vseq >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sAdd rep new_w)))]::final_adts)
                               ([vseq >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sAdd rep new_w)))]::final_adts));
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
    destruct H; unfold In in *.
    destruct_ex; intuition.
    pose proof (ADTRefinementPreservesMethods
                  (projT2 FiniteSetImpl)
                  {| bindex := sAdd |} _ _ w' H0 (ReturnComputes _)) as ref;
      unfold refineMethod in ref.
    inversion_by computes_to_inv; injections; subst.
    simpl in *; rewrite <- H4.
    simpl; eexists; split; eauto.
    unfold Add; constructor; eauto.
    inversion H; subst.
    exists (Add _ s x); unfold Add; simpl; intuition.
    pose proof (ADTRefinementPreservesMethods
                  (projT2 FiniteSetImpl)
                  {| bindex := sAdd |} _ _ x s_r_eqv (ReturnComputes _)) as ref;
      unfold refineMethod in ref.
    inversion_by computes_to_inv; injections; subst.
    rewrite <- H3; simpl in *; eauto.
    constructor 2; eauto.
    simpl.
    - destruct_ex.
      intuition.
      pose proof (ADTRefinementPreservesMethods
                    (projT2 FiniteSetImpl)
                    {| bindex := sIn |} _ _ x H0 (ReturnComputes _)) as ref;
        unfold refineMethod in ref.
      inversion_by computes_to_inv; injections; subst.
      rewrite <- H2 in H1; simpl in *; subst.
      pose proof (ADTRefinementPreservesMethods
                    (projT2 FiniteSetImpl)
                    {| bindex := sAdd |} _ _ w' s_r_eqv (ReturnComputes _)) as ref;
        unfold refineMethod in ref.
      inversion_by computes_to_inv; injections; subst; simpl in *.
      rewrite <- H6 in H4; simpl in *; injections.
      pose proof (ADTRefinementPreservesMethods
                    (projT2 FiniteSetImpl)
                    {| bindex := sIn |} _ _ x H5 (ReturnComputes _)) as ref;
        unfold refineMethod in ref.
      inversion_by computes_to_inv; injections; subst.
      rewrite <- H4 in H8; injections; subst.
      pose proof ((proj1 H1) (refl_equal _)) as H'; destruct H'.
      constructor; eexists s; eauto.
      constructor 2; eauto.
  Qed.

  (* Finally we show how to compile the method call, once we have method bodies for its two arguments. *)
  Lemma compile_sAdd
  : forall {env},
    forall vens vhead vpointer vdiscard label w r s,
    forall scas adts knowledge w'
           (s_r_eqv : AbsR (projT2 FiniteSetImpl) s r),
      Label2Word env label = Some w ->
      Word2Spec env w = Some (Axiomatic FEnsemble_sAdd) ->
      ~ StringMap.In vpointer adts ->
      ~ StringMap.In vdiscard adts ->
      ~ StringMap.In vens scas ->
      vpointer <> vens ->
      vpointer <> vhead ->
      vhead <> vens ->
      vens <> vdiscard ->
      adts[vens >> AxSpec.ADT (FEnsemble s)] ->
      scas[vhead >> SCA _ w'] ->
      refine (@Prog _ env knowledge
                    scas
                    ([vdiscard >sca> 0]::[vpointer >sca> w]::scas)
                    ([vens >adt> FEnsemble (AbsImpl r) ] :: adts)
                    ([vens >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sAdd r w'))) ] :: adts))
             (ret (Label vpointer label;
                   Call vdiscard (Var vpointer) (vens :: vhead :: nil))%facade).
  Proof.
    unfold refine, Prog, ProgOk; intros;
    inversion_by computes_to_inv;
    subst; constructor; split; intros;
    destruct_pairs.
    (* Safe *)
    + repeat (constructor; intros).
    - econstructor; [ | eapply not_in_adts_not_mapsto_adt ]; try eassumption; map_iff_solve intuition.
    - inversion_facade; mapsto_eq_add; (* TODO this line above should also work in other similar theorems *)
      eq_transitive; autoinj;
      econstructor; eauto 2 using mapsto_eval.

      eauto using NoDup_0, NoDup_1, NoDup_2. (* TO COPY *)

      scas_adts_mapsto.

      try apply mapM_MapsTo_1; (* TODO: this, too, should work in other proofs *)
        try apply mapM_MapsTo_2;
        eauto;
        rewrite_Eq_in_goal;
        map_iff_solve idtac;
        eassumption.

      eapply not_in_adts_not_mapsto_adt;
        [ rewrite_Eq_in_goal; apply add_adts_pop_sca; [ | eassumption ] | ];
        map_iff_solve intuition.

      simpl; eexists; try eexists. reflexivity.

      (* RunsTo *)
      + inversion_facade.
        eapply RunsTo_label in H16; eauto.
        eapply RunsTo_Var in H19; eauto.
        eapply runsto_sAdd in H19; eauto;
        try (rewrite_Eq_in_goal; map_iff_solve eauto;
             scas_adts_mapsto; eassumption).

        split; repeat rewrite_Eq_in_goal.
        repeat (first [ apply SomeSCAs_chomp
                      | apply add_sca_pop_adts; [rewrite StringMapFacts.F.add_neq_in_iff; eassumption | ] ]);
          trivial.
        apply add_adts_pop_sca; map_iff_solve trivial.
        erewrite AbsImpl_Add by eauto.
        apply AllADTs_chomp_remove.
        rewrite H13; trickle_deletion.
        apply add_adts_pop_sca. map_iff_solve intuition.
        reflexivity.

        rewrite_Eq_in_goal; map_iff_solve eauto.
  Qed.

  Lemma compile_AbsImpl_Add
  : forall {env},
    forall vseq vhead,
    forall init_scas inter_scas final_scas init_adts inter_adts final_adts knowledge rep new_w,
      vhead <> vseq ->
      refine (@Prog _ env knowledge
                    init_scas final_scas
                    init_adts ([vseq >adt>
                                FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sAdd rep new_w))) ] :: final_adts))
             (pnew_w <- (@Prog _ env knowledge
                               init_scas ([vhead >sca> new_w]::init_scas)
                               init_adts init_adts);
              p_rep <- (@Prog _ env knowledge
                              ([vhead >sca> new_w]::init_scas) ([vhead >sca> new_w]::init_scas)
                              init_adts ([vseq >adt> FEnsemble (AbsImpl rep) ]::inter_adts));
              pAdd <- (@Prog _ env knowledge
                             ([vhead >sca> new_w]::init_scas) inter_scas
                             ([vseq >adt> FEnsemble (AbsImpl rep) ]::inter_adts)
                             ([vseq >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sAdd rep new_w)))]::final_adts));
              pclean <- (@Prog _ env knowledge
                               inter_scas final_scas
                               ([vseq >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sAdd rep new_w)))]::final_adts)
                               ([vseq >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sAdd rep new_w)))]::final_adts));
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
    destruct H; unfold In in *.
    destruct_ex; intuition.
    pose proof (ADTRefinementPreservesMethods
                  (projT2 FiniteSetImpl)
                  {| bindex := sAdd |} _ _ w' H0 (ReturnComputes _)) as ref;
      unfold refineMethod in ref.
    inversion_by computes_to_inv; injections; subst.
    simpl in *; rewrite <- H4.
    simpl; eexists; split; eauto.
    unfold Add; constructor; eauto.
    inversion H; subst.
    exists (Add _ s x); unfold Add; simpl; intuition.
    pose proof (ADTRefinementPreservesMethods
                  (projT2 FiniteSetImpl)
                  {| bindex := sAdd |} _ _ x s_r_eqv (ReturnComputes _)) as ref;
      unfold refineMethod in ref.
    inversion_by computes_to_inv; injections; subst.
    rewrite <- H3; simpl in *; eauto.
    constructor 2; eauto.
    simpl.
    - destruct_ex.
      intuition.
      pose proof (ADTRefinementPreservesMethods
                    (projT2 FiniteSetImpl)
                    {| bindex := sIn |} _ _ x H0 (ReturnComputes _)) as ref;
        unfold refineMethod in ref.
      inversion_by computes_to_inv; injections; subst.
      rewrite <- H2 in H1; simpl in *; subst.
      pose proof (ADTRefinementPreservesMethods
                    (projT2 FiniteSetImpl)
                    {| bindex := sAdd |} _ _ w' s_r_eqv (ReturnComputes _)) as ref;
        unfold refineMethod in ref.
      inversion_by computes_to_inv; injections; subst; simpl in *.
      rewrite <- H6 in H4; simpl in *; injections.
      pose proof (ADTRefinementPreservesMethods
                    (projT2 FiniteSetImpl)
                    {| bindex := sIn |} _ _ x H5 (ReturnComputes _)) as ref;
        unfold refineMethod in ref.
      inversion_by computes_to_inv; injections; subst.
      rewrite <- H4 in H8; injections; subst.
      pose proof ((proj1 H1) (refl_equal _)) as H'; destruct H'.
      constructor; eexists s; eauto.
      constructor 2; eauto.
  Qed.

  (* Finally we show how to compile the method call, once we have method bodies for its two arguments. *)
  Lemma compile_sAdd
  : forall {env},
    forall vens vhead vpointer vdiscard label w r s,
    forall scas adts knowledge w'
           (s_r_eqv : AbsR (projT2 FiniteSetImpl) s r),
      Label2Word env label = Some w ->
      Word2Spec env w = Some (Axiomatic FEnsemble_sAdd) ->
      ~ StringMap.In vpointer adts ->
      ~ StringMap.In vdiscard adts ->
      ~ StringMap.In vens scas ->
      vpointer <> vens ->
      vpointer <> vhead ->
      vhead <> vens ->
      vens <> vdiscard ->
      adts[vens >> AxSpec.ADT (FEnsemble s)] ->
      scas[vhead >> SCA _ w'] ->
      refine (@Prog _ env knowledge
                    scas
                    ([vdiscard >sca> 0]::[vpointer >sca> w]::scas)
                    ([vens >adt> FEnsemble (AbsImpl r) ] :: adts)
                    ([vens >adt> FEnsemble (AbsImpl (fst (CallMethod (projT1 FiniteSetImpl) sAdd r w'))) ] :: adts))
             (ret (Label vpointer label;
                   Call vdiscard (Var vpointer) (vens :: vhead :: nil))%facade).
  Proof.
    unfold refine, Prog, ProgOk; intros;
    inversion_by computes_to_inv;
    subst; constructor; split; intros;
    destruct_pairs.
    (* Safe *)
    + repeat (constructor; intros).
    - econstructor; [ | eapply not_in_adts_not_mapsto_adt ]; try eassumption; map_iff_solve intuition.
    - inversion_facade; mapsto_eq_add; (* TODO this line above should also work in other similar theorems *)
      eq_transitive; autoinj;
      econstructor; eauto 2 using mapsto_eval.

      eauto using NoDup_0, NoDup_1, NoDup_2. (* TO COPY *)

      scas_adts_mapsto.

      try apply mapM_MapsTo_1; (* TODO: this, too, should work in other proofs *)
        try apply mapM_MapsTo_2;
        eauto;
        rewrite_Eq_in_goal;
        map_iff_solve idtac;
        eassumption.

      eapply not_in_adts_not_mapsto_adt;
        [ rewrite_Eq_in_goal; apply add_adts_pop_sca; [ | eassumption ] | ];
        map_iff_solve intuition.

      simpl; eexists; try eexists. reflexivity.

      (* RunsTo *)
      + inversion_facade.
        eapply RunsTo_label in H16; eauto.
        eapply RunsTo_Var in H19; eauto.
        eapply runsto_sAdd in H19; eauto;
        try (rewrite_Eq_in_goal; map_iff_solve eauto;
             scas_adts_mapsto; eassumption).

        split; repeat rewrite_Eq_in_goal.
        repeat (first [ apply SomeSCAs_chomp
                      | apply add_sca_pop_adts; [rewrite StringMapFacts.F.add_neq_in_iff; eassumption | ] ]);
          trivial.
        apply add_adts_pop_sca; map_iff_solve trivial.
        erewrite AbsImpl_Add by eauto.
        apply AllADTs_chomp_remove.
        rewrite H13; trickle_deletion.
        apply add_adts_pop_sca. map_iff_solve intuition.
        reflexivity.

        rewrite_Eq_in_goal; map_iff_solve eauto.
  Qed.

End compile_FiniteSet_Methods.
