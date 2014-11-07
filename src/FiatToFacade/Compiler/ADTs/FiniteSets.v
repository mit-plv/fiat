Require Import FiatToFacade.Compiler.Prerequisites FiatToFacade.Compiler.ADTs.ListsInversion.
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


Lemma compile_sAdd
      (FiniteSetImpl : FullySharpened FiniteSetSpec)
        : forall {env},
          forall vens vhead vpointer vdiscard label w r s,
          forall scas adts knowledge w',
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
                          ([vens >adt> FEnsemble (snd (CallMethod (projT1 FiniteSetImpl) sToEnsemble r tt)) ] :: adts)
                          ([vens >adt> FEnsemble (snd (CallMethod  (projT1 FiniteSetImpl) sToEnsemble (fst (CallMethod (projT1 FiniteSetImpl) sAdd r w')) tt)) ] :: adts))
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

    mapsto_eq_add.

    (* Annnnd.... couldn't get any farther. *)

    eapply runsto_cons_var in H19; eauto.

    split; repeat rewrite_Eq_in_goal.

    repeat (first [ apply SomeSCAs_chomp
                  | apply add_sca_pop_adts; [rewrite StringMapFacts.F.add_neq_in_iff; eassumption | ] ]);
      trivial.

    apply add_adts_pop_sca; map_iff_solve trivial.
    apply AllADTs_chomp_remove.

    rewrite H12.
    trickle_deletion.
    apply add_adts_pop_sca. map_iff_solve intuition.
    reflexivity.

    rewrite_Eq_in_goal; map_iff_solve idtac.
    scas_adts_mapsto; assumption.

    rewrite_Eq_in_goal; map_iff_solve idtac.
    scas_adts_mapsto; assumption.
Qed.


Lemma compile_list_delete :
  forall env label w vpointer vret vseq seq knowledge scas adts adts',
    Label2Word env label = Some w ->
    Word2Spec env w = Some (Axiomatic List_delete) ->
    ~ StringMap.In vpointer adts ->
    ~ StringMap.In vret adts ->
    ~ StringMap.In vseq scas ->
    vpointer <> vseq ->
    adts[vseq >> ADT (List seq)] ->
    StringMap.Equal adts' (StringMap.remove vseq adts) ->
    refine (@Prog _ env knowledge
                  scas ([vret >sca> 0]::[vpointer >> SCA FacadeADT w]::scas)
                  adts adts')
           (ret (Label vpointer label;
                 Call vret (Var vpointer) (vseq :: nil)))%facade.
Proof.
  unfold refine, Prog, ProgOk; intros;
  inversion_by computes_to_inv;
  subst; constructor; split; intros;
  destruct_pairs.

  (* Safe *)
  + repeat (constructor; intros).
    - econstructor; eauto 2 using not_in_adts_not_mapsto_adt.
    - inversion_facade; mapsto_eq_add; (* TODO *)
      eq_transitive; autoinj;
      econstructor; eauto 2 using mapsto_eval.
      repeat (constructor; eauto).

      scas_adts_mapsto.

      apply mapM_MapsTo_1; eauto.
      rewrite_Eq_in_goal.
      map_iff_solve idtac.
      eassumption.

      eapply not_in_adts_not_mapsto_adt.
      rewrite_Eq_in_goal; eauto using add_adts_pop_sca.
      assumption.
      simpl; eexists; reflexivity.

    (* RunsTo *)
  + inversion_facade.
    eapply RunsTo_label in H13; eauto.

    mapsto_eq_add.

    eapply runsto_delete' in H16; eauto.
    split; repeat rewrite_Eq_in_goal.

    repeat (apply SomeSCAs_chomp; trivial; trickle_deletion).

    apply SomeSCAs_not_In_remove; trivial.
    trickle_deletion.
    repeat (apply add_adts_pop_sca; [ map_iff_solve intuition | ]).
    apply AllADTs_chomp_remove'; intuition.

    scas_adts_mapsto.
    rewrite_Eq_in_goal; map_iff_solve ltac:(intuition eassumption).
Qed.

Lemma compile_new :
  forall {env},
  forall scas adts knowledge,
  forall vret vpointer label w,
    Label2Word env label = Some w ->
    Word2Spec env w = Some (Axiomatic List_new) ->
    ~ StringMap.In vpointer adts ->
    ~ StringMap.In vret adts ->
    ~ StringMap.In vret scas ->
    vpointer <> vret ->
    refine (@Prog _ env knowledge
                  scas ([vpointer >sca> w]::scas)
                  adts ([vret >adt> List nil]::adts))
           (ret (Label vpointer label;
                 Call vret (Var vpointer) nil)%facade).
Proof.
  unfold refine, Prog, ProgOk; intros;
  inversion_by computes_to_inv;
  subst; constructor; split; intros;
  destruct_pairs.

  (* Safe *)
  + repeat (constructor; intros).
    - econstructor; eauto 2 using not_in_adts_not_mapsto_adt.
    - inversion_facade; mapsto_eq_add; (* TODO *)
      eq_transitive; autoinj;
      econstructor; eauto 2 using mapsto_eval.
      constructor. reflexivity.
      eapply not_in_adts_not_mapsto_adt.
      rewrite_Eq_in_goal; eauto using add_adts_pop_sca.
      assumption.
      reflexivity.

  (* RunsTo *)
  + inversion_facade.
    eapply RunsTo_label in H11; eauto.

    mapsto_eq_add.
    eapply runsto_new in H14; eauto.
    split; repeat rewrite_Eq_in_goal.

    apply add_sca_pop_adts, SomeSCAs_chomp; trivial;
    rewrite StringMapFacts.F.add_neq_in_iff; assumption.

    apply AllADTs_chomp, add_adts_pop_sca; trivial;
    rewrite StringMapFacts.F.add_neq_in_iff; assumption.
Qed.


Lemma compile_copy :
  forall {env},
  forall scas adts knowledge seq,
  forall vret vfrom vpointer label w,
    Label2Word env label = Some w ->
    Word2Spec env w = Some (Axiomatic List_copy) ->
    ~ StringMap.In vpointer adts ->
    ~ StringMap.In vret adts ->
    ~ StringMap.In vret scas ->
    ~ StringMap.In vfrom scas ->
    vpointer <> vret ->
    vpointer <> vfrom ->
    adts[vfrom >> ADT (List seq)] ->
    refine (@Prog _ env knowledge
                  scas ([vpointer >sca> w]::scas)
                  adts ([vret >adt> List seq]::adts))
           (ret (Label vpointer label;
                 Call vret (Var vpointer) (vfrom :: nil))%facade).
Proof.
  unfold refine, Prog, ProgOk; intros;
  inversion_by computes_to_inv;
  subst; constructor; split; intros;
  destruct_pairs.

  (* Safe *)
  + repeat (constructor; intros).
    - econstructor; eauto 2 using not_in_adts_not_mapsto_adt.
    - inversion_facade; mapsto_eq_add; (* TODO *)
      eq_transitive; autoinj;
      econstructor; eauto 2 using mapsto_eval.
      repeat (constructor; eauto).

      scas_adts_mapsto.

      apply mapM_MapsTo_1; eauto.
      rewrite_Eq_in_goal.
      map_iff_solve idtac.
      eassumption.

      eapply not_in_adts_not_mapsto_adt.
      rewrite_Eq_in_goal; eauto using add_adts_pop_sca.
      assumption.
      simpl; eexists; reflexivity.

  (* RunsTo *)
  + inversion_facade.
    eapply RunsTo_label in H14; eauto.

    mapsto_eq_add.

    eapply runsto_copy_var in H17; eauto.
    split; repeat rewrite_Eq_in_goal.

    repeat (apply add_sca_pop_adts; [rewrite StringMapFacts.F.add_neq_in_iff; eassumption | ]).
    apply SomeSCAs_chomp; trivial.

    apply AllADTs_chomp, AllADTs_swap, add_adts_pop_sca; trivial.
    apply AllADTs_add_in; assumption.
    rewrite_Eq_in_goal; map_iff_solve idtac.
    scas_adts_mapsto; assumption.
Qed.

Lemma compile_pre_push :
  forall {env},
  forall vseq vhead,
  forall init_scas inter_scas final_scas init_adts inter_adts final_adts knowledge head seq,
    vhead <> vseq ->
    refine (@Prog _ env knowledge
                  init_scas final_scas
                  init_adts ([vseq >adt> List (head :: seq)] :: final_adts))
           (phead <- (@Prog _ env knowledge
                            init_scas ([vhead >sca> head]::init_scas)
                            init_adts init_adts);
            ptail <- (@Prog _ env knowledge
                            ([vhead >sca> head]::init_scas) ([vhead >sca> head]::init_scas)
                            init_adts ([vseq >adt> List seq]::inter_adts));
            ppush <- (@Prog _ env knowledge
                            ([vhead >sca> head]::init_scas) inter_scas
                            ([vseq >adt> List seq]::inter_adts)
                            ([vseq >adt> List (head :: seq)]::final_adts));
            pclean <- (@Prog _ env knowledge
                            inter_scas final_scas
                            ([vseq >adt> List (head :: seq)]::final_adts)
                            ([vseq >adt> List (head :: seq)]::final_adts));
            ret (phead; ptail; ppush; pclean)%facade)%comp.
Proof.
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  (* Safe *)
  repeat (constructor; split; intros);
  specialize_states;
  try assumption.

  (* RunsTo *)
  intros;
    repeat inversion_facade;
    specialize_states;
    intuition.
Qed.
