Require Import FiatToFacade.Compiler.Prerequisites.
Require Import FiatToFacade.Compiler.ADTs.ListsInversion FiatToFacade.Compiler.ADTs.Lists.
Require Import Facade.examples.FiatADTs GLabelMap.
Require Import QueryStructure.Refinements.AdditionalRefinementLemmas. (* TODO *)

Unset Implicit Arguments.

Ltac compile_fold_induction_is_empty_call :=
  match goal with
    | [ H: RunsTo _ (Call _ _ _) _ _ |- _ ] =>
      eapply runsto_is_empty in H;
        try eassumption;
        [ let H1 := fresh in
          destruct H as [ ? ([ (H & H1) | (H & H1) ] & ?) ];
            try solve [exfalso; apply H1; reflexivity]; subst
        | intuition .. ]
  end.

Ltac loop_body_prereqs :=
  split; [assumption|split];
  match goal with
    | [ H: RunsTo _ (Call _ _ _) _ _ |- _ ] =>
      eapply runsto_pop in H; try eauto;
      rewrite_Eq_in_goal;
      try map_iff_solve ltac:(intuition eassumption)
  end;
  rewrite_Eq_in_goal;
  [ apply Superset_swap_left; auto;
    apply add_sca_pop_adts; map_iff_solve idtac; auto;
    repeat apply SomeSCAs_chomp;
    eassumption
  | apply add_adts_pop_sca; try assumption;
    map_iff_solve intuition;
    apply AllADTs_swap; auto;
    apply add_adts_pop_sca; auto;
    map_iff_solve intuition;
    first [ eapply AllADTs_replace;
            eassumption
          | match goal with
              | [ H: AllADTs ?state ?adts |- AllADTs _ _ ] =>
                rewrite H;
                  first [ rewrite AllADTs_swap_left_iff by congruence;
                          apply AllADTs_chomp_remove;
                          trickle_deletion;
                          apply AllADTs_chomp;
                          reflexivity
                        | repeat (rewrite <- AllADTs_swap_iff;
                                  [ apply AllADTs_chomp_remove; trickle_deletion
                                  | solve [eauto] ]);
                          rewrite add_add_add';
                          reflexivity ]
            end
          ]
  ].

Definition compile_fold_base_pair_adt :
  forall {env},
  forall {acc_type} {wadt1 wadt2},
  forall {vseq vadt1 vadt2: StringMap.key},
  forall {thead tis_empty: StringMap.key},
  forall {fpop fempty},
  forall {loop compiled_loop},
  forall {knowledge scas adts},
    @ADTPairLoopBodyOk env acc_type loop compiled_loop knowledge scas adts
                    vseq vadt1 vadt2 thead tis_empty wadt1 wadt2 ->
    GLabelMap.find fempty env = Some (Axiomatic List_empty) ->
    GLabelMap.find fpop env  = Some (Axiomatic List_pop) ->
    vadt1 <> vadt2 ->
    vadt1 <> vseq ->
    vadt1 <> tis_empty ->
    vadt2 <> vseq ->
    vadt2 <> tis_empty ->
    thead <> vadt1 ->
    thead <> vadt2 ->
    thead <> vseq ->
    tis_empty <> vseq ->
    ~ StringMap.In thead adts ->
    ~ StringMap.In tis_empty adts ->
    ~ StringMap.In vseq scas ->
    forall seq (init: acc_type),
      refine (@Prog _ env knowledge
                    (scas)
                    ([tis_empty >sca> 1]::scas)
                    ([vadt1 >adt> wadt1 init]::[vadt2 >adt> wadt2 init]::[vseq >adt> List seq]::adts)
                    ([vadt1 >adt> wadt1 (List.fold_left loop seq init)]::[vadt2 >adt> wadt2 (List.fold_left loop seq init)]::[vseq >adt> List nil]::adts))
             (ret (Fold thead tis_empty vseq fpop fempty compiled_loop)).
Proof.
  unfold ADTPairLoopBodyOk, ADTPairLoopBodyProgCondition, Prog, ProgOk, refine; unfold_coercions;
  induction seq as [ | a seq ]; intros;

  [ | specialize (fun init => IHseq init _ (ReturnComputes _)) ];
  constructor; intros; destruct_pairs;
  split;
  inversion_by computes_to_inv;
  subst;
  scas_adts_mapsto.

  Require Import Permutation.

  (** Safe **)
  constructor.
  split; intros.

  (* Call is safe *)

  eapply safe_call_1;
    first [ eassumption
          | symmetry; eassumption (* TODO: Can be removed *)
          | simpl; eexists; reflexivity
          | map_iff_solve intuition ].

  (* (Non-running) loop is safe *)

  compile_fold_induction_is_empty_call.
  eapply SafeWhileFalse.
  eapply BoolToW_eval;
    [ reflexivity | rewrite_Eq_in_goal; map_iff_solve intuition ].

  (** RunsTo **)
  unfold Fold; intros; do 2 inversion_facade;
  try compile_fold_induction_is_empty_call;
  simpl;
  scas_adts_mapsto;
  mapsto_eq_add;
  try (match goal with
         | [ H: is_true _ _ |- _ ] => apply is_true_eq in H
       end; auto_mapsto_unique).

  split; rewrite_Eq_in_goal; map_iff_solve idtac.
  apply SomeSCAs_chomp; assumption.
  apply add_adts_pop_sca; [ map_iff_solve intuition | assumption ].

  (** Induction's safety **)
  constructor; split.

  (* Call safe *)
  eapply safe_call_1;
    first [ eassumption
          | symmetry; eassumption
          | simpl; eexists; reflexivity
          | map_iff_solve intuition ].

  (* Loop safe *)
  intros.
  compile_fold_induction_is_empty_call; try discriminate.
  mapsto_eq_add.

  constructor;
    [ unfold_coercions;
      rewrite is_true_eq;
      assumption | | ].

  constructor; split.

  (* Pop safe *)
  assert (st' [vseq >> ADT (List (a :: seq))])
    by (rewrite_Eq_in_goal; map_iff_solve intuition).

  eapply safe_call_1.
  eassumption.
  eassumption.
  rewrite_Eq_in_goal.
  apply add_adts_pop_sca;
    [ | eassumption | .. ];
    map_iff_solve intuition.
  map_iff_solve intuition.
  simpl. eexists. eexists. reflexivity.

  intros.
  constructor.
  (* Loop body + next statement safe *)

  repeat match goal with
           | [ H: (forall acc head seq initial_state,
                     _ -> (forall final_state, RunsTo _ ?compiled_loop _ _ -> _))
               |- context[RunsTo _ ?compiled_loop ?initial _] ] =>
             specialize (fun p final => H init a seq initial p final);
               match type of H with
                 | ?cond -> _ => try pose cond as prereq
               end
         end.

  assert (prereq) as prereqs; unfold prereq in *; clear prereq.
  loop_body_prereqs.

  (* Loop body *)
  split.
  eauto.

  (* next statement *)
  intros.
  repeat match goal with
           | [ H: _ -> (forall final_state, _ -> _),
               H': RunsTo _ compiled_loop _ _ |- _ ] => specialize (H prereqs _ H')
         end.


  scas_adts_mapsto.
  eapply safe_call_1; try eassumption.
  map_iff_solve congruence.
  simpl; eexists; reflexivity.

  (* Actual loop induction *)
  intros.

  do 2 inversion_facade.

  repeat match goal with
           | [ H: (forall acc head seq initial_state,
                     _ -> (forall final_state, RunsTo _ ?compiled_loop _ _ -> _)),
               H': RunsTo _ ?compiled_loop ?initial _ |- _ ] =>
             specialize (fun p final => H init a seq initial p final);
               match type of H with
                 | ?cond -> _ => try pose cond as prereq
               end
         end.

  assert (prereq) as prereqs; unfold prereq in *; clear prereq.
  loop_body_prereqs.

  repeat match goal with
           | [ H: _ -> (forall final_state, _ -> _),
               H': RunsTo _ compiled_loop _ _ |- _ ] => specialize (H prereqs _ H')
         end.

  match goal with
    | [ H: RunsTo _ _ _ ?st |- Safe env _ ?st ] => apply (SafeSeq_inv H)
  end.
  specialize (IHseq (loop init a)); inversion_by computes_to_inv.
  match goal with
    | [ H: context[Fold] |- _ ] => unfold Fold in H; apply H
  end.

  tauto.

  (* Induction case for the loop *)
  simpl; intros.
  specialize (IHseq (loop init a)); inversion_by computes_to_inv.

  (* initial_state is at the very beginning of the loop.  We need to unfold one
     iteration first, and then deduce the new states *)

  unfold Fold in *.
  inversion_facade.

  (* TODO: This is a dupe of part of the loop_body_prereqs code *)
  match goal with
    | [ H: RunsTo _ (Call _ _ _) _ _ |- _ ] =>
      eapply runsto_is_empty in H; eauto;
      destruct H as [ret (ret_val & state_eq)];
      destruct ret_val; destruct_pairs; try discriminate (* Remove the list empty case *)
  end.

  assert (is_true st' (tis_empty = 0)%facade) by
      (unfold_coercions; rewrite is_true_eq;
       rewrite_Eq_in_goal;
       map_iff_solve intuition). (* TODO this should be a lemma *)

  inversion_facade; try (exfalso; eapply true_and_false; eassumption).

  (* Unfold one loop iteration, but keep the last statement, and merge it back at the beginning of the while, to recreate the induction condition. *)

  repeat match goal with
           | [ H: RunsTo _ (Seq _ _) _ _ |- _ ] =>
             inversion_clear' H
         end.

  (* Copied from earlier *)
  repeat match goal with
           | [ H: (forall acc head seq initial_state,
                     _ -> (forall final_state, RunsTo _ ?compiled_loop _ _ -> _)),
               H': RunsTo _ ?compiled_loop ?initial _ |- _ ] =>
             specialize (fun p final => H init a seq initial p final);
               match type of H with
                 | ?cond -> _ => try pose cond as prereq
               end
         end.

  assert (prereq) as prereqs; unfold prereq in *; clear prereq.
  loop_body_prereqs.

  repeat match goal with
           | [ H: _ -> (forall final_state, _ -> _),
               H': RunsTo _ compiled_loop _ _ |- _ ] => specialize (H prereqs _ H'); pose H
         end.
  (* </Copied> *)

  (* Stick together the last statement and the body of the loop *)
  match goal with
    | [ Hlast: RunsTo _ _ ?initial_state ?st, Hloop: RunsTo _ (DFacade.While _ _) ?st ?final_state |- _ ] =>
      pose proof (RunsToSeq Hlast Hloop)
  end.
  specialize_states.
  split; intuition.
Qed.

Lemma PickComputes_inv: forall {A} (x: A) P,
                          computes_to (Pick (fun x => P x)) x -> P x.
Proof.
  intros; inversion_by computes_to_inv; assumption.
Qed.

Lemma map_add_remove_swap :
  forall {elt} k1 k2 v m,
    k1 <> k2 ->
    @StringMap.Equal elt
                     ([k1 >> v]::(StringMap.remove k2 m))
                     (StringMap.remove k2 ([k1 >> v]::m)).
Proof.
  intros; red; intros k3.
  map_iff_solve idtac.

  repeat (rewrite ?StringMapFacts.add_o;
          rewrite ?StringMapFacts.remove_o).
  destruct (StringMap.E.eq_dec k1 k3), (StringMap.E.eq_dec k2 k3);
    subst; congruence.
Qed.

Ltac autospecialize_simple :=
  repeat match goal with
           | [ H: ?a -> _, H': ?a |- _ ] =>
             match (type of a) with
               | Prop => specialize (H H')
             end
         end.

Lemma compile_fold_pair_adt :
  forall env,
  forall acc_type wadt1 wadt2,
  forall vseq vadt1 vadt2: StringMap.key,
  forall thead tis_empty: StringMap.key,
  forall fpop fempty,
  forall loop,
  forall knowledge scas adts,
    GLabelMap.find fempty env = Some (Axiomatic List_empty) ->
    GLabelMap.find fpop env  = Some (Axiomatic List_pop) ->
    vadt1 <> vadt2 ->
    vadt1 <> vseq ->
    vadt1 <> tis_empty ->
    vadt2 <> vseq ->
    vadt2 <> tis_empty ->
    thead <> vadt1 ->
    thead <> vadt2 ->
    thead <> vseq ->
    tis_empty <> vseq ->
    ~ StringMap.In thead adts ->
    ~ StringMap.In tis_empty adts ->
    ~ StringMap.In vseq scas ->
    ~ StringMap.In tis_empty scas ->
    forall seq init,
      refine (@Prog _ env knowledge
                    scas scas
                    ([vseq >adt> List seq]::adts)
                    ([vadt1 >adt> wadt1 (List.fold_left loop seq init)]
                       ::[vadt2 >adt> wadt2 (List.fold_left loop seq init)]
                       ::[vseq >adt> List nil]::adts))
             (cloop <- { cloop | @ADTPairLoopBodyOk env acc_type loop cloop knowledge
                                                    scas adts vseq vadt1 vadt2 thead tis_empty wadt1 wadt2 };
              pinitadt1 <- (@Prog _ env knowledge
                                 scas scas
                                 ([vseq >adt> List seq]::adts)
                                 ([vadt2 >adt> wadt2 init]::[vseq >adt> List seq]::adts));
              pinitadt2 <- (@Prog _ env knowledge
                                 scas scas
                                 ([vadt2 >adt> wadt2 init]::[vseq >adt> List seq]::adts)
                                 ([vadt1 >adt> wadt1 init]::[vadt2 >adt> wadt2 init]::[vseq >adt> List seq]::adts));
              ret (pinitadt1; pinitadt2; Fold thead tis_empty vseq fpop fempty cloop)%facade)%comp.
Proof.
  unfold refine; intros.
  inversion_by computes_to_inv;
    subst;
    constructor;
    match goal with
      | [ H: _ |- _ ] => apply PickComputes_inv in H; unfold ProgOk in H
    end. unfold ProgOk in * ;
    intros; destruct_pairs;
    specialize_states;
    destruct_pairs.

  match goal with
    | [ H: context[ADTPairLoopBodyOk], H': context[GLabelMap.find], H'': context[GLabelMap.find] |- _ ] =>
      pose proof (compile_fold_base_pair_adt H H' H'')
  end.

  autospecialize_simple.
  unfold refine, Prog, ProgOk in *.

  match goal with
    | [ H: _ -> _ -> _ |- _ ] => specialize (H seq init _ (ReturnComputes _))
  end.
  inversion_by computes_to_inv.

  split.

  (* Safe *)
  repeat (safe_seq; intros).
  specialize_states; intuition.

  (* RunsTo *)
  intros; destruct_pairs.
  repeat inversion_facade.
  specialize_states.
  split; [ | intuition ].

  (* Tricks to get rid of is_empty *)
  rewrite (not_in_remove_eq tis_empty scas); eauto.
  eapply SomeSCAs_remove; eauto.
Qed.

Definition compile_fold_base_pair :
  forall {env},
  forall {acc_type wsca wadt},
  forall {vseq vsca vadt: StringMap.key},
  forall {thead tis_empty: StringMap.key},
  forall {fpop fempty},
  forall {loop compiled_loop},
  forall {knowledge scas adts},
    @PairLoopBodyOk env acc_type loop compiled_loop knowledge scas adts
                    vseq vsca vadt thead tis_empty wsca wadt ->
    GLabelMap.find fempty env = Some (Axiomatic List_empty) ->
    GLabelMap.find fpop env  = Some (Axiomatic List_pop) ->
    vsca <> vadt ->
    vsca <> vseq ->
    vsca <> tis_empty ->
    vadt <> vseq ->
    vadt <> tis_empty ->
    thead <> vsca ->
    thead <> vadt ->
    thead <> vseq ->
    tis_empty <> vseq ->
    ~ StringMap.In thead adts ->
    ~ StringMap.In tis_empty adts ->
    ~ StringMap.In vseq scas ->
    forall seq (init: acc_type),
      refine (@Prog _ env knowledge
                    ([vsca >sca> wsca init]::scas)
                    ([tis_empty >sca> 1]::[vsca >sca> wsca (List.fold_left loop seq init)]::scas)
                    ([vadt >adt> wadt init]::[vseq >adt> List seq]::adts) ([vadt >adt> wadt (List.fold_left loop seq init)]::[vseq >adt> List nil]::adts))
             (ret (Fold thead tis_empty vseq fpop fempty compiled_loop)).
Proof.
  unfold PairLoopBodyOk, PairLoopBodyProgCondition, Prog, ProgOk, refine; unfold_coercions;
  induction seq as [ | a seq ]; intros;
  [ | specialize (fun init => IHseq init _ (ReturnComputes _)) ];
  constructor; intros; destruct_pairs;
  split;
  inversion_by computes_to_inv;
  subst;
  scas_adts_mapsto.

  (** Safe **)
  constructor.
  split; intros.

  (* Call is safe *)

  eapply safe_call_1;
    first [ eassumption
          | symmetry; eassumption (* TODO: Can be removed *)
          | simpl; eexists; reflexivity
          | map_iff_solve intuition ].

  (* (Non-running) loop is safe *)

  compile_fold_induction_is_empty_call.
  eapply SafeWhileFalse.
  eapply BoolToW_eval;
    [ reflexivity | rewrite_Eq_in_goal; map_iff_solve intuition ].

  (** RunsTo **)
  unfold Fold; intros; do 2 inversion_facade;
  try compile_fold_induction_is_empty_call;
  simpl;
  scas_adts_mapsto;
  mapsto_eq_add;
  try (match goal with
         | [ H: is_true _ _ |- _ ] => apply is_true_eq in H
       end; auto_mapsto_unique).

  split; rewrite_Eq_in_goal; map_iff_solve idtac.
  apply SomeSCAs_chomp; assumption.
  apply add_adts_pop_sca; [ map_iff_solve intuition | assumption ].

  (** Induction's safety **)
  constructor; split.

  (* Call safe *)
  eapply safe_call_1;
    first [ eassumption
          | symmetry; eassumption
          | simpl; eexists; reflexivity
          | map_iff_solve intuition ].

  (* Loop safe *)
  intros.
  compile_fold_induction_is_empty_call; try discriminate.
  mapsto_eq_add.

  constructor;
    [ unfold_coercions;
      rewrite is_true_eq;
      assumption | | ].

  constructor; split.

  (* Pop safe *)
  assert (st' [vseq >> ADT (List (a :: seq))])
    by (rewrite_Eq_in_goal; map_iff_solve intuition).

  eapply safe_call_1.
  eassumption.
  eassumption.
  rewrite_Eq_in_goal.
  apply add_adts_pop_sca;
    [ | eassumption | .. ];
    map_iff_solve intuition.
  map_iff_solve intuition.
  simpl. eexists. eexists. reflexivity.

  intros.
  constructor.
  (* Loop body + next statement safe *)

  repeat match goal with
           | [ H: (forall acc head seq initial_state,
                     _ -> (forall final_state, RunsTo _ ?compiled_loop _ _ -> _))
               |- context[RunsTo _ ?compiled_loop ?initial _] ] =>
             specialize (fun p final => H init a seq initial p final);
               match type of H with
                 | ?cond -> _ => try pose cond as prereq
               end
         end.

  assert (prereq) as prereqs; unfold prereq in *; clear prereq.
  loop_body_prereqs.

  (* Loop body *)
  split.
  eauto.

  (* next statement *)
  intros.
  repeat match goal with
           | [ H: _ -> (forall final_state, _ -> _),
               H': RunsTo _ compiled_loop _ _ |- _ ] => specialize (H prereqs _ H')
         end.

  scas_adts_mapsto.
  eapply safe_call_1; try eassumption.
  map_iff_solve congruence.
  simpl; eexists; reflexivity.

  (* Actual loop induction *)
  intros.

  do 2 inversion_facade.

  repeat match goal with
           | [ H: (forall acc head seq initial_state,
                     _ -> (forall final_state, RunsTo _ ?compiled_loop _ _ -> _)),
               H': RunsTo _ ?compiled_loop ?initial _ |- _ ] =>
             specialize (fun p final => H init a seq initial p final);
               match type of H with
                 | ?cond -> _ => try pose cond as prereq
               end
         end.

  assert (prereq) as prereqs; unfold prereq in *; clear prereq.
  loop_body_prereqs.

  repeat match goal with
           | [ H: _ -> (forall final_state, _ -> _),
               H': RunsTo _ compiled_loop _ _ |- _ ] => specialize (H prereqs _ H')
         end.

  match goal with
    | [ H: RunsTo _ _ _ ?st |- Safe env _ ?st ] => apply (SafeSeq_inv H)
  end.
  specialize (IHseq (loop init a)); inversion_by computes_to_inv.
  match goal with
    | [ H: context[Fold] |- _ ] => unfold Fold in H; apply H
  end.

  tauto.

  (* Induction case for the loop *)
  simpl; intros.
  specialize (IHseq (loop init a)); inversion_by computes_to_inv.

  (* initial_state is at the very beginning of the loop.  We need to unfold one
     iteration first, and then deduce the new states *)

  unfold Fold in *.
  inversion_facade.

  (* TODO: This is a dupe of part of the loop_body_prereqs code *)
  match goal with
    | [ H: RunsTo _ (Call _ _ _) _ _ |- _ ] =>
      eapply runsto_is_empty in H; eauto;
      destruct H as [ret (ret_val & state_eq)];
      destruct ret_val; destruct_pairs; try discriminate (* Remove the list empty case *)
  end.

  assert (is_true st' (tis_empty = 0)%facade) by
      (unfold_coercions; rewrite is_true_eq;
       rewrite_Eq_in_goal;
       map_iff_solve intuition). (* TODO this should be a lemma *)

  inversion_facade; try (exfalso; eapply true_and_false; eassumption).

  (* Unfold one loop iteration, but keep the last statement, and merge it back at the beginning of the while, to recreate the induction condition. *)

  repeat match goal with
           | [ H: RunsTo _ (Seq _ _) _ _ |- _ ] =>
             inversion_clear' H
         end.

  (* Copied from earlier *)
  repeat match goal with
           | [ H: (forall acc head seq initial_state,
                     _ -> (forall final_state, RunsTo _ ?compiled_loop _ _ -> _)),
               H': RunsTo _ ?compiled_loop ?initial _ |- _ ] =>
             specialize (fun p final => H init a seq initial p final);
               match type of H with
                 | ?cond -> _ => try pose cond as prereq
               end
         end.

  assert (prereq) as prereqs; unfold prereq in *; clear prereq.
  loop_body_prereqs.

  repeat match goal with
           | [ H: _ -> (forall final_state, _ -> _),
               H': RunsTo _ compiled_loop _ _ |- _ ] => specialize (H prereqs _ H'); pose H
         end.
  (* </Copied> *)

  (* Stick together the last statement and the body of the loop *)
  match goal with
    | [ Hlast: RunsTo _ _ ?initial_state ?st, Hloop: RunsTo _ (DFacade.While _ _) ?st ?final_state |- _ ] =>
      pose proof (RunsToSeq Hlast Hloop)
  end.
  specialize_states.
  split; intuition.
Qed.

Definition compile_fold_base_sca :
  forall {env},
  forall {vseq vret: StringMap.key},
  forall {thead tis_empty: StringMap.key},
  forall {fpop fempty},
  forall {loop compiled_loop},
  forall {knowledge scas adts},
    SCALoopBodyOk env loop compiled_loop knowledge scas adts vseq vret thead tis_empty ->
    GLabelMap.find (elt:=FuncSpec _) fempty env = Some (Axiomatic List_empty) ->
    GLabelMap.find (elt:=FuncSpec _) fpop env = Some (Axiomatic List_pop) ->
    vret <> vseq ->
    vret <> tis_empty ->
    thead <> vret ->
    thead <> vseq ->
    tis_empty <> vseq ->
    ~ StringMap.In thead adts ->
    ~ StringMap.In tis_empty adts ->
    ~ StringMap.In vseq scas ->
    forall seq init,
      refine (@Prog _ env knowledge
                    ([vret >sca> init]::scas) ([tis_empty >sca> 1]::[vret >sca> List.fold_left loop seq init]::scas)
                    ([vseq >adt> List seq]::adts) ([vseq >adt> List nil]::adts))
             (ret (Fold thead tis_empty vseq fpop fempty compiled_loop)).
Proof.
  unfold SCALoopBodyOk, SCALoopBodyProgCondition, Prog, ProgOk, refine; unfold_coercions;
  induction seq as [ | a seq ]; intros;
  [ | specialize (fun init => IHseq init _ (ReturnComputes _)) ];
  constructor; intros; destruct_pairs;
  split;
  inversion_by computes_to_inv;
  subst;
  scas_adts_mapsto.

  (** Safe **)
  constructor.
  split; intros.

  (* Call is safe *)

  eapply safe_call_1;
    first [ eassumption
          | symmetry; eassumption (* TODO: Can be removed *)
          | simpl; eexists; reflexivity
          | map_iff_solve intuition ].

  (* (Non-running) loop is safe *)

  compile_fold_induction_is_empty_call.
  eapply SafeWhileFalse.
  eapply BoolToW_eval;
    [ reflexivity | rewrite_Eq_in_goal; map_iff_solve intuition ].

  (** RunsTo **)
  unfold Fold; intros; do 2 inversion_facade;
  try compile_fold_induction_is_empty_call;
  simpl;
  scas_adts_mapsto;
  mapsto_eq_add;
  try (match goal with
         | [ H: is_true _ _ |- _ ] => apply is_true_eq in H
       end; auto_mapsto_unique).

  split; rewrite_Eq_in_goal; map_iff_solve idtac.
  apply SomeSCAs_chomp; assumption.
  apply add_adts_pop_sca; [ map_iff_solve intuition | assumption ].

  (** Induction's safety **)
  constructor; split.

  (* Call safe *)
  eapply safe_call_1;
    first [ eassumption
          | symmetry; eassumption
          | simpl; eexists; reflexivity
          | map_iff_solve intuition ].

  (* Loop safe *)
  intros.
  compile_fold_induction_is_empty_call; try discriminate.
  mapsto_eq_add.

  constructor;
    [ unfold_coercions;
      rewrite is_true_eq;
      assumption | | ].

  constructor; split.

  (* Pop safe *)
  assert (st' [vseq >> ADT (List (a :: seq))])
    by (rewrite_Eq_in_goal; map_iff_solve intuition).

  eapply safe_call_1.
  eassumption.
  eassumption.
  rewrite_Eq_in_goal.
  apply add_adts_pop_sca;
    [ | eassumption | .. ];
    map_iff_solve intuition.
  map_iff_solve intuition.
  simpl. eexists. eexists. reflexivity.

  intros.
  constructor.

  (* Loop body + next statement safe *)

  repeat match goal with
           | [ H: (forall acc head seq initial_state,
                     _ -> (forall final_state, RunsTo _ ?compiled_loop _ _ -> _))
               |- context[RunsTo _ ?compiled_loop ?initial _] ] =>
             specialize (fun p final => H init a seq initial p final);
               match type of H with
                 | ?cond -> _ => try pose cond as prereq
               end
         end.

  assert (prereq) as prereqs; unfold prereq in *; clear prereq.
  loop_body_prereqs.

  (* Loop body *)
  split.
  eauto.

  (* next statement *)
  intros.
  repeat match goal with
           | [ H: _ -> (forall final_state, _ -> _),
               H': RunsTo _ compiled_loop _ _ |- _ ] => specialize (H prereqs _ H')
         end.

  scas_adts_mapsto.
  eapply safe_call_1; try eassumption.
  map_iff_solve congruence.
  simpl; eexists; reflexivity.

  (* Actual loop induction *)
  intros.

  do 2 inversion_facade.

  repeat match goal with
           | [ H: (forall acc head seq initial_state,
                     _ -> (forall final_state, RunsTo _ ?compiled_loop _ _ -> _)),
               H': RunsTo _ ?compiled_loop ?initial _ |- _ ] =>
             specialize (fun p final => H init a seq initial p final);
               match type of H with
                 | ?cond -> _ => try pose cond as prereq
               end
         end.

  assert (prereq) as prereqs; unfold prereq in *; clear prereq.
  loop_body_prereqs.

  repeat match goal with
           | [ H: _ -> (forall final_state, _ -> _),
               H': RunsTo _ compiled_loop _ _ |- _ ] => specialize (H prereqs _ H')
         end.

  match goal with
    | [ H: RunsTo _ _ _ ?st |- Safe env _ ?st ] => apply (SafeSeq_inv H)
  end.
  specialize (IHseq (loop init a)); inversion_by computes_to_inv.
  match goal with
    | [ H: context[Fold] |- _ ] => unfold Fold in H; apply H
  end.

  tauto.

  (* Induction case for the loop *)
  simpl; intros.
  specialize (IHseq (loop init a)); inversion_by computes_to_inv.

  (* initial_state is at the very beginning of the loop.  We need to unfold one
     iteration first, and then deduce the new states *)

  unfold Fold in *.
  inversion_facade.

  (* TODO: This is a dupe of part of the loop_body_prereqs code *)
  match goal with
    | [ H: RunsTo _ (Call _ _ _) _ _ |- _ ] =>
      eapply runsto_is_empty in H; eauto;
      destruct H as [ret (ret_val & state_eq)];
      destruct ret_val; destruct_pairs; try discriminate (* Remove the list empty case *)
  end.

  assert (is_true st' (tis_empty = 0)%facade) by
      (unfold_coercions; rewrite is_true_eq;
       rewrite_Eq_in_goal;
       map_iff_solve intuition). (* TODO this should be a lemma *)

  inversion_facade; try (exfalso; eapply true_and_false; eassumption).

  (* Unfold one loop iteration, but keep the last statement, and merge it back at the beginning of the while, to recreate the induction condition. *)

  repeat match goal with
           | [ H: RunsTo _ (Seq _ _) _ _ |- _ ] =>
             inversion_clear' H
         end.

  (* Copied from earlier *)
  repeat match goal with
           | [ H: (forall acc head seq initial_state,
                     _ -> (forall final_state, RunsTo _ ?compiled_loop _ _ -> _)),
               H': RunsTo _ ?compiled_loop ?initial _ |- _ ] =>
             specialize (fun p final => H init a seq initial p final);
               match type of H with
                 | ?cond -> _ => try pose cond as prereq
               end
         end.

  assert (prereq) as prereqs; unfold prereq in *; clear prereq.
  loop_body_prereqs.

  repeat match goal with
           | [ H: _ -> (forall final_state, _ -> _),
               H': RunsTo _ compiled_loop _ _ |- _ ] => specialize (H prereqs _ H'); pose H
         end.
  (* </Copied> *)

  (* Stick together the last statement and the body of the loop *)
  match goal with
    | [ Hlast: RunsTo _ _ ?initial_state ?st, Hloop: RunsTo _ (DFacade.While _ _) ?st ?final_state |- _ ] =>
      pose proof (RunsToSeq Hlast Hloop)
  end.
  specialize_states.
  split; intuition.
Qed.

Definition compile_fold_base_adt :
  forall {env},
  forall {acc_type wrapper},
  forall {vseq vret: StringMap.key},
  forall {thead tis_empty: StringMap.key},
  forall {fpop fempty},
  forall {loop compiled_loop},
  forall {knowledge scas adts},
    @ADTLoopBodyOk env acc_type loop compiled_loop knowledge scas adts vseq vret thead tis_empty wrapper ->
    GLabelMap.find fempty env = Some (Axiomatic List_empty) ->
    GLabelMap.find fpop env  = Some (Axiomatic List_pop) ->
    vret <> vseq ->
    vret <> tis_empty ->
    thead <> vret ->
    thead <> vseq ->
    tis_empty <> vseq ->
    ~ StringMap.In thead adts ->
    ~ StringMap.In tis_empty adts ->
    ~ StringMap.In vseq scas ->
    forall seq (init: acc_type),
      refine (@Prog _ env knowledge
                    (scas) ([tis_empty >sca> 1]::scas)
                    ([vret >adt> wrapper init]::[vseq >adt> List seq]::adts) ([vret >adt> wrapper (List.fold_left loop seq init)]::[vseq >adt> List nil]::adts))
             (ret (Fold thead tis_empty vseq fpop fempty compiled_loop)).
Proof.
  unfold ADTLoopBodyOk, ADTLoopBodyProgCondition, Prog, ProgOk, refine; unfold_coercions;
  induction seq as [ | a seq ]; intros;
  [ | specialize (fun init => IHseq init _ (ReturnComputes _)) ];
  constructor; intros; destruct_pairs;
  split;
  inversion_by computes_to_inv;
  subst;
  scas_adts_mapsto.

  (** Safe **)
  constructor.
  split; intros.

  (* Call is safe *)
  eapply safe_call_1;
    first [ eassumption
          | symmetry; eassumption
          | simpl; eexists; reflexivity
          | map_iff_solve intuition ].

  (* (Non-running) loop is safe *)

  compile_fold_induction_is_empty_call.
  eapply SafeWhileFalse.
  eapply BoolToW_eval;
    [ reflexivity | rewrite_Eq_in_goal; map_iff_solve intuition ].

  (** RunsTo **)
  unfold Fold; intros; do 2 inversion_facade;
  try compile_fold_induction_is_empty_call;
  simpl;
  scas_adts_mapsto;
  mapsto_eq_add;
  try (match goal with
         | [ H: is_true _ _ |- _ ] => apply is_true_eq in H
       end; auto_mapsto_unique).

  split; rewrite_Eq_in_goal; map_iff_solve idtac.
  apply SomeSCAs_chomp; assumption.
  apply add_adts_pop_sca; [ map_iff_solve intuition | assumption ].

  (** Induction's safety **)
  constructor; split.

  (* Call safe *)
  eapply safe_call_1;
    first [ eassumption
          | symmetry; eassumption
          | simpl; eexists; reflexivity
          | map_iff_solve intuition ].

  (* Loop safe *)
  intros.
  compile_fold_induction_is_empty_call; try discriminate.
  mapsto_eq_add.

  constructor;
    [ unfold_coercions;
      rewrite is_true_eq;
      assumption | | ].

  constructor; split.

  (* Pop safe *)
  assert (st' [vseq >> ADT (List (a :: seq))])
    by (rewrite_Eq_in_goal; map_iff_solve intuition).

  eapply safe_call_1.
  eassumption.
  eassumption.
  rewrite_Eq_in_goal.
  apply add_adts_pop_sca;
    [ | eassumption | .. ];
    map_iff_solve intuition.
  map_iff_solve intuition.
  simpl. eexists. eexists. reflexivity.

  intros.
  constructor.

  (* Loop body + next statement safe *)

  repeat match goal with
           | [ H: (forall acc head seq initial_state,
                     _ -> (forall final_state, RunsTo _ ?compiled_loop _ _ -> _))
               |- context[RunsTo _ ?compiled_loop ?initial _] ] =>
             specialize (fun p final => H init a seq initial p final);
               match type of H with
                 | ?cond -> _ => try pose cond as prereq
               end
         end.

  assert (prereq) as prereqs; unfold prereq in *; clear prereq.
  loop_body_prereqs.

  (* Loop body *)
  split.
  eauto.

  (* next statement *)
  intros.
  repeat match goal with
           | [ H: _ -> (forall final_state, _ -> _),
               H': RunsTo _ compiled_loop _ _ |- _ ] => specialize (H prereqs _ H')
         end.

  scas_adts_mapsto.
  eapply safe_call_1; try eassumption.
  map_iff_solve congruence.
  simpl; eexists; reflexivity.

  (* Actual loop induction *)
  intros.

  do 2 inversion_facade.

  repeat match goal with
           | [ H: (forall acc head seq initial_state,
                     _ -> (forall final_state, RunsTo _ ?compiled_loop _ _ -> _)),
               H': RunsTo _ ?compiled_loop ?initial _ |- _ ] =>
             specialize (fun p final => H init a seq initial p final);
               match type of H with
                 | ?cond -> _ => try pose cond as prereq
               end
         end.

  assert (prereq) as prereqs; unfold prereq in *; clear prereq.
  loop_body_prereqs.

  repeat match goal with
           | [ H: _ -> (forall final_state, _ -> _),
               H': RunsTo _ compiled_loop _ _ |- _ ] => specialize (H prereqs _ H')
         end.

  match goal with
    | [ H: RunsTo _ _ _ ?st |- Safe env _ ?st ] => apply (SafeSeq_inv H)
  end.
  specialize (IHseq (loop init a)); inversion_by computes_to_inv.
  match goal with
    | [ H: context[Fold] |- _ ] => unfold Fold in H; apply H
  end.

  tauto.

  (* Induction case for the loop *)
  simpl; intros.
  specialize (IHseq (loop init a)); inversion_by computes_to_inv.

  (* initial_state is at the very beginning of the loop.  We need to unfold one
     iteration first, and then deduce the new states *)

  unfold Fold in *.
  inversion_facade.

  (* TODO: This is a dupe of part of the loop_body_prereqs code *)
  match goal with
    | [ H: RunsTo _ (Call _ _ _) _ _ |- _ ] =>
      eapply runsto_is_empty in H; eauto;
      destruct H as [ret (ret_val & state_eq)];
      destruct ret_val; destruct_pairs; try discriminate (* Remove the list empty case *)
  end.

  assert (is_true st' (tis_empty = 0)%facade) by
      (unfold_coercions; rewrite is_true_eq;
       rewrite_Eq_in_goal;
       map_iff_solve intuition). (* TODO this should be a lemma *)

  inversion_facade; try (exfalso; eapply true_and_false; eassumption).

  (* Unfold one loop iteration, but keep the last statement, and merge it back at the beginning of the while, to recreate the induction condition. *)

  repeat match goal with
           | [ H: RunsTo _ (Seq _ _) _ _ |- _ ] =>
             inversion_clear' H
         end.

  (* Copied from earlier *)
  repeat match goal with
           | [ H: (forall acc head seq initial_state,
                     _ -> (forall final_state, RunsTo _ ?compiled_loop _ _ -> _)),
               H': RunsTo _ ?compiled_loop ?initial _ |- _ ] =>
             specialize (fun p final => H init a seq initial p final);
               match type of H with
                 | ?cond -> _ => try pose cond as prereq
               end
         end.

  assert (prereq) as prereqs; unfold prereq in *; clear prereq.
  loop_body_prereqs.

  repeat match goal with
           | [ H: _ -> (forall final_state, _ -> _),
               H': RunsTo _ compiled_loop _ _ |- _ ] => specialize (H prereqs _ H'); pose H
         end.
  (* </Copied> *)

  (* Stick together the last statement and the body of the loop *)
  match goal with
    | [ Hlast: RunsTo _ _ ?initial_state ?st, Hloop: RunsTo _ (DFacade.While _ _) ?st ?final_state |- _ ] =>
      pose proof (RunsToSeq Hlast Hloop)
  end.
  specialize_states.
  split; intuition.
Qed.

Lemma compile_fold_sca :
  forall env,
  forall vseq vret: StringMap.key,
  forall thead tis_empty: StringMap.key,
  forall fpop fempty,
  forall loop,
  forall knowledge scas adts,
    GLabelMap.find fempty env = Some (Axiomatic List_empty) ->
    GLabelMap.find fpop env   = Some (Axiomatic List_pop) ->
    vret <> vseq ->
    vret <> tis_empty ->
    thead <> vret ->
    thead <> vseq ->
    tis_empty <> vseq ->
    ~ StringMap.In thead adts ->
    ~ StringMap.In tis_empty adts ->
    ~ StringMap.In vseq scas ->
    ~ StringMap.In tis_empty scas ->
    forall seq init,
      refine (@Prog _ env knowledge
                    (scas) ([vret >sca> List.fold_left loop seq init]::scas)
                    ([vseq >adt> List seq]::adts) ([vseq >adt> List nil]::adts))
             (cloop <- { cloop | SCALoopBodyOk env loop cloop knowledge
                                               scas adts vseq vret thead tis_empty };
              pinit <- (@Prog _ env knowledge
                              scas ([vret >sca> init]::scas)
                              ([vseq >adt> List seq]::adts) ([vseq >adt> List seq]::adts));
              ret (pinit; Fold thead tis_empty vseq fpop fempty cloop)%facade)%comp.
Proof.
  unfold refine; intros.
  inversion_by computes_to_inv;
    subst;
    constructor;
    match goal with
      | [ H: _ |- _ ] => apply PickComputes_inv in H; unfold ProgOk in H
    end; unfold ProgOk in * ;
    intros; destruct_pairs;
    specialize_states;
    destruct_pairs.

  match goal with
    | [ H: context[SCALoopBodyOk], H': context[GLabelMap.find], H'': context[GLabelMap.find] |- _ ] =>
      pose proof (compile_fold_base_sca H H' H'')
  end.

  autospecialize_simple.

  unfold refine, Prog, ProgOk in *.

  match goal with
    | [ H: _ -> _ -> _ |- _ ] => specialize (H seq init _ (ReturnComputes _))
  end.
  inversion_by computes_to_inv.

  split.

  (* Safe *)
  constructor; split; intuition.

  (* RunsTo *)
  intros; destruct_pairs.
  inversion_facade.
  specialize_states.
  split; [ | intuition ].

  (* Tricks to get rid of is_empty *)
  rewrite (not_in_remove_eq tis_empty scas); eauto.
  rewrite map_add_remove_swap; eauto.
  eapply SomeSCAs_remove; eauto.
Qed.

Lemma compile_fold_adt :
  forall env,
  forall acc_type wrapper,
  forall vseq vret: StringMap.key,
  forall thead tis_empty: StringMap.key,
  forall fpop fempty,
  forall loop,
  forall knowledge scas adts,
    GLabelMap.find fempty env = Some (Axiomatic List_empty) ->
    GLabelMap.find fpop env  = Some (Axiomatic List_pop) ->
    vret <> vseq ->
    vret <> tis_empty ->
    thead <> vret ->
    thead <> vseq ->
    tis_empty <> vseq ->
    ~ StringMap.In thead adts ->
    ~ StringMap.In tis_empty adts ->
    ~ StringMap.In vseq scas ->
    ~ StringMap.In tis_empty scas ->
    forall seq init,
      refine (@Prog _ env knowledge
                    (scas) (scas)
                    ([vseq >adt> List seq]::adts) ([vret >adt> wrapper (List.fold_left loop seq init)]
                                                     ::[vseq >adt> List nil]::adts))
             (cloop <- { cloop | @ADTLoopBodyOk env acc_type loop cloop knowledge
                                                scas adts vseq vret thead tis_empty wrapper };
              pinit <- (@Prog _ env knowledge
                              scas scas
                              ([vseq >adt> List seq]::adts) ([vret >adt> wrapper init]::[vseq >adt> List seq]::adts));
              ret (pinit; Fold thead tis_empty vseq fpop fempty cloop)%facade)%comp.
Proof.
  unfold refine; intros.
  inversion_by computes_to_inv;
    subst;
    constructor;
    match goal with
      | [ H: _ |- _ ] => apply PickComputes_inv in H; unfold ProgOk in H
    end. unfold ProgOk in * ;
    intros; destruct_pairs;
    specialize_states;
    destruct_pairs.

  match goal with
    | [ H: context[ADTLoopBodyOk], H': context[GLabelMap.find], H'': context[GLabelMap.find] |- _ ] =>
      pose proof (compile_fold_base_adt H H' H'')
  end.

  autospecialize_simple.
  unfold refine, Prog, ProgOk in *.

  match goal with
    | [ H: _ -> _ -> _ |- _ ] => specialize (H seq init _ (ReturnComputes _))
  end.
  inversion_by computes_to_inv.

  split.

  (* Safe *)
  constructor; split; intuition.

  (* RunsTo *)
  intros; destruct_pairs.
  inversion_facade.
  specialize_states.
  split; [ | intuition ].

  (* Tricks to get rid of is_empty *)
  rewrite (not_in_remove_eq tis_empty scas); eauto.
  (* REMOVED rewrite map_add_remove_swap; eauto. *)
  eapply SomeSCAs_remove; eauto.
Qed.

Lemma compile_fold_pair :
  forall env,
  forall acc_type wsca wadt,
  forall vseq vsca vadt: StringMap.key,
  forall thead tis_empty: StringMap.key,
  forall fpop fempty,
  forall loop,
  forall knowledge scas adts,
    GLabelMap.find fempty env = Some (Axiomatic List_empty) ->
    GLabelMap.find fpop env  = Some (Axiomatic List_pop) ->
    vsca <> vadt ->
    vsca <> vseq ->
    vsca <> tis_empty ->
    vadt <> vseq ->
    vadt <> tis_empty ->
    thead <> vsca ->
    thead <> vadt ->
    thead <> vseq ->
    tis_empty <> vseq ->
    ~ StringMap.In thead adts ->
    ~ StringMap.In tis_empty adts ->
    ~ StringMap.In vseq scas ->
    ~ StringMap.In tis_empty scas ->
    forall seq init,
      refine (@Prog _ env knowledge
                    (scas) ([vsca >sca> wsca (List.fold_left loop seq init)]::scas)
                    ([vseq >adt> List seq]::adts) ([vadt >adt> wadt (List.fold_left loop seq init)]
                                                     ::[vseq >adt> List nil]::adts))
             (cloop <- { cloop | @PairLoopBodyOk env acc_type loop cloop knowledge
                                                 scas adts vseq vsca vadt thead tis_empty wsca wadt };
              pinitsca <- (@Prog _ env knowledge
                                 scas ([vsca >sca> wsca init]::scas)
                                 ([vseq >adt> List seq]::adts) ([vseq >adt> List seq]::adts));
              pinitadt <- (@Prog _ env knowledge
                                 ([vsca >sca> wsca init]::scas) ([vsca >sca> wsca init]::scas)
                                 ([vseq >adt> List seq]::adts) ([vadt >adt> wadt init]::[vseq >adt> List seq]::adts));
              ret (pinitsca; pinitadt; Fold thead tis_empty vseq fpop fempty cloop)%facade)%comp.
Proof.
  unfold refine; intros.
  inversion_by computes_to_inv;
    subst;
    constructor;
    match goal with
      | [ H: _ |- _ ] => apply PickComputes_inv in H; unfold ProgOk in H
    end; unfold ProgOk in * ;
    intros; destruct_pairs;
    specialize_states;
    destruct_pairs.

  match goal with
    | [ H: context[PairLoopBodyOk], H': context[GLabelMap.find], H'': context[GLabelMap.find] |- _ ] =>
      pose proof (compile_fold_base_pair H H' H'')
  end.

  autospecialize_simple.
  unfold refine, Prog, ProgOk in *.

  match goal with
    | [ H: _ -> _ -> _ |- _ ] => specialize (H seq init _ (ReturnComputes _))
  end.
  inversion_by computes_to_inv.

  split.

  (* Safe *)
  repeat (safe_seq; intros).
  specialize_states.
  intuition.

  (* RunsTo *)
  intros; destruct_pairs.
  repeat inversion_facade.
  specialize_states.
  split; [ | intuition ].

  (* Tricks to get rid of is_empty *)
  rewrite (not_in_remove_eq tis_empty scas); eauto.
  rewrite map_add_remove_swap; eauto.
  eapply SomeSCAs_remove; eauto.
Qed.
