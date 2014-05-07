Require Import List Omega Ensembles.

Require Import FMapAVL OrderedTypeEx.
Require Import FMapExtensions.
Require Import DBSchema SetEq AdditionalLemmas.
Require Export ADTRefinement.BuildADTRefinements.

Unset Implicit Arguments.

Module GenericTreeDB := FMapAVL.Make(Nat_as_OT). (* TODO: Add the generic implementation *)
Module Import DBExtraFacts := FMapExtensions GenericTreeDB.

Section TreeBasedRefinement.
  Open Scope type_scope.
  Open Scope Tuple_scope.

  Definition TreeDB : Type := GenericTreeDB.t Process.

  Definition NeatDB :=
    (TreeDB * TreeDB). 

  Definition AllSleepingSet ensemble :=
    fun (p: Process) => ensemble p /\ p!STATE = Sleeping.

  Definition AllRunningSet ensemble :=
    fun (p: Process) => ensemble p /\ p!STATE = Running.

  Definition KeyedOnPID (tree: TreeDB) :=
    forall (p: Process), 
      forall (a: nat), 
        GenericTreeDB.MapsTo a p tree ->
        a = p!PID.

  Definition NeatDB_equivalence old_rep (neat_db: NeatDB) :=
    let (sleeping, running) := neat_db in
    let set_db := GetRelation old_rep PROCESSES in
    EnsembleListEquivalence (AllSleepingSet set_db) (GetValues sleeping) /\ 
    EnsembleListEquivalence (AllRunningSet  set_db) (GetValues running ) /\
    KeyedOnPID sleeping /\ KeyedOnPID running.

  Lemma filter_on_key :
    forall (tree: TreeDB) 
           (equality: nat -> nat -> bool)
           (equality_iff: forall x y, equality x y = true <-> x = y),
    forall (key: nat),
      KeyedOnPID tree -> 
      SetEq
        (List.filter
           (fun (p: Process) => equality (p!PID) key)
           (GetValues tree))
        (Option2Box 
           (GenericTreeDB.find key tree)).
  Proof.
    unfold KeyedOnPID.
    unfold SetEq, GetValues.
    intros; intuition.

    rewrite in_Option2Box.
    rewrite filter_In in *.
    rewrite in_map_iff in *.
    destruct H0 as ([x0 (_snd, in_seq)], _fst).
    unfold dec2bool in *.

    rewrite <- find_mapsto_iff.
    destruct x0.
    subst; simpl in *.
    apply in_elements_mapsto in in_seq.

    specialize (H p k in_seq).

    rewrite equality_iff in *.
    subst; trivial.

    (****)

    rewrite in_Option2Box in H0.
    rewrite filter_In in *.
    unfold dec2bool in *.
    rewrite <- find_mapsto_iff in H0.
    pose proof H0 as H2.
    rewrite elements_mapsto_iff in H0.
    apply InA_In_snd in H0.
    intuition.
    
    specialize (H x key H2).
    
    rewrite equality_iff in *.
    intuition.
  Qed.

  Lemma partition_set : 
    forall ens x,
      (fun x => AllRunningSet ens x \/ AllSleepingSet ens x) x <-> ens x.
  Proof.
    unfold AllRunningSet, AllSleepingSet; 
    intros ens x;
    destruct (x!STATE);
      tauto.
  Qed.

  Lemma NeatScheduler :
    Sharpened ProcessSchedulerSpec.
  Proof.
    hone representation' using NeatDB_equivalence.
 
    hone_observer' ENUMERATE.
 
    intros db state result computes set_db db_equiv.

    destruct db as (sleeping, running);
      unfold NeatDB_equivalence in db_equiv;
      destruct db_equiv as (sleeping_correct, (running_correct, (sleeping_keys, running_keys))).
    Check equiv_EnsembleListEquivalence.

    pose proof (equiv_EnsembleListEquivalence 
                  (partition_set (GetRelation set_db PROCESSES))
                  (SetUnion_Or running_correct sleeping_correct)).
    
    set (full_db := SetUnion (GetValues running) (GetValues sleeping)).

    unfold EnsembleListEquivalence, In, 
           AllRunningSet, AllSleepingSet 
      in sleeping_correct, running_correct. 
    
    symmetry in sleeping_correct, running_correct.

    rewrite (refine_ensemble_into_list full_db _ _ _ (fun p => beq_state p!STATE Running)) 
      in running_correct;
      eauto using beq_process_iff__state.

    rewrite (refine_ensemble_into_list full_db _ _ _ (fun p => beq_state p!STATE Sleeping)) 
      in sleeping_correct;
      eauto using beq_process_iff__state.

    rewrite (refine_ensemble_into_list_with_extraction full_db _ _ _ (fun p => beq_state p!STATE state));
      eauto using beq_process_iff__state.

    rewrite (state_eta_rule state (fun l => map _ _) (fun x => SetEq result x)).
    
    rewrite <- sleeping_correct, <- running_correct.

    rewrite <- !map_list_map_fmap.

    refine_eq_into_ret.
 
    pull_definition.

    hone_observer' GET_CPU_TIME.

    intros db pid result computes set_db db_equiv.

    destruct db as (sleeping, running);
      unfold NeatDB_equivalence in db_equiv;
      destruct db_equiv as (sleeping_correct, (running_correct, (sleeping_keys, running_keys))).

    set (full_db := SetUnion (GetValues running) (GetValues sleeping)).

    pose proof (equiv_EnsembleListEquivalence 
                  (partition_set (GetRelation set_db PROCESSES))
                  (SetUnion_Or running_correct sleeping_correct)).
    
    unfold EnsembleListEquivalence, In, AllRunningSet, AllSleepingSet 
      in sleeping_correct, running_correct. 
    symmetry in sleeping_correct, running_correct.

    rewrite (refine_ensemble_into_list full_db _ _ _ (fun p => beq_state p!STATE Running)) 
      in running_correct;
      eauto using beq_process_iff__state.

    rewrite (refine_ensemble_into_list full_db _ _ _ (fun p => beq_state p!STATE Sleeping)) 
      in sleeping_correct;
      eauto using beq_process_iff__state.

    rewrite (refine_ensemble_into_list_with_extraction full_db _ _ _ (fun p => beq_nat p!PID pid));
      eauto using beq_process_iff__pid.

    unfold full_db;
      rewrite filter_union.

    repeat rewrite filter_on_key; 
      eauto using beq_nat_true_iff.
    
    refine_eq_into_ret.
    
    pull_definition.
    
    (*
    Definition NeatDB_spawn db state :=
      let (sleeping, running) := db in
      match sleeping with
        | Sleeping => (GenericTreeDB.add 0 ()
    .
     *)

    hone' mutator SPAWN using _.

    intros; subst.
    unfold refine.
    intros.
    econstructor.
    constructor.
    intros.

    Focus 2. 
    constructor.
    reflexivity.

    unfold QSInsertSpec, RelationInsert;
      simpl.
    eexists.
    constructor.
    
    econstructor.
    constructor.
    intros.

    constructor.
    intros.
  Admitted.
End TreeBasedRefinement.

