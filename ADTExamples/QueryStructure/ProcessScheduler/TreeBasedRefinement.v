Require Import List Omega Ensembles.

Require Import FMapAVL OrderedTypeEx.
Require Import FMapExtensions.
Require Import DBSchema SetEq AdditionalLemmas.
Require Export ADTRefinement.BuildADTRefinements.

Require Import GeneralInsertRefinements ListInsertRefinements
        GeneralQueryRefinements ListQueryRefinements.

Unset Implicit Arguments.

Module GenericTreeDB := FMapAVL.Make(Nat_as_OT). (* TODO: Add the generic implementation *)
Module Import DBExtraFacts := FMapExtensions GenericTreeDB.

Section TreeBasedRefinement.
  Open Scope type_scope.
  Open Scope Tuple_scope.

  Definition TreeDB : Type := GenericTreeDB.t Process.

  Definition NeatDB :=
    (nat * (TreeDB * TreeDB)).

  Definition AllSleepingSet ensemble :=
    fun (p: Process) => ensemble p /\ p!STATE = Sleeping.

  Definition AllRunningSet ensemble :=
    fun (p: Process) => ensemble p /\ p!STATE = Running.

  Definition KeyedOnPID (tree: TreeDB) :=
    forall (p: Process), 
      forall (a: nat), 
        GenericTreeDB.MapsTo a p tree ->
        a = p!PID.

  Lemma KeyedOnPID_add :
    forall process tree pid,
      KeyedOnPID tree ->
      process!PID = pid ->
      KeyedOnPID (GenericTreeDB.add pid process tree).
  Proof.
    unfold KeyedOnPID; intros.
    rewrite add_mapsto_iff in H1.
    destruct H1;
      intuition;
      subst; intuition.
  Qed.

  Definition NeatDB_equivalence old_rep (neat_db: NeatDB) :=
    let (next_pid, databases) := neat_db in
    let set_db := GetUnConstrRelation old_rep PROCESSES in
    (forall pid, (forall tuple, In _ set_db tuple -> tuple!PID = pid -> lt pid next_pid)) 
    /\
    (let (sleeping, running) := databases in
     (EnsembleListEquivalence (AllSleepingSet set_db) (GetValues sleeping) /\ 
      KeyedOnPID sleeping) 
     /\
     (EnsembleListEquivalence (AllRunningSet  set_db) (GetValues running ) /\
      KeyedOnPID running)).

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

  Notation "x '∈' y" := (In _ y x) (at level 50, no associativity).

  Lemma partition_set : 
    forall ens x,
      (fun x => AllRunningSet ens x \/ AllSleepingSet ens x) x <-> ens x.
  Proof.
    unfold AllRunningSet, AllSleepingSet; 
    intros ens x;
    destruct (x!STATE);
      tauto.
  Qed.

  Lemma decide_admit :
    forall c,
      refine 
        {b |
         decides b
                 (forall tup' : Tuple,
                    GetUnConstrRelation c PROCESSES tup' ->
                    tupleAgree
                      (<PID_COLUMN :: 0, STATE_COLUMN :: Sleeping, CPU_COLUMN :: 0>) tup'
                      [CPU_COLUMN; STATE_COLUMN]%SchemaConstraints ->
                    tupleAgree
                      (<PID_COLUMN :: 0, STATE_COLUMN :: Sleeping, CPU_COLUMN :: 0>) tup'
                      [PID_COLUMN]%SchemaConstraints)}
        (ret true).
  Proof. admit. Qed.
  
  Lemma decide_admit' :
    forall c,
      refine
        {b |
         decides b
                 (forall tup' : Tuple,
                    GetUnConstrRelation c PROCESSES tup' ->
                    tupleAgree 
                      tup' (<PID_COLUMN :: 0, STATE_COLUMN :: Sleeping, CPU_COLUMN :: 0>)
                      [CPU_COLUMN; STATE_COLUMN]%SchemaConstraints ->
                    tupleAgree 
                      tup' (<PID_COLUMN :: 0, STATE_COLUMN :: Sleeping, CPU_COLUMN :: 0>)
                      [PID_COLUMN]%SchemaConstraints)}
        (ret true).
  Proof. admit. Qed.

  Lemma refine_pick_fmap_add_matching :
    forall tree ens tuple pid (cond: Process -> Prop),
      cond tuple ->
      tuple!PID = pid ->
      KeyedOnPID tree ->
      (~ GenericTreeDB.In (elt:=Tuple) pid tree) ->
      (EnsembleListEquivalence
         (fun tuple' => In _ (GetUnConstrRelation ens PROCESSES) tuple' /\ cond tuple')
         (GetValues tree)) ->
      refine
        {a |
         EnsembleListEquivalence
           (fun tuple' =>
              In _ (GetUnConstrRelation
                      (UpdateUnConstrRelation 
                         ProcessSchedulerSchema ens PROCESSES
                         (RelationInsert tuple (GetUnConstrRelation ens PROCESSES)))
                      PROCESSES) tuple' /\ cond tuple')
           (GetValues a) /\ 
         KeyedOnPID a}
        (ret (GenericTreeDB.add pid tuple tree)).
  Proof.
    unfold refine;
    intros;
    inversion_by computes_to_inv;
    subst.
    constructor;
      split.
    unfold GetUnConstrRelation, RelationInsert, AllSleepingSet in *; simpl in *.
    
    apply (EnsembleListEquivalence_fmap_add_filtered _ (fun x => ilist_hd ens x)); 
      simpl;
      intuition.

    apply KeyedOnPID_add;
      intuition.
  Qed.

  Lemma refine_pick_fmap_add_not_matching :
    forall tree ens tuple (cond: Process -> Prop),
      (~ cond tuple) ->
      KeyedOnPID tree ->
      (EnsembleListEquivalence
         (fun tuple' => In _ (GetUnConstrRelation ens PROCESSES) tuple' /\ cond tuple')
         (GetValues tree)) ->
      refine
        {a |
         EnsembleListEquivalence
           (fun tuple' =>
              In _ (GetUnConstrRelation
                      (UpdateUnConstrRelation 
                         ProcessSchedulerSchema ens PROCESSES
                         (RelationInsert tuple (GetUnConstrRelation ens PROCESSES)))
                      PROCESSES) tuple' /\ cond tuple')
           (GetValues a) /\ 
         KeyedOnPID a}
        (ret tree).
  Proof.
    unfold refine;
    intros;
    inversion_by computes_to_inv;
    subst.
    constructor;
      split.
    unfold GetUnConstrRelation, RelationInsert, AllSleepingSet in *; simpl in *.
    
    unfold EnsembleListEquivalence, In in *;
      intros.

    rewrite <- H1.
    split; intros;
    intuition; subst; intuition.
    
    trivial.
  Qed. 

  Lemma NeatScheduler :
    Sharpened ProcessSchedulerSpec.
  Proof.
    hone representation using (@DropQSConstraints_SiR ProcessSchedulerSchema).

    hone mutator SPAWN.
    {
      remove trivial insertion checks.
      finish honing.
    }

    hone representation using NeatDB_equivalence.
 
    hone_observer' ENUMERATE.
 
    intros db state result computes set_db_unconstr set_db constr_unconstr_equiv db_equiv.

    destruct db as (next_pid & sleeping & running);
      unfold NeatDB_equivalence in db_equiv;
      destruct db_equiv as (nextpid_correct & (sleeping_correct & sleeping_keys)
                                            & (running_correct & running_keys)).

    pose proof (equiv_EnsembleListEquivalence 
                  (partition_set (GetUnConstrRelation set_db_unconstr PROCESSES))
                  (SetUnion_Or running_correct sleeping_correct)).

    unfold DropQSConstraints_SiR in constr_unconstr_equiv.
    pose proof H.
    rewrite <- constr_unconstr_equiv, GetRelDropConstraints in H.

    set (full_db := SetUnion (GetValues running) (GetValues sleeping)).

    unfold EnsembleListEquivalence, In, AllRunningSet, AllSleepingSet 
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

    intros db pid result computes set_db_unconstr set_db constr_unconstr_equiv db_equiv.

    destruct db as (next_pid & sleeping & running);
      unfold NeatDB_equivalence in db_equiv;
      destruct db_equiv as (nextpid_correct & (sleeping_correct & sleeping_keys)
                                            & (running_correct & running_keys)).

    pose proof (equiv_EnsembleListEquivalence 
                  (partition_set (GetUnConstrRelation set_db_unconstr PROCESSES))
                  (SetUnion_Or running_correct sleeping_correct)).

    unfold DropQSConstraints_SiR in constr_unconstr_equiv.
    pose proof H.
    rewrite <- constr_unconstr_equiv, GetRelDropConstraints in H.

    set (full_db := SetUnion (GetValues running) (GetValues sleeping)).
    
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

    hone mutator SPAWN.

    setoid_rewrite decide_admit.
    setoid_rewrite decide_admit'.
    setoid_rewrite refineEquiv_split_ex.
    setoid_rewrite refineEquiv_pick_computes_to_and.
    simplify with monad laws.
    setoid_rewrite refine_pick_eq_ex_bind. 

    unfold NeatDB_equivalence.
    simplify with monad laws.

    Require Import Utf8.
    simpl.

    unfold NeatDB.

    destruct r_n as (next_pid & sleeping & running);
      unfold NeatDB_equivalence in H;
      destruct H as (nextpid_correct & (sleeping_correct & sleeping_keys)
                                     & (running_correct & running_keys)).

    setoid_rewrite refine_let.
    setoid_rewrite (refine_pick_val _ (a := S next_pid)).

    simplify with monad laws.
    setoid_rewrite refine_let.

    simplify with monad laws. 
    setoid_rewrite (refine_pick_fmap_add_matching sleeping _ _ _ (fun x => x!STATE = Sleeping)); eauto.
    simplify with monad laws. 
    setoid_rewrite (refine_pick_fmap_add_not_matching running _ _ (fun x => x!STATE = Running)); eauto.
    simplify with monad laws.

    apply refine_ret_eq.
    unfold H0; clear H0.
    
    pull_definition.

    intuition.
    discriminate.

    admit. (* Really new PID *)

    unfold GetUnConstrRelation, UpdateUnConstrRelation, RelationInsert, In; simpl; intros.
    destruct H;
    subst; simpl in *.

    compute; omega.
    apply lt_S, (nextpid_correct _ tuple); intuition.

    finish sharpening.
  Defined.
End TreeBasedRefinement.

