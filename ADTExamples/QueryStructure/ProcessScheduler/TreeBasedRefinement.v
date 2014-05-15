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

  Lemma no_collisions_when_using_a_fresh_pid :
    forall pid c (tup tup': Process),
      tupleAgree tup tup' [PID_COLUMN]%SchemaConstraints ->
      (forall a, (GetUnConstrRelation c PROCESSES) a -> pid > (a PID)) ->
      tup!PID = pid ->
      GetUnConstrRelation c PROCESSES tup' ->
      False.
  Proof.
    unfold tupleAgree, GetAttribute; 
    simpl; 
    intuition;
    specialize (H0 tup' H2); 
    specialize (H PID); 
      subst; 
      intuition. 
  Qed.
      
  Lemma insert_always_happens :
    forall pid c,
      (forall a, (GetUnConstrRelation c PROCESSES) a -> pid > (a PID)) ->
      refine 
        {b |
         decides b
                 (forall tup' : Tuple,
                    GetUnConstrRelation c PROCESSES tup' ->
                    tupleAgree
                      (<PID_COLUMN :: pid, STATE_COLUMN :: Sleeping, CPU_COLUMN :: 0>) tup'
                      [PID_COLUMN]%SchemaConstraints ->
                    tupleAgree
                      (<PID_COLUMN :: pid, STATE_COLUMN :: Sleeping, CPU_COLUMN :: 0>) tup'
                      [CPU_COLUMN; STATE_COLUMN]%SchemaConstraints)
                    }
        (ret true).
  Proof.  
    intros; constructor; inversion_by computes_to_inv; subst; simpl.
    intros; exfalso; apply (no_collisions_when_using_a_fresh_pid pid c _ _ H1); trivial.
  Qed.
  
  Lemma tupleAgree_sym : 
    forall (heading: Heading) tup1 tup2 attrs,
      @tupleAgree heading tup1 tup2 attrs <-> @tupleAgree heading tup2 tup1 attrs.
  Proof.
    intros; unfold tupleAgree.
    intuition; symmetry; intuition.
  Qed.
  
  Lemma insert_always_happens' :
    forall pid c,
      (forall a, (GetUnConstrRelation c PROCESSES) a -> pid > (a PID)) ->
      refine 
        {b |
         decides b
                 (forall tup' : Tuple,
                    GetUnConstrRelation c PROCESSES tup' ->
                    tupleAgree
                      tup' (<PID_COLUMN :: pid, STATE_COLUMN :: Sleeping, CPU_COLUMN :: 0>)
                      [PID_COLUMN]%SchemaConstraints ->
                    tupleAgree
                      tup' (<PID_COLUMN :: pid, STATE_COLUMN :: Sleeping, CPU_COLUMN :: 0>)
                      [CPU_COLUMN; STATE_COLUMN]%SchemaConstraints)
                    }
        (ret true).
  Proof. 
    intros; constructor; inversion_by computes_to_inv; subst; simpl.
    intros; exfalso; rewrite tupleAgree_sym in H1; apply (no_collisions_when_using_a_fresh_pid pid c _ _ H1); trivial.
  Qed.

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

  Lemma InValues_In :
    forall tree tup,
      KeyedOnPID tree ->
      List.In tup (GetValues tree) ->
      (GenericTreeDB.In tup!PID tree). 
  Proof.
    unfold KeyedOnPID; intuition.
    apply (MapsTo_In _ tup).
    unfold GetValues in H0; rewrite <- MapsTo_snd in H0.
    destruct H0 as [key mapsto].
    pose proof (H _ _ mapsto); subst; trivial.
  Qed.

  Lemma In_InValues :
    forall tree pid,
      KeyedOnPID tree ->
      (GenericTreeDB.In pid tree) ->
      (exists tup, tup!PID = pid /\ List.In tup (GetValues tree)).
  Proof.
    unfold KeyedOnPID; intuition.
    unfold GetValues; setoid_rewrite <- MapsTo_snd.

    rewrite elements_in_iff in H0.
    destruct H0 as [val ina].
    rewrite <- elements_mapsto_iff in ina.
    pose proof (H _ _ ina); subst.
    eauto.
  Qed.
  

  Lemma NeatScheduler :
    Sharpened ProcessSchedulerSpec.
  Proof.
    hone representation using (@DropQSConstraints_SiR ProcessSchedulerSchema).

    hone mutator SPAWN.
    {
      unfold ForAll_In. (*TODO: Why does swapping these two calls break 'finish honing'?*)
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

    unfold NeatDB_equivalence, NeatDB in *;
      destruct r_n as (next_pid & sleeping & running);
      destruct H as (nextpid_correct & (sleeping_correct & sleeping_keys)
                                     & (running_correct & running_keys));
      simpl in *.

    setoid_rewrite refineEquiv_split_ex.
    setoid_rewrite refineEquiv_pick_computes_to_and.
    simplify with monad laws.

    setoid_rewrite (refine_pick_val _ (a := next_pid)); eauto.
    simplify with monad laws.
    setoid_rewrite insert_always_happens; eauto.
    simplify with monad laws.
    setoid_rewrite insert_always_happens'; eauto.
    simplify with monad laws.
    setoid_rewrite refine_pick_eq_ex_bind. 
    simplify with monad laws. 

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

    (* Didn't insert a running process *)
    discriminate.

    (* No duplicates *)
    
    unfold not; intro has_key.
    apply In_InValues in has_key; eauto.
    destruct has_key as [tup (collision & already_inserted)].
    unfold EnsembleListEquivalence in sleeping_correct; 
      rewrite <- sleeping_correct in already_inserted.
    
    apply weaken, (nextpid_correct tup!PID) in already_inserted; eauto.
    compute in collision, already_inserted.
    omega.

    (* Updated next_pid properly *)
    unfold In, GetUnConstrRelation, UpdateUnConstrRelation, RelationInsert in *; 
      simpl in *;
      intros pid tuple [ is_new_process | is_updated_process ] pid_eq; 
      subst;
      [ compute | apply lt_S, (nextpid_correct _ tuple) ]; 
      intuition.

    finish sharpening.
  Defined.
End TreeBasedRefinement.

