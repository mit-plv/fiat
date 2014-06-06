Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation BuildADTRefinements
        QueryStructureSchema QueryStructure
        QueryQSSpecs InsertQSSpecs EmptyQSSpecs
        GeneralInsertRefinements GeneralQueryRefinements
        GeneralQueryStructureRefinements
        ListQueryRefinements ListInsertRefinements
        ListQueryStructureRefinements.

Require Import BagsOfTuples CachingBags Bool.
Require Import DBSchema SetEq AdditionalLemmas.
Require Export ADTRefinement.BuildADTRefinements.

Unset Implicit Arguments.

Definition StatePIDIndexedTree : @BagPlusBagProof (@Tuple ProcessSchema).
  mkIndex ProcessSchema [STATE; PID].
Defined.

Definition Storage := AddCachingLayer (BagProof StatePIDIndexedTree) (fun p => p PID)
                                      0 max (ListMax_cacheable 0).

Definition StorageType           := BagType Storage.
Definition StorageIsBag          := BagProof Storage.
Definition StorageSearchTermType := SearchTermType Storage.

Section TreeBasedRefinement.
  Open Scope type_scope.
  Open Scope Tuple_scope.

  Notation "x '∈' y" := (In _ y x) (at level 50, no associativity).

  Lemma no_collisions_when_using_a_fresh_pid :
    forall pid c (tup tup': Process),
      tupleAgree tup tup' [PID_COLUMN]%SchemaConstraints ->
      (forall a, (GetUnConstrRelation c PROCESSES) a -> pid > (a PID)) ->
      tup PID = pid ->
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
                      (<PID_COLUMN :: pid, STATE_COLUMN :: SLEEPING, CPU_COLUMN :: 0>) tup'
                      [PID_COLUMN]%SchemaConstraints ->
                    tupleAgree
                      (<PID_COLUMN :: pid, STATE_COLUMN :: SLEEPING, CPU_COLUMN :: 0>) tup'
                      [CPU_COLUMN; STATE_COLUMN]%SchemaConstraints)
                    }
        (ret true).
  Proof.
    intros; constructor; inversion_by computes_to_inv; subst; simpl.
    intros; exfalso; apply (no_collisions_when_using_a_fresh_pid pid c _ _ H1); trivial.
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
                      tup' (<PID_COLUMN :: pid, STATE_COLUMN :: SLEEPING, CPU_COLUMN :: 0>)
                      [PID_COLUMN]%SchemaConstraints ->
                    tupleAgree
                      tup' (<PID_COLUMN :: pid, STATE_COLUMN :: SLEEPING, CPU_COLUMN :: 0>)
                      [CPU_COLUMN; STATE_COLUMN]%SchemaConstraints)
                    }
        (ret true).
  Proof.
    intros; constructor; inversion_by computes_to_inv; subst; simpl.
    intros; exfalso; rewrite tupleAgree_sym in H1; apply (no_collisions_when_using_a_fresh_pid pid c _ _ H1); trivial.
  Qed.

  Lemma NeatScheduler :
    Sharpened ProcessSchedulerSpec.
  Proof.
    unfold ProcessSchedulerSpec.

    unfold ForAll_In; start honing QueryStructure.

    Definition equivalence := fun set_db (db: StorageType) =>
      EnsembleListEquivalence (GetUnConstrRelation set_db PROCESSES) (benumerate db).

    hone representation using equivalence. (* TODO: unfolding equiv here slows everything down. Why? *)
    
    hone constructor INIT. {
      repeat setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      repeat setoid_rewrite refineEquiv_pick_eq'.
      simplify with monad laws.

      rewrite (refine_pick_val' bempty) by apply EnsembleListEquivalence_Empty.
      subst_body; higher_order_1_reflexivity. 
    }

    hone method ENUMERATE. {
      unfold equivalence in H.

      setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      setoid_rewrite refineEquiv_pick_pair.
      setoid_rewrite refineEquiv_pick_eq'. 
      simplify with monad laws.
      simpl.

      rewrite (Equivalent_UnConstr_In_EnsembleListEquivalence) by eassumption.

      setoid_rewrite Equivalent_List_In_Where.

      (* Full qualification of bfind_matcher needed to avoid apparition of spurious existentials *)
      rewrite (filter_by_equiv dec (@bfind_matcher _ _ _ StorageIsBag (Some n, (None, []))))
        by (
            unfold ObservationalEq; simpl;
            unfold NatTreeBag.KeyFilter;
            unfold NatTreeBag.MoreFacts.BasicProperties.F.eq_dec;
            
            intros;
            rewrite ?andb_true_r, ?andb_true_l;
            intuition
          ).

      setoid_rewrite (@bfind_correct _ _ _ StorageIsBag r_n (Some n, (None, []))).
      setoid_rewrite refine_For_List_Return.
      simplify with monad laws.

      rewrite refine_pick_val by eassumption.
      simplify with monad laws.
      finish honing.
    }    

    (* TODO: s/Decideable/Decidable/ *)
    (* TODO: Use rewrite by instead of [ ... | eassumption ] *)
    (* TODO: Handle the 'projection' parameter differently; 
             right now it appears explicitly in plenty of 
             places, and since it is infered in KeyFilter 
             it makes it possble to swap same-type search terms,
             delaying the failure until the call to bfind_correct *)
    (* TODO: The backtick notation from bounded indexes cannot be input *)
    (* TODO: The insert_always_happens scripts could probably be made more generic *)

    hone method GET_CPU_TIME. {
      unfold equivalence in H.

      setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      setoid_rewrite refineEquiv_pick_pair.
      setoid_rewrite refineEquiv_pick_eq'. 
      simplify with monad laws.
      simpl.

      rewrite (Equivalent_UnConstr_In_EnsembleListEquivalence) by eassumption.

      setoid_rewrite Equivalent_List_In_Where.

      (* Full qualification of bfind_matcher needed to avoid apparition of spurious existentials *)
      rewrite (filter_by_equiv _ (@bfind_matcher _ _ _ StorageIsBag (None, (Some n, [])))) by prove_observational_eq.

      setoid_rewrite (@bfind_correct _ _ _ StorageIsBag r_n (None, (Some n, []))).
      setoid_rewrite refine_For_List_Return.
      simplify with monad laws.

      rewrite refine_pick_val by eassumption.
      simplify with monad laws.
      finish honing.
    }    

    hone method SPAWN. {
      unfold equivalence in H.
      
      setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      setoid_rewrite refineEquiv_pick_pair.
      setoid_rewrite refineEquiv_pick_eq'. 
      simplify with monad laws.
      simpl.
 
      assert (forall tup : Tuple,
                GetUnConstrRelation c PROCESSES tup ->
                S (ccached_value r_n) > tup!PID_COLUMN) 
        by (
            intros;
            rewrite <- (cfresh_cache r_n);
            apply (cached_max_gt_projected (fun (p: Process) => p!PID_COLUMN));
            unfold EnsembleListEquivalence, In in H;               (* TODO: Get rid of this unfold *)
            rewrite <- H; assumption                               (* TODO: What is this spurious GetAttribute? *)
          ).

      rewrite refine_pick_val by eassumption.
      simplify with monad laws.

      rewrite insert_always_happens by eassumption.
      simplify with monad laws.

      rewrite insert_always_happens' by eassumption.
      simplify with monad laws.

      unfold equivalence.

      rewrite (refine_pick_val' 
                 (binsert r_n 
                  <PID_COLUMN :: (S (ccached_value r_n)), 
                  STATE_COLUMN :: SLEEPING, 
                  CPU_COLUMN :: 0>)).

      simplify with monad laws.

      finish honing.

      (* Insert correct *)
      unfold EnsembleListEquivalence in *.

      setoid_rewrite (@binsert_enumerate _ _ _ StorageIsBag _).
      setoid_rewrite get_update_unconstr_iff.
      setoid_rewrite <- H.
      unfold RelationInsert, In in *;
      intuition.
    }

    finish sharpening.
  Defined.
End TreeBasedRefinement.
