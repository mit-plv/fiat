Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation BuildADTRefinements
        QueryStructureSchema QueryStructure
        QueryQSSpecs InsertQSSpecs EmptyQSSpecs
        GeneralInsertRefinements GeneralQueryRefinements
        GeneralQueryStructureRefinements
        ListQueryRefinements ListInsertRefinements
        ListQueryStructureRefinements.

Require Import BagsOfTuples CachingBags Bool.
Require Import DBSchema AdditionalLemmas.
Require Export ADTRefinement.BuildADTRefinements.

Unset Implicit Arguments.

Definition StatePIDIndexedTree : @BagPlusBagProof Process.
  mkIndex ProcessSchema [STATE; PID].
Defined.

Definition Storage := AddCachingLayer (BagProof StatePIDIndexedTree)
                                      (fun p => p PID)
                                      0 eq _ max ListMax_cacheable.

Definition StorageType           := BagType Storage.
Definition StorageIsBag          := BagProof Storage.
Definition StorageSearchTermType := SearchTermType Storage.

Section TreeBasedRefinement.
  Open Scope type_scope.
  Open Scope Tuple_scope.

  Notation "x '∈' y" := (In _ y x) (at level 50, no associativity).

  Opaque Query_For.

  Definition equivalence (set_db: UnConstrQueryStructure ProcessSchedulerSchema) (db: StorageType) :=
    EnsembleIndexedListEquivalence (GetUnConstrRelation set_db PROCESSES) (benumerate db).

  Lemma NeatScheduler :
    Sharpened ProcessSchedulerSpec.
  Proof.
    unfold ProcessSchedulerSpec.

    unfold ForAll_In; start honing QueryStructure.

    hone representation using equivalence.

    hone constructor INIT. {
      unfold equivalence.

      repeat setoid_rewrite refineEquiv_pick_ex_computes_to_and;
      repeat setoid_rewrite refineEquiv_pick_eq';
      simplify with monad laws.

      rewrite (refine_pick_val' bempty) by intuition (apply EnsembleIndexedListEquivalence_Empty).
      subst_body; higher_order_1_reflexivity.
    }

    hone method ENUMERATE. {
      unfold equivalence in H.

      setoid_rewrite refineEquiv_pick_ex_computes_to_and;
      setoid_rewrite refineEquiv_pick_pair;
      setoid_rewrite refineEquiv_pick_eq';
      simplify with monad laws; cbv beta;
      simpl.

      rewrite refine_List_Query_In by eassumption.
      rewrite refine_List_Query_In_Where; instantiate (1 := _).
      rewrite refine_List_For_Query_In_Return_Permutation.

      rewrite filter over Storage using search term 
                (Some n, (@None nat, @nil (TSearchTermMatcher ProcessSchema))).

      setoid_rewrite (bfind_correct _).
      setoid_rewrite refine_Permutation_Reflexivity.
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

    hone method GET_CPU_TIME. {
      unfold equivalence in H.

      setoid_rewrite refineEquiv_pick_ex_computes_to_and;
      setoid_rewrite refineEquiv_pick_pair;
      setoid_rewrite refineEquiv_pick_eq';
      simplify with monad laws; cbv beta;
      simpl.

      rewrite refine_List_Query_In; eauto.
      rewrite refine_List_Query_In_Where; instantiate (1 := _).
      rewrite refine_List_For_Query_In_Return_Permutation.

      rewrite filter over Storage using search term 
                (@None nat, (Some n, @nil (TSearchTermMatcher ProcessSchema))). 

      setoid_rewrite (bfind_correct _).
      setoid_rewrite refine_Permutation_Reflexivity.
      simplify with monad laws.

      rewrite refine_pick_val by eassumption.
      simplify with monad laws.
      finish honing.
    }

    hone method SPAWN. {
      unfold equivalence in H.

      lift list property (assert_cache_property (cfresh_cache r_n) max_cached_neq_projected _) as cache.
    
      setoid_rewrite refineEquiv_pick_ex_computes_to_and;
      setoid_rewrite refineEquiv_pick_pair;
      setoid_rewrite refineEquiv_pick_eq';
      simplify with monad laws; cbv beta;
      simpl.

      rewrite refine_pick_val by eassumption.
      simplify with monad laws.
 
      rewrite refine_pick_val by eauto using EnsembleIndexedListEquivalence_pick_new_index.
      simplify with monad laws.

      rewrite refine_tupleAgree_refl_True.
      simplify with monad laws.

      rewrite (refine_pick_val' true) by prove trivial constraints.
      simplify with monad laws.

      rewrite (refine_pick_val' true) by prove trivial constraints.
      simplify with monad laws.

      rewrite refine_pick_val by (apply binsert_correct_DB; eauto).
      simplify with monad laws.

      finish honing.
    }

    finish sharpening.
  Defined.
End TreeBasedRefinement.
