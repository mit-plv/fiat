Require Import AutoDB.

Require Import Bags BagsOfTuples CachingBags Bool.
Require Import DBSchema AdditionalLemmas AdditionalRefinementLemmas.
Require Export ADTRefinement.BuildADTRefinements.

Unset Implicit Arguments.

Definition Processes := GetRelationKey ProcessSchedulerSchema PROCESSES_TABLE. 
Definition ProcessHeading := QSGetNRelSchemaHeading ProcessSchedulerSchema Processes.

Definition StatePIDIndexedTree : @BagPlusBagProof (@Tuple ProcessHeading).
  mkIndex ProcessHeading [ProcessHeading/STATE; ProcessHeading/PID].
Defined.

Definition Storage := AddCachingLayer (BagProof StatePIDIndexedTree)
                                      (fun p => p!PID)
                                      0 eq _ max ListMax_cacheable.

Definition StorageType           := BagType Storage.
Definition StorageIsBag          := BagProof Storage.
Definition StorageSearchTermType := SearchTermType Storage.

Section TreeBasedRefinement.
  Definition ProcessScheduler_AbsR
             (or : UnConstrQueryStructure ProcessSchedulerSchema)
             (nr : StorageType) :=
    EnsembleIndexedListEquivalence (or!PROCESSES_TABLE)%QueryImpl
                                   (benumerate nr).

  Lemma NeatScheduler :
    Sharpened ProcessSchedulerSpec.
  Proof.
    unfold ProcessSchedulerSpec.

    unfold ForAll_In; start honing QueryStructure.
    hone representation using ProcessScheduler_AbsR.

    hone constructor INIT. {
      unfold ProcessScheduler_AbsR in *.
      simplify with monad laws.

      rewrite (refine_pick_val' bempty) by (intuition; apply bempty_correct_DB).
      subst_body; higher_order_1_reflexivity.
    }

    hone method ENUMERATE. {
      unfold ProcessScheduler_AbsR in *.
      simplify with monad laws.

      concretize.
      rewrite filter over Storage using search term
                (Some n, (@None nat, @nil (TSearchTermMatcher ProcessHeading))).
      setoid_rewrite (bfind_correct _).
      commit.

      choose_db ProcessScheduler_AbsR.
      finish honing.
    }

    hone method GET_CPU_TIME. {
      unfold ProcessScheduler_AbsR in *.
      simplify with monad laws.

      concretize.
      rewrite filter over Storage using search term
                (@None nat, (Some n, @nil (TSearchTermMatcher ProcessHeading))).
      setoid_rewrite (bfind_correct _).
      commit.
      
      choose_db ProcessScheduler_AbsR.
      finish honing.
    }

    hone method SPAWN. {
      unfold ProcessScheduler_AbsR in *;
      simplify with monad laws.

      lift list property (assert_cache_property (cfresh_cache r_n) 
                                                max_cached_neq_projected _) as cache.

      rewrite refine_pick_val by eassumption;
        simplify with monad laws.

      pruneDuplicates.
      pickIndex.

      rewrite (refine_pick_val' true) by prove trivial constraints;
        simplify with monad laws.

      rewrite refine_pick_val by binsert_correct_DB;
        simplify with monad laws; simpl.

      finish honing.
    }
 
    hone method COUNT. {
      unfold ProcessScheduler_AbsR in *.
      simplify with monad laws.

      concretize.
      rewrite <- (bfind_star _).
      commit.

      rewrite refine_pick_val by eassumption.
      finish honing.
    }

    finish sharpening.
  Defined.
End TreeBasedRefinement.
