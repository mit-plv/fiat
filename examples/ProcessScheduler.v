Require Import ADTSynthesis.QueryStructure.Refinements.AutoDB.

Section ProcessSchedulerInterface.
  Definition PID := "pid".
  Definition STATE := "state".
  Definition CPU := "cpu".
  Definition PROCESSES_TABLE := "processes".

  Definition State := nat.
  Definition SLEEPING := 0.
  Definition RUNNING  := 1.

  Definition ProcessSchedulerSchema := Query Structure Schema [
    relation PROCESSES_TABLE has schema <PID   :: nat,
                                         STATE :: State,
                                         CPU   :: nat>
    where attributes [CPU; STATE] depend on [PID]
  ] enforcing [].

  Definition SPAWN        := "Spawn".
  Definition ENUMERATE    := "Enumerate".
  Definition GET_CPU_TIME := "GetCPUTime".
  Definition COUNT        := "Count".
  Definition INIT         := "Init".

  Definition ProcessSchedulerSig := ADTsignature {
    INIT         : unit          → rep,
    SPAWN        : rep × unit    → rep × bool,
    ENUMERATE    : rep × State   → rep × list nat,
    GET_CPU_TIME : rep × nat     → rep × list nat,
    COUNT        : rep × unit    → rep × nat
  }.

  Open Scope comp_scope.
  Open Scope Tuple.

  Definition ForAll_In
             qsSchema
             (qs : QueryStructure qsSchema)
             R (bod : Ensemble (@Tuple (QSGetNRelSchemaHeading qsSchema R))) : Prop :=
    forall tup, Ensembles.In _ (GetRelation qs R) tup ->
                bod tup.

  Notation "∀ x '∈' R ',' bod" :=
    (ForAll_In qsHint R (fun x => bod))
      (bod at level 11, at level 10)
    : QuerySpec_scope.

  Arguments ForAll_In _ _ _ _ / .

  Definition ProcessSchedulerSpec : ADT ProcessSchedulerSig :=
    QueryADTRep
      ProcessSchedulerSchema {
        const INIT (_ : unit) : rep := empty,

        update SPAWN (_ : unit) : bool :=
          new_pid <- {n | ∀ p ∈ ``(PROCESSES_TABLE), (n <> p!PID)};
          Insert <PID:: new_pid, STATE:: SLEEPING, CPU:: 0> into PROCESSES_TABLE,

        query ENUMERATE (state : State) : list nat :=
          For (p in PROCESSES_TABLE)
              Where (p!STATE = state)
              Return (p!PID),

        query GET_CPU_TIME (id : nat) : list nat :=
          For (p in PROCESSES_TABLE)
              Where (p!PID = id)
              Return (p!CPU),

        query COUNT (_ : unit) : nat :=
          Count (For (p in PROCESSES_TABLE)
                 Return 1)
      }.
End ProcessSchedulerInterface.

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
