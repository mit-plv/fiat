Require Import AutoDB.

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
