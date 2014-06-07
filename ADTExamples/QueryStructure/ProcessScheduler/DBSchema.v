Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation QueryStructureSchema
        BuildADTRefinements QueryQSSpecs InsertQSSpecs EmptyQSSpecs
        QueryStructure GeneralInsertRefinements ListInsertRefinements
        GeneralQueryRefinements ListQueryRefinements
        ProcessScheduler.AdditionalLemmas.

(* TODO: Reactivate? *)
(*Notation "x '∈' y" := (In _ y x) (at level 50, no associativity) *)

Section ProcessSchedulerInterface.
  Require Import QueryStructureNotations.

  Definition PID_COLUMN := "pid".
  Definition STATE_COLUMN := "state".
  Definition CPU_COLUMN := "cpu".
  Definition PROCESSES_TABLE := "processes".

  Definition State := nat.
  Definition SLEEPING := 0.
  Definition RUNNING  := 1.

  Definition ProcessSchedulerSchema := Query Structure Schema [
    relation PROCESSES_TABLE has schema <PID_COLUMN   :: nat,
                                         STATE_COLUMN :: State,
                                         CPU_COLUMN   :: nat>
    where attributes [CPU_COLUMN; STATE_COLUMN] depend on [PID_COLUMN]
  ] enforcing [].

  Definition PROCESSES := GetRelationKey ProcessSchedulerSchema PROCESSES_TABLE.

  Definition PID   := GetAttributeKey PROCESSES PID_COLUMN.
  Definition STATE := GetAttributeKey PROCESSES STATE_COLUMN.
  Definition CPU   := GetAttributeKey PROCESSES CPU_COLUMN.

  Definition ProcessSchema :=
    QSGetNRelSchemaHeading ProcessSchedulerSchema PROCESSES.

  Definition Process := (@Tuple ProcessSchema).

  Definition SPAWN        := "Spawn".
  Definition ENUMERATE    := "Enumerate".
  Definition GET_CPU_TIME := "GetCPUTime".
  Definition COUNT        := "Count".
  Definition INIT         := "Init".

  Definition ProcessSchedulerSig := ADTsignature {
    INIT         : unit          → rep ,
    SPAWN        : rep × nat     → rep × (), 
    ENUMERATE    : rep × State   → rep × list nat,
    GET_CPU_TIME : rep × nat     → rep ×list nat 
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

        update SPAWN (ns : nat) : unit :=
          new_pid <- {n | ∀ p ∈ PROCESSES, (n > p!PID_COLUMN)};
          Insert <PID_COLUMN:: new_pid, STATE_COLUMN:: SLEEPING, CPU_COLUMN:: 0> into PROCESSES_TABLE,

        query ENUMERATE (state : State) : list nat :=
          For (p in PROCESSES_TABLE)
              Where (p STATE = state)
              Return (p!PID_COLUMN),

        query GET_CPU_TIME (id : nat) : list nat :=
          For (p in PROCESSES_TABLE)
              Where (p!PID_COLUMN = id)
              Return (p!CPU_COLUMN)
(*,

        def query COUNT (_: unit) : nat :=
          Count (For (p in PROCESSES_TABLE)
                 Return 1)*)
      }.
End ProcessSchedulerInterface.

Section ProcessSchedulerLemmas.
  Lemma beq_process_true_iff :
    forall { A: Type } (db_schema: Heading) (column: Attributes db_schema)
           { beq_A: Domain db_schema column -> Domain db_schema column -> bool },
    forall (beq_iff : forall a b, beq_A a b = true <-> a = b),
    forall value (p: @Tuple db_schema),
      p column = value <-> beq_A (p column) value = true.
  Proof.
    intros ? ? ? ? beq_iff; split; apply beq_iff.
  Qed.

  (* TODO: Is this needed? *)
  Definition beq_process_iff__pid   := beq_process_true_iff (A:=nat) PID beq_nat_true_iff.
End ProcessSchedulerLemmas.
