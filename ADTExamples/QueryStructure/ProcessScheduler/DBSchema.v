Require Import String Omega List Ensembles. 

Require Export ADTNotation.
Require Export QueryStructureSchema QueryQSSpecs InsertQSSpecs QueryStructure.

Require Export State.

Section ProcessSchedulerInterface.
  Local Open Scope QSSchema.
  Local Open Scope ADTSig_scope.
  Local Open Scope QueryStructureParsing_scope.
  Local Open Scope string_scope.
  Local Open Scope Tuple_scope.

  Definition PID_COLUMN := "pid".
  Definition STATE_COLUMN := "state".
  Definition CPU_COLUMN := "cpu".
  Definition PROCESSES_TABLE := "processes".

  Definition ProcessSchedulerSchema := query structure schema [
    relation PROCESSES_TABLE has schema <PID_COLUMN   : nat,
                                         STATE_COLUMN : State,
                                         CPU_COLUMN   : nat>
    where attributes [CPU_COLUMN; STATE_COLUMN] depend on [PID_COLUMN]
  ] enforcing [].

  Definition PROCESSES := GetRelationKey ProcessSchedulerSchema PROCESSES_TABLE.

  Definition PID   := GetAttributeKey PROCESSES PID_COLUMN.
  Definition STATE := GetAttributeKey PROCESSES STATE_COLUMN.
  Definition CPU   := GetAttributeKey PROCESSES CPU_COLUMN.

  Definition ProcessSchedulerRefRep := 
    @QueryStructure ProcessSchedulerSchema.

  Definition ProcessSchema := 
    QSGetNRelSchemaHeading ProcessSchedulerSchema PROCESSES.

  Definition Process := (Tuple ProcessSchema).

  Definition SPAWN        := "Spawn".
  Definition ENUMERATE    := "Enumerate".
  Definition GET_CPU_TIME := "GetCPUTime".
  Definition COUNT        := "Count".

  Definition ProcessSchedulerSig := ADTsignature {
    SPAWN        : rep × nat     → rep(*,
    "Kill"       : rep × nat     → rep,
    "Suspend"    : rep × nat     → rep,
    "Resume"     : rep × nat     → rep*);
    ENUMERATE    : rep × State   → list nat,
    GET_CPU_TIME : rep × nat     → list nat (*,
    COUNT        : rep × unit    → nat*)
  }.

  Definition ProcessSchedulerSpec : ADT ProcessSchedulerSig := 
    QueryADTRep 
      ProcessSchedulerRefRep {
        def update SPAWN (ns : nat) : rep := (* TODO: pid/0 *)
          Insert <PID_COLUMN: 0, STATE_COLUMN: Sleeping, CPU_COLUMN: 0> into PROCESSES;
          
        def query ENUMERATE (state : State) : list nat :=
          For (p in PROCESSES)
              Where (p!STATE = state)
              Return (p!PID), 

        def query GET_CPU_TIME (id : nat) : list nat :=
          For (p in PROCESSES)
              Where (p!PID = id)
              Return (p!CPU)
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
    forall value (p: Tuple db_schema),
      p column = value <-> beq_A (p column) value = true.
  Proof.
    intros ? ? ? ? beq_iff; split; apply beq_iff.
  Qed.  

  Definition beq_process_iff__state := beq_process_true_iff (A:=State) STATE beq_state_true_iff.

  Definition beq_process_iff__pid   := beq_process_true_iff (A:=nat) PID beq_nat_true_iff.
End ProcessSchedulerLemmas.