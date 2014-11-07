Require Import StringMap.
Require Import Memory.
Require Import Facade.FacadeADTs.
Require Import FiatToFacade.FacadeNotations.
Require Import FiatToFacade.Prog FiatToFacade.StringMapNotations.

Definition SCALoopBodyProgCondition
           env loop compiled_loop knowledge scas adts
           (vseq vret thead tis_empty: StringMap.key) (acc head: W) (seq: list W) :=
  @ProgOk _ env compiled_loop knowledge
          ([thead >sca> head]::[tis_empty >sca> 0]::[vret >sca> acc]::scas)
          ([vret >sca> loop acc head]::scas)
          ([vseq >adt> List seq]::adts)
          ([vseq >adt> List seq]::adts).
          
Definition SCALoopBodyOk
           env loop compiled_loop knowledge scas adts
           (vseq vret thead tis_empty: StringMap.key) :=
  forall (acc: W) (head: W) (seq: list W),
    SCALoopBodyProgCondition env loop compiled_loop knowledge scas adts vseq
                             vret thead tis_empty acc head seq.

Definition ADTLoopBodyProgCondition
           env {acc_type} loop compiled_loop knowledge scas adts
           (vseq vret thead tis_empty: StringMap.key) (acc: acc_type) wrapper (head: W) (seq: list W) :=
  @ProgOk _ env compiled_loop knowledge
          ([thead >sca> head]::[tis_empty >sca> 0]::scas)
          (scas)
          ([vret >adt> wrapper acc]::[vseq >adt> List seq]::adts)
          ([vret >adt> wrapper (loop acc head)]::[vseq >adt> List seq]::adts).

Definition ADTLoopBodyOk
           env {acc_type} loop compiled_loop knowledge scas adts
           (vseq vret thead tis_empty: StringMap.key) wrapper :=
  forall acc (head: W) (seq: list W),
    @ADTLoopBodyProgCondition env acc_type loop compiled_loop knowledge scas adts vseq
                              vret thead tis_empty acc wrapper head seq.
