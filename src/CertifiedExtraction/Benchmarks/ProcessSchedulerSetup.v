Require Import Fiat.Examples.QueryStructure.ProcessScheduler.
Require Import Fiat.QueryStructure.Automation.MasterPlan.

Definition RepSpec := Eval simpl in (Rep SchedulerSpec).
Definition RepImpl := Eval simpl in (Rep PartialSchedulerImpl).
Definition SharpenedRepImpl := fst (projT2 SharpenedScheduler).
Opaque SharpenedRepImpl.
Definition AbsR' := AbsR SharpenedRepImpl.

Global Transparent CallBagMethod.
