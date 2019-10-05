Require Import Narcissus.Examples.Guard.StatefulGuard.
Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import Narcissus.Examples.Guard.Core.
Require Import Narcissus.OCamlExtraction.Extraction.

Open Scope string_scope.

Notation simp x :=
  ltac:(let x := (eval red in x) in
        let x := (eval cbn in x) in
        exact x).

Definition guard_init : ComputationalADT.cRep GuardImpl :=
  simp (CallConstructor GuardImpl "Init").

Definition guard_process_packet (bs: bytes) (chain: IPTables.chain) (rep: ComputationalADT.cRep GuardImpl) : (_ * option result) :=
  match IPTables.input_of_bytes chain bs with
  | Some input => simp (CallMethod GuardImpl "Filter" rep input)
  | None => (rep, Some DROP)
  end.

Extraction "guard.ml" guard_init guard_process_packet.
