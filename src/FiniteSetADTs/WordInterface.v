Require Export Fiat.Common.Coq__8_4__8_5__Compat.
(** Before we integrated bedrock, we used a dummy implementation of
    this module using [nat]; see NatWord.v. *)
Require Import Coq.Classes.Morphisms.

Set Implicit Arguments.
Global Set Asymmetric Patterns.

Module Type BedrockWordT.
  Axiom W : Type.
  Axiom wzero : W.
  Axiom wplus : W -> W -> W.
  Axiom wminus : W -> W -> W.
  Axiom weq : W -> W -> bool.
  Axiom wlt : W -> W -> bool.
  Axiom weq_iff : forall x y, x = y <-> weq x y = true.
  Axiom wlt_irrefl : forall x, wlt x x = false.
  Axiom wlt_trans : forall x y z, wlt x y = true -> wlt y z = true -> wlt x z = true.
  Axiom wle_antisym : forall x y, wlt x y = false -> wlt y x = false -> x = y.
  Axiom wle_asym : forall x y, wlt x y = true -> wlt y x = false.
  Axiom from_nat : nat -> W.
End BedrockWordT.
