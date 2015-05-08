Require Import Coq.Lists.List
        Coq.Program.Program
        Coq.Arith.Arith.
Require Import
        Fiat.ADT
        Fiat.ADT.ComputationalADT
        Fiat.ADTNotation
        Fiat.ADTRefinement
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.Fiat4Monitors.RADL_Topics
        Fiat.Fiat4Monitors.RADL_Messages
        Fiat.Fiat4Monitors.RADL_Flags
        Fiat.Fiat4Monitors.RADL_Nodes
        Fiat.Fiat4Monitors.MonitorADTs.

Require Import Bedrock.Platform.Facade.DFacade
        Bedrock.Platform.Facade.Notations
        Bedrock.Platform.Cito.ADT
        Bedrock.Platform.Cito.RepInv.

Import Adt.

(* This is a placeholder for a legitimate description of the memory layout. *)
Definition Monitors_rep_inv p (adtvalue : ADTValue) : HProp :=
  match adtvalue with
    | _ => p =?> 1
  end%Sep.

Module Ri <: RepInv Adt.

  Definition RepInv := W -> ADTValue -> HProp.

  Definition rep_inv := Monitors_rep_inv.

  Lemma rep_inv_ptr : forall p a, rep_inv p a ===> p =?> 1 * any.
    destruct a;
    unfold rep_inv, Monitors_rep_inv; simpl;
    sepLemma; apply any_easy.
  Qed.

End Ri.
