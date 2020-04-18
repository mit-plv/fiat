Require Import Bedrock.Platform.Cito.Syntax.

Set Implicit Arguments.

Require Import Bedrock.StringSet.
Import StringSet.
Require Import Coq.FSets.FSetProperties.
Module Import SSP := Properties StringSet.

(* syntactic_requirement *)
Section SynReq.

  Require Import Coq.Strings.String.

  Variable vars : list string.

  Variable temp_size : nat.

  Variable s : Stmt.

  Require Import Bedrock.Platform.Cito.FreeVars.
  Require Import Bedrock.Platform.Cito.Depth.

  Local Open Scope nat.

  Definition in_scope :=
    Subset (free_vars s) (of_list vars) /\
    depth s <= temp_size.

  Require Import Bedrock.Platform.Cito.WellFormed.

  Definition syn_req := in_scope /\ wellformed s.

End SynReq.

Require Import Bedrock.Platform.Cito.ADT.
Require Import Bedrock.Platform.Cito.RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Bedrock.Platform.Cito.Inv.
  Module Import InvMake := Make E.
  Import SemanticsMake.
  Module Import InvMake2 := Make M.

  Section Spec.

    Variable vars : list string.

    Variable temp_size : nat.

    Variable s k : Stmt.

    Variable rv_postcond : W -> vals -> Prop.

    Definition precond := inv vars temp_size rv_postcond (Syntax.Seq s k).

    Definition postcond := inv vars temp_size rv_postcond k.

    Definition imply (pre new_pre: assert) := forall specs x, interp specs (pre x) -> interp specs (new_pre x).

    Definition verifCond pre := imply pre precond :: syn_req vars temp_size (Syntax.Seq s k) :: nil.

  End Spec.

End Make.
