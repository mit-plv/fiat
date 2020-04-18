Set Implicit Arguments.

Require Import Bedrock.Platform.Facade.DFacadeToBedrock.
Require Import Bedrock.Platform.Facade.examples.FiatADTs.
Require Import Bedrock.Platform.Facade.examples.FiatRepInv.

Module Import M := DFacadeToBedrock.Make FiatADTs.Adt FiatRepInv.Ri.

Definition pre_cond (arg1 : Value ADTValue) (arg2 : Value ADTValue) := False.
Definition post_cond (arg1 : Value ADTValue) (arg2 : Value ADTValue) (ret : Value ADTValue) := True.

Require Import Bedrock.Platform.Facade.CompileUnit.

Definition imports := GLabelMapFacts.of_list ((("ADT", "sEmpty"), FEnsemble_sEmpty) :: nil).

Definition input : CompileUnit pre_cond post_cond.
  refine (@Build_CompileUnit _ pre_cond post_cond (DFacade.Assign "ret" (Const $0)) eq_refl eq_refl eq_refl imports eq_refl _ _).
  intros.
  unfold pre_cond in *; intuition.
  intros.
  unfold pre_cond in *; intuition.
Defined.

Import CompileOutMake.

Definition output := compile input.
Definition m1 := bedrock_module output.
Definition m1_ok := bedrock_module_ok output.
Definition m2 := bedrock_module_impl output.
Definition m2_ok := bedrock_module_impl_ok output.

(* link together the two modules contained in CompileOut *)
Definition all1 := link m1 m2.

Lemma all1_ok : moduleOk all1.
    link m1_ok m2_ok.
Qed.

Require Import Bedrock.Platform.Facade.examples.FiatImpl.

(* link all1 with the ADT implementation *)
Definition all := link all1 FiatImpl.m.

Theorem all_ok : moduleOk all.
  link all1_ok FiatImpl.ok.
Qed.
