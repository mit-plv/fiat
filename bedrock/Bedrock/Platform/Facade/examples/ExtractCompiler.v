(** Here's what we run to extract a generic OCaml compiler for Facade programs, linked against the query-structure ADT implementations. *)

Set Implicit Arguments.

Require Import Bedrock.Platform.Facade.examples.QsADTs.
Require Import Bedrock.Platform.Facade.examples.QsRepInv.

Require Import Bedrock.Platform.Facade.DFacadeToBedrock2.

Module Import M := DFacadeToBedrock2.Make QsADTs.Adt QsRepInv.Ri.

Require Import AxSpec.

Require Import DFModule.
Require Import DFacade.

Require Import Bedrock.Platform.Facade.CompileUnit2.
Import CompileOut2Make.

Require Import Bedrock.AMD64_gas.
Require Import Bedrock.Platform.Facade.examples.QsImpl.

Section compiler.
  Variable exports : StringMap.StringMap.t (AxiomaticSpec QsADTs.ADTValue).
  Variable input : CompileUnit exports.

  Definition output := compile input.
  Definition m1 := bedrock_module output.
  Definition m1_ok := bedrock_module_ok output.
  Definition m2 := bedrock_module_impl output.
  Definition m2_ok := bedrock_module_impl_ok output.

  (* link together the two modules contained in CompileOut *)
  Definition all1 := link m1 m2.
  Definition all := link all1 QsImpl.m.

  Definition compiler := moduleS all.
End compiler.

Extraction "facadeCompiler.ml" compiler.
