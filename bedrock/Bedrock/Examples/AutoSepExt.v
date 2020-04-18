Require Import Bedrock.Bedrock.
Export Bedrock.

(** * Specialize the library proof automation to some parameters useful for basic examples. *)

Import TacPackIL.
Require Bedrock.sep.PtsTo.
Require Export Bedrock.sep.Array Bedrock.sep.Locals.
Require Import Bedrock.Provers.

(** Build our memory plugin **)
Module Plugin_PtsTo := Bedrock.sep.PtsTo.BedrockPtsToEvaluator.

Definition TacPackage : Type :=
  @ILAlgoTypes.TypedPackage.

Definition auto_ext' : TacPackage.
  ILAlgoTypes.Tactics.build_prover_pack Provers.ComboProver ltac:(fun a =>
  ILAlgoTypes.Tactics.build_mem_pack Plugin_PtsTo.ptsto32_pack ltac:(fun b =>
  ILAlgoTypes.Tactics.build_mem_pack Bedrock.sep.Array.pack ltac:(fun c =>
  ILAlgoTypes.Tactics.build_mem_pack Bedrock.sep.Locals.pack ltac:(fun d =>
    ILAlgoTypes.Tactics.glue_packs (ILAlgoTypes.BedrockPackage.bedrock_package, a, b, c, d) ltac:(fun res =>
      let res :=
        eval cbv beta iota zeta delta [
          ILAlgoTypes.Env ILAlgoTypes.Algos ILAlgoTypes.Algos_correct
          ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Preds ILAlgoTypes.PACK.Funcs
          ILAlgoTypes.PACK.applyTypes
          ILAlgoTypes.PACK.applyFuncs
          ILAlgoTypes.PACK.applyPreds

          ILAlgoTypes.BedrockPackage.bedrock_package
          Env.repr_combine Env.footprint Env.nil_Repr
          Env.listToRepr
          app map

          ILEnv.bedrock_funcs_r ILEnv.bedrock_types_r
          ILAlgoTypes.AllAlgos_composite
          ILAlgoTypes.oplus Prover.composite_ProverT
          Env.listToRepr

          Plugin_PtsTo.ptsto32_ssig Bedrock.sep.Array.ssig Bedrock.sep.Locals.ssig

          Bedrock.sep.Locals.types_r Bedrock.sep.Locals.funcs_r

          comboTypes comboFuncs
          Bedrock.sep.Array.types_r Bedrock.sep.Array.funcs_r
        ] in res in
        ILAlgoTypes.Tactics.opaque_pack res) || fail 1000 "compose" )))).
Defined.
