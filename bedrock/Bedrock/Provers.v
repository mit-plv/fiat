Require Import Bedrock.Prover Bedrock.Env.
Require Import Bedrock.ILEnv.
Require Bedrock.provers.AssumptionProver.
Require Bedrock.provers.ReflexivityProver.
Require Bedrock.provers.WordProver.
Require Bedrock.provers.ArrayBoundProver.

Set Implicit Arguments.
Set Strict Implicit.

(** * The Combo Prover **)

Definition comboTypes := repr_combine bedrock_types_r sep.Array.types_r.
Definition comboFuncs types' := repr_combine (bedrock_funcs_r (repr comboTypes types'))
  (Array.funcs_r (repr comboTypes types')).

Definition ComboProver : ProverPackage :=
{| ProverTypes := comboTypes
 ; ProverFuncs := comboFuncs
 ; Prover_correct := fun ts fs => composite_ProverT_correct
   (composite_ProverT_correct (provers.AssumptionProver.assumptionProver_correct _)
     (provers.ReflexivityProver.reflexivityProver_correct _))
   (composite_ProverT_correct
     (provers.WordProver.wordProver_correct (types' := repr comboTypes ts) (repr (comboFuncs ts) fs))
     (provers.ArrayBoundProver.boundProver_correct (types' := repr comboTypes ts) (repr (comboFuncs ts) fs)))
|}.
