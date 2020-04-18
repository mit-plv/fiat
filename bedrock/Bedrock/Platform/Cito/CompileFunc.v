Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.ADT.
Require Import Bedrock.Platform.Cito.RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Bedrock.Platform.Cito.CompileFuncImpl.
  Module Import CompileFuncImplMake := Make E M.
  Import CompileFuncSpecMake.
  Require Import Bedrock.Platform.Cito.GoodOptimizer.
  Import GoodOptimizerMake.

  Require Import Bedrock.Platform.Cito.GoodFunc.

  Require Import Bedrock.Platform.Cito.SyntaxFunc.
  Require Import Coq.Strings.String.

  Section TopSection.

    Variable module_name : string.

    Variable func : Func.

    Hypothesis good_func : GoodFunc func.

    Variable optimizer : Optimizer.

    Hypothesis good_optimizer : GoodOptimizer optimizer.

    Definition body := body func module_name good_func good_optimizer.

    Require Import Bedrock.Platform.Cito.CompileFuncSpec.
    Require Import Bedrock.StructuredModule.
    Definition compile : function module_name :=
      (Name func, CompileFuncSpecMake.spec func, body).

  End TopSection.

End Make.
