Set Implicit Arguments.

Require Import Bedrock.Platform.Facade.FModule.
Require Import Bedrock.Platform.Facade.Compile.
Require Import Bedrock.Platform.Facade.Facade.

Section ADTValue.

  Variable ADTValue : Type.

  Variable module : FModule ADTValue.

  Require Import Bedrock.Platform.Cito.GoodModule.

  Notation FName := SyntaxFunc.Name.
  Notation MName := GoodModule.Name.

  Require Import Bedrock.Platform.Cito.CModule.
  Require Import Bedrock.Platform.Cito.Semantics.

  Definition compile_func (f : FFunction) : CFun := Build_CFun (compile_op f) (syntax_ok f).

  Require Import Bedrock.Platform.Cito.StringMap.
  Import StringMap.
  Require Import Bedrock.Platform.Cito.StringMapFacts.

  Definition compile_to_cmodule : CModule := Build_CModule (StringMap.map compile_func (FModule.Functions module)).

  Require Import Coq.Strings.String.

  Variable name : string.

  Require Import Bedrock.Platform.Cito.NameDecoration.

  Hypothesis good_name : is_good_module_name name = true.

  Require Import Bedrock.Platform.Cito.CModuleFacts.

  Definition compile_to_gmodule : GoodModule.GoodModule := cmodule_to_gmodule name good_name compile_to_cmodule.

End ADTValue.
