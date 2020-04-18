Set Implicit Arguments.

Require Import Bedrock.Platform.Facade.DFModule.
Require Import Bedrock.Platform.Facade.CompileDFacade.
Require Import Bedrock.Platform.Facade.DFacade.

Section ADTValue.

  Variable ADTValue : Type.

  Variable module : DFModule ADTValue.

  Definition compile_func (f : DFFun) : FModule.FFunction := FModule.Build_FFunction (compile_op f) (compiled_syntax_ok f).

  Require Import Bedrock.Platform.Cito.StringMap.
  Import StringMap.
  Require Import Bedrock.Platform.Cito.StringMapFacts.

  Definition compile_to_fmodule : FModule.FModule ADTValue := FModule.Build_FModule (Imports module) (StringMap.map compile_func (Funs module)).

  Require Import Coq.Strings.String.

  Variable name : string.

  Require Import Bedrock.Platform.Cito.NameDecoration.

  Hypothesis good_name : is_good_module_name name = true.

  Require Bedrock.Platform.Facade.CompileModule.

  Definition compile_to_cmodule : CModule.CModule := CompileModule.compile_to_cmodule compile_to_fmodule.

  Definition compile_to_gmodule : GoodModule.GoodModule := CompileModule.compile_to_gmodule compile_to_fmodule name good_name.

End ADTValue.
