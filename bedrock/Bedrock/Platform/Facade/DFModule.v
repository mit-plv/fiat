Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.StringMap.
Import StringMap.

Require Import Bedrock.Platform.Facade.FModule.
Require Import Bedrock.Platform.Facade.DFacade.
Require Import Bedrock.Platform.Facade.CompileDFacade.

Local Notation FunCore := OperationalSpec.

Record DFFun :=
  {
    Core : FunCore;
    compiled_syntax_ok : FModule.is_syntax_ok (compile_op Core) = true
  }.

Coercion Core : DFFun >-> OperationalSpec.

Section ADTValue.

  Variable ADTValue : Type.

  Notation AxiomaticSpec := (@AxiomaticSpec ADTValue).

  Require Import Bedrock.Platform.Cito.GLabelMap.

  Record DFModule :=
    {
      Imports : GLabelMap.t AxiomaticSpec;
      (* Exports : StringMap.t AxiomaticSpec; *)
      Funs : StringMap.t DFFun;
      import_module_names_good : 
        let imported_module_names := List.map (fun x => fst (fst x)) (GLabelMap.elements Imports) in
        List.forallb Cito.NameDecoration.is_good_module_name imported_module_names = true
    }.

End ADTValue.
