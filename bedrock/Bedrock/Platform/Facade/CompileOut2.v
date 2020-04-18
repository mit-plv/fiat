Set Implicit Arguments.

Require Import ADT RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import StringMap.
  Require Import AxSpec.
  Require Import Bedrock.XCAP.
  Require Import LabelMap.
  Require Import String.
  Require Import LinkSpec.

  Module LinkSpecMake := LinkSpec.Make E.
  Module LinkSpecMake2 := LinkSpecMake.Make M.

  Section TopSection.

    Record CompileOut (exports : StringMap.t (AxiomaticSpec ADTValue)) (ax_mod_name : string) :=
      {
        (* the main exported module to use *)
        bedrock_module : XCAP.module;
        bedrock_module_ok : XCAP.moduleOk bedrock_module;
        bedrock_module_exports : 
          forall x export,
            StringMap.find x exports = Some export ->
            LabelMap.find (ax_mod_name, Labels.Global x) (Exports bedrock_module) = Some (LinkSpecMake2.foreign_func_spec (ax_mod_name, x) export);
        (* this is a module containing the actual code. Just link with this module. Don't need to care about it. *)
        bedrock_module_impl : XCAP.module;
        bedrock_module_impl_ok : XCAP.moduleOk bedrock_module_impl
      }.

  End TopSection.

End Make.