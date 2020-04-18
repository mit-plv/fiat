Set Implicit Arguments.

Require Import Bedrock.Platform.Facade.CompileUnit.
Require Import Bedrock.Platform.Cito.StringMap Bedrock.Platform.Cito.WordMap Bedrock.Platform.Cito.GLabelMap Coq.Strings.String Coq.Lists.List.
Local Open Scope string_scope.

(* the exported Bedrock function and its spec is [export_module_name!fun_name@compileS] *)
Notation export_module_name := "export".
(* Be careful about extra_stack! Setting it too large (e.g. 200) will greatly slow compilation, while setting it too small (e.g. 10) will cause run-time stack overflow *)
(* Notation extra_stack := 200. *)
Notation extra_stack := 10.

Require Import Bedrock.Platform.Cito.ADT Bedrock.Platform.Cito.RepInv.
Module Make (Import E : ADT) (Import M : RepInv E).
  Require Import Bedrock.Platform.Cito.Inv Bedrock.Platform.Malloc.
  Module Import InvMake := Make E.
  Module Import InvMake2 := Make M.
  Require Import Bedrock.Platform.Cito.Semantics.
  Require Import Bedrock.Platform.Cito.SemanticsUtil.

  Section TopSection.

    (* pre_cond arg1 arg2 *)
    Variable pre_cond : Value ADTValue -> Value ADTValue -> Prop.
    (* post_cond arg1 arg2 ret *)
    Variable post_cond : Value ADTValue -> Value ADTValue -> Value ADTValue -> Prop.

    Definition compileS := SPEC(argvar1, argvar2) reserving (6 + extra_stack)%nat
      Al v1, Al v2, Al h,
      PRE[V] is_heap h * [| pre_cond v1 v2 /\ let pairs := (V argvar1, v1) :: (V argvar2, v2) :: nil in disjoint_ptrs pairs /\ good_scalars pairs /\ WordMap.Equal h (make_heap pairs) |] * mallocHeap 0
      POST[R] Ex h', is_heap h' * [| exists r, post_cond v1 v2 r /\ let pairs := (R, r) :: nil in good_scalars pairs /\ WordMap.Equal h' (make_heap pairs) |] * mallocHeap 0.

    Require Import Bedrock.LabelMap.

    Record CompileOut :=
      {
        (* the main exported module to use *)
        bedrock_module : XCAP.module;
        bedrock_module_ok : XCAP.moduleOk bedrock_module;
        bedrock_module_export : LabelMap.find (export_module_name, Labels.Global fun_name) (Exports bedrock_module) = Some (Precondition compileS None);
        (* this is a module containing the actual code. Just link with this module. Don't need to care about it. *)
        bedrock_module_impl : XCAP.module;
        bedrock_module_impl_ok : XCAP.moduleOk bedrock_module_impl
      }.

  End TopSection.

End Make.
