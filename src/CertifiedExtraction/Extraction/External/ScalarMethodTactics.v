Require Import
        CertifiedExtraction.Extraction.Core
        CertifiedExtraction.Extraction.External.ScalarMethods
        CertifiedExtraction.Extraction.External.GenericMethods.

Ltac compile_external_call_SCA av env fWW arg ext :=
  let fpointer := find_function_in_env (Axiomatic (FacadeImplementationWW av fWW)) env in
  let varg := find_fast arg ext in
  match varg with
  | Some ?varg =>
    apply (CompileCallFacadeImplementationWW (fpointer := fpointer) (varg := varg))
  | None =>
    let varg := gensym "arg" in
    apply (CompileCallFacadeImplementationWW_full (fpointer := fpointer) (varg := varg))
  end.
