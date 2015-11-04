Require Import
        CertifiedExtraction.Extraction.External.Core
        CertifiedExtraction.Extraction.External.GenericADTMethods.

Ltac compile_mutation_alloc :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       match constr:(pre, post) with
                       | (?tenv, Cons ?s (ret (?f _ _)) (fun _ => ?tenv)) =>
                         let av := av_from_ext ext in
                         let fpointer := find_function_pattern_in_env
                                          (fun w => (Axiomatic (FacadeImplementationOfMutation (av := av) (H := w) f))) env in
                         let arg := gensym "arg" in
                         let tmp := gensym "tmp" in
                         apply (CompileCallFacadeImplementationOfMutation_Alloc
                                  (fpointer := fpointer) (varg := arg) (vtmp := (DummyArgument tmp)))
                       end).

Ltac compile_mutation_replace :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       match constr:(pre, post) with
                       | ([[?s <-- ?adt as _]] :: ?tenv, [[?s <-- (?f _ ?adt) as _]] :: ?tenv) =>
                         let av := av_from_ext ext in
                         let fpointer := find_function_pattern_in_env
                                          (fun w => Axiomatic (FacadeImplementationOfMutation (av := av) (H := w) f)) env in
                         let arg := gensym "arg" in
                         let tmp := gensym "tmp" in
                         apply (CompileCallFacadeImplementationOfMutation_Replace
                                  (fpointer := fpointer) (varg := arg) (vtmp := (DummyArgument tmp)))
                       end).

Ltac compile_constructor :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       match constr:(pre, post) with
                       | (?tenv, Cons ?s (ret ?adt) (fun _ => ?tenv)) =>
                         let av := av_from_ext ext in
                         let fpointer := find_function_pattern_in_env
                                          (fun w => (Axiomatic (FacadeImplementationOfConstructor
                                                               (av := av) (H := w) adt))) env in
                         apply (CompileCallFacadeImplementationOfConstructor
                                  tenv (fpointer := fpointer))
                       end).
