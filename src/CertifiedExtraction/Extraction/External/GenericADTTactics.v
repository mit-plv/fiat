Require Import
        CertifiedExtraction.Extraction.External.Core
        CertifiedExtraction.Extraction.External.GenericADTMethods.

Ltac compile_mutation_alloc :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       match constr:(pre, post) with
                       | (?tenv, Cons ?s (ret (ADT (?f _ _))) (fun _ => ?tenv)) =>
                         let fpointer := find_function_in_env
                                          (Axiomatic (FacadeImplementationOfMutation f)) env in
                         let arg := gensym "arg" in
                         let tmp := gensym "tmp" in
                         apply (CompileCallFacadeImplementationOfMutation_Alloc
                                  (fpointer := fpointer) (varg := arg) (vtmp := (DummyArgument tmp)))
                       end).

Ltac compile_mutation_replace :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       match constr:(pre, post) with
                       | ([[?s <-- ADT ?adt as _]] :: ?tenv, [[?s <-- ADT (?f _ ?adt) as _]] :: ?tenv) =>
                         let fpointer := find_function_in_env
                                          (Axiomatic (FacadeImplementationOfMutation f)) env in
                         let arg := gensym "arg" in
                         let tmp := gensym "tmp" in
                         apply (CompileCallFacadeImplementationOfMutation_Replace
                                  (fpointer := fpointer) (varg := arg) (vtmp := (DummyArgument tmp)))
                       end).

Ltac compile_constructor :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       match constr:(pre, post) with
                       | (?tenv, Cons ?s (ret (ADT ?adt)) (fun _ => ?tenv)) =>
                         let fpointer := find_function_in_env
                                          (Axiomatic (FacadeImplementationOfConstructor adt)) env in
                         apply (CompileCallFacadeImplementationOfConstructor
                                  tenv (fpointer := fpointer))
                       end).
