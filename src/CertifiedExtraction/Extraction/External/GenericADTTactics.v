Require Import
        CertifiedExtraction.Extraction.External.Core
        CertifiedExtraction.Extraction.External.GenericADTMethods.

Ltac ensure_all_pointers_found :=
  (* FIXME use instead of explicitly finding pointers *)
  match goal with
  | |- GLabelMap.MapsTo ?ptr _ _ => is_evar ptr; first [solve [GLabelMapUtils.decide_mapsto_maybe_instantiate] | fail 2]
  | _ => idtac
  end.

Ltac compile_mutation_alloc :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       match constr:(pre, post) with
                       | (?tenv, Cons ?s (ret (?f _ _)) (fun _ => ?tenv)) =>
                         let arg := gensym "arg" in
                         let tmp := gensym "tmp" in
                         let av := av_from_ext ext in
                         match type of f with
                         | ?a -> ?b -> ?b => (* FIXME just try to apply both lemmas *)
                           let pr := constr:(eq_refl a : a = W) in
                           let fpointer := find_function_pattern_in_env
                                            (fun w => (Axiomatic (FacadeImplementationOfMutation_SCA (av := av) _ (H := w) f))) env in
                           apply (CompileCallFacadeImplementationOfMutation_SCA_Alloc
                                    (fpointer := fpointer) (varg := arg) (vtmp := (DummyArgument tmp)))
                         | ?a -> ?b -> ?b =>
                           apply (CompileCallFacadeImplementationOfMutation_ADT_Alloc (varg := arg) (vtmp := (DummyArgument tmp)));
                             ensure_all_pointers_found
                         end
                       end).

Ltac compile_mutation_replace :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       let av := av_from_ext ext in
                       let arg := gensym "arg" in
                       let tmp := gensym "tmp" in
                       match constr:(pre, post) with
                       | ([[?s <-- ?adt as _]] :: ?tenv, [[?s <-- (?f _ ?adt) as _]] :: ?tenv) =>
                         match type of f with
                         | ?a -> ?b -> ?b => (* FIXME just try to apply both lemmas *)
                           let fpointer := find_function_pattern_in_env
                                            (fun w => Axiomatic (FacadeImplementationOfMutation_SCA (av := av) _ (H := w) f)) env in
                           apply (CompileCallFacadeImplementationOfMutation_SCA_Replace
                                    (fpointer := fpointer) (varg := arg) (vtmp := (DummyArgument tmp)))
                         | ?a -> ?b -> ?b =>
                           apply (CompileCallFacadeImplementationOfMutation_ADT_Replace (varg := arg) (vtmp := (DummyArgument tmp)));
                             ensure_all_pointers_found
                         end
                       end).

Ltac compile_constructor :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       match constr:(pre, post) with
                       | (?tenv, Cons ?s (ret ?adt) (fun _ => ?tenv)) =>
                         let av := av_from_ext ext in
                         let fpointer := find_function_pattern_in_env
                                          (fun w => (Axiomatic (FacadeImplementationOfConstructor
                                                               (av := av) _ (H := w) adt))) env in
                         apply (CompileCallFacadeImplementationOfConstructor
                                  tenv (fpointer := fpointer))
                       end).
