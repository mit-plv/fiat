Require Import
        CertifiedExtraction.Extraction.External.Core
        CertifiedExtraction.Extraction.External.FacadeLoops.

Ltac compile_loop :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | ([[`?vseq <-- ?seq as _]] :: ?tenv _, [[`?vret <-- (List.fold_left _ ?seq _) as _]] :: ?tenv _) =>
              let vhead := gensym "head" in
              let vtest := gensym "test" in
              apply (FacadeLoops.CompileLoop (vhead := vhead) (vtest := vtest))
            end).
