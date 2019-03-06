Require Import
        CertifiedExtraction.Extraction.Core
        CertifiedExtraction.Extraction.Conditionals.

Ltac is_comp c :=
  match type of c with
  | @Comp _ => idtac
  | _ => fail 1
  end.

Ltac compile_if t tp fp :=
  is_comp tp; is_comp fp;
  let test_var := gensym "test" in
  apply (CompileIf _ (tmp := test_var)).
