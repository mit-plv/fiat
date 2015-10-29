Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Examples
        CertifiedExtraction.Extraction.AllInternal
        CertifiedExtraction.Extraction.Extraction.

Definition MyEnvLists :=
  (GLabelMap.add ("std", "rand") (Axiomatic FRandom))
    ((GLabelMap.add ("list", "nil") (Axiomatic (FacadeImplementationOfConstructor nil)))
       ((GLabelMap.add ("list", "push") (Axiomatic (FacadeImplementationOfMutation cons)))
          ((GLabelMap.add ("list", "pop") (Axiomatic List_pop))
             ((GLabelMap.add ("list", "delete") (Axiomatic (FacadeImplementationOfDestructor _)))
                ((GLabelMap.add ("list", "empty?") (Axiomatic List_empty))
                   (GLabelMap.empty _)))))).

Example other_test_with_adt'' :
    sigT (fun prog => forall seq, {{ [["arg1" <-- ADT seq as _ ]] :: Nil }}
                            prog
                          {{ [["ret" <-- SCA _ (List.fold_left (@Word.wplus 32) seq (Word.wordToNat 0)) as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvLists).
Proof.
  econstructor; intros.
  
  eapply CompileSeq with ([["arg1" <-- ADT nil as _]]::[["ret" <-- SCA (list W) (List.fold_left (Word.wplus (sz:=32)) seq (Word.wordToNat 0)) as _]]::Nil).
  let vhead := gensym "head" in
  let vtest := gensym "test" in
  apply (FacadeLoops.CompileLoop (vhead := vhead) (vtest := vtest)); try compile_do_side_conditions.
  compile_step.
  intros;
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  repeat compile_step.
  subst.

  let fop := translate_op Word.wplus in
  apply (CompileBinopOrTest_right_inPlace fop); compile_do_side_conditions.

  unfold MyEnvLists.
  let vtmp := gensym "tmp" in
  let fpointer := find_function_in_env (Axiomatic (@FacadeImplementationOfDestructor (list W))) MyEnvLists in
  apply (CompileCallFacadeImplementationOfDestructor (fpointer := fpointer) (vtmp := vtmp)); try compile_do_side_conditions.
Defined.

Print Assumptions other_test_with_adt''.

Eval cbv beta iota zeta delta [extract_facade Fold proj1_sig sig_of_sigT other_test_with_adt'' WrapOpInExpr] in (extract_facade other_test_with_adt'').

Example other_test_with_adt'' :
    sigT (fun prog => forall seq seq', {{ [["arg1" <-- ADT seq as _ ]] :: [["arg2" <--  ADT seq' as _]] :: Nil }}
                                 prog
                               {{ [["arg1" <-- ADT (rev_append seq seq') as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvW).
Proof.
  econstructor; intros.

  compile_step.
  compile_step.
  compile_step.
  compile_random.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_random.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  

  compile_step.
  Fail fail.
Abort.

