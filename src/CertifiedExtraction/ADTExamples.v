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

  let vhead := gensym "head" in
  let vtest := gensym "test" in
  apply (FacadeLoops.CompileLoop (vhead := vhead) (vtest := vtest)); try compile_do_side_conditions.
  compile_step.
  intros.

  Lemma ProgOk_Transitivity_Cons_B :
    forall {av} env ext t1 t1' t2 prog1 prog2 k (v: Comp (Value av)),
      {{ t1 }}                            prog1     {{ [[Some k <~~ v as kk]] :: t1' kk }}     ∪ {{ ext }} // env ->
      {{ [[Some k <~~ v as kk]] :: t1' kk }} prog2     {{ [[Some k <~~ v as kk]] :: t2 kk }} ∪ {{ ext }} // env ->
      {{ t1 }}                      Seq prog1 prog2 {{ [[Some k <~~ v as kk]] :: t2 kk }} ∪ {{ ext }} // env.
  Proof.
    eauto using CompileSeq.
  Qed.

  (* This is a well-behaved version of ProgOk_Transitivity_Cons, but it is not
     very useful, as the side goal that it creates are in a form in which one
     would want to apply transitivity again. *)
  Lemma ProgOk_Transitivity_Cons_Drop :
    forall {av} env ext t1 t2 prog1 prog2 k (v: Comp (Value av)),
      {{ t1 }}                     prog1      {{ [[Some k <~~ v as _]]::(DropName k t1) }}     ∪ {{ ext }} // env ->
      {{ [[Some k <~~ v as _]]::(DropName k t1) }}      prog2      {{ [[Some k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
      {{ t1 }}                Seq prog1 prog2 {{ [[Some k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env.
  Proof.
    SameValues_Facade_t.
  Qed.

  (* eapply ProgOk_Transitivity_Cons_B. *)
  (* rewrite TelEq_swap; try compile_do_side_conditions. *)
  (* apply CompileSkip. *)
  (* compile_step. *)
  (* compile_step. *)
  
  compile_step.

  repeat compile_step.

  subst.

  let fop := translate_op Word.wplus in
  apply (CompileBinopOrTest_right_inPlace fop); compile_do_side_conditions.
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

