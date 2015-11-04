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
             ((GLabelMap.add ("list", "delete") (Axiomatic (FacadeImplementationOfDestructor)))
                ((GLabelMap.add ("list", "empty?") (Axiomatic List_empty))
                   (GLabelMap.empty (FuncSpec (list W)))))))).

Example other_test_with_adt'' :
    sigT (fun prog => forall seq: list W, {{ [["arg1" <-- seq as _ ]] :: Nil }}
                                    prog
                                  {{ [["ret" <-- (List.fold_left (@Word.wminus 32) seq 0) as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvLists).
Proof.
  econstructor; intros.
  repeat (compile_step || compile_loop).
  let fop := translate_op Word.wminus in
  apply (CompileBinopOrTest_right_inPlace fop); compile_do_side_conditions.
Defined.

Print Assumptions other_test_with_adt''. (* FIXME *)

Opaque Word.wordToNat.
Opaque Word.natToWord.

Eval compute in (extract_facade other_test_with_adt'').

Eval cbv beta iota zeta delta [extract_facade Fold proj1_sig sig_of_sigT other_test_with_adt'' WrapOpInExpr] in (extract_facade other_test_with_adt'').

Definition fold_comp {TAcc TElem} (f: TAcc -> TElem -> Comp TAcc) seq init :=
  List.fold_left (fun acc elem =>
                    ( acc <- acc;
                      f acc elem )%comp)
                 seq (ret init).

Example other_test_with_adt''' `{FacadeWrapper (Value (list W)) (list W)} f:
    sigT (fun prog => {{ Nil }}
                     prog
                   {{ [[`"ret" <~~  ( seq <- {s: list W | True };
                                    res <- fold_comp f seq (Word.natToWord 32 0: W);
                                    ret res) as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvLists).
Proof.
  econstructor; intros.

  repeat setoid_rewrite SameValues_Fiat_Bind_TelEq.
  eapply ProgOk_Transitivity_Name' with "seq".

  Focus 2.

  Require Import QueryStructure.Specification.Operations.FlattenCompList.
  Check flatten_CompList.

  repeat (compile_step || compile_loop).
  let fop := translate_op Word.wminus in
  apply (CompileBinopOrTest_right_inPlace fop); compile_do_side_conditions.
Defined.


Example other_test_with_adt'' :
    sigT (fun prog => forall seq seq', {{ [["arg1" <-- seq as _ ]] :: [["arg2" <-- seq' as _]] :: Nil }}
                                 prog
                               {{ [["arg1" <-- (rev_append seq seq') as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvW).
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