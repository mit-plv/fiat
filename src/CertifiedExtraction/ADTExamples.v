Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Examples
        CertifiedExtraction.Extraction.AllInternal
        CertifiedExtraction.Extraction.Extraction.

Definition MyEnvLists `{FacadeWrapper av (list W)} : Env av :=
  (GLabelMap.add ("std", "rand") (Axiomatic FRandom))
    ((GLabelMap.add ("list", "nil") (Axiomatic (FacadeImplementationOfConstructor nil)))
       ((GLabelMap.add ("list", "push") (Axiomatic (FacadeImplementationOfMutation cons)))
          ((GLabelMap.add ("list", "pop") (Axiomatic List_pop))
             ((GLabelMap.add ("list", "delete") (Axiomatic (FacadeImplementationOfDestructor)))
                ((GLabelMap.add ("list", "empty?") (Axiomatic List_empty))
                   (GLabelMap.empty (FuncSpec _))))))).

Example other_test_with_adt'' `{FacadeWrapper av (list W)}:
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

Definition fold_comp {TAcc TElem} (f: Comp TAcc -> TElem -> Comp TAcc) seq init :=
  List.fold_left (fun (acc: Comp TAcc) (elem: TElem) =>
                    ( f acc elem )%comp)
                 seq init.

Require Import
        CertifiedExtraction.Extraction.AllInternal
        CertifiedExtraction.Extraction.External.Core
        CertifiedExtraction.Extraction.External.Loops
        CertifiedExtraction.Extraction.External.GenericADTMethods
        CertifiedExtraction.Extraction.External.FacadeADTs.

(* Opaque WrapInstance.            (* FIXME simpl never? *) *)

Lemma CompileLoop :
  forall `{FacadeWrapper av (list W)}
    lst init vhead vtest vlst vret fpop fempty fdealloc facadeInit facadeBody env (ext: StringMap.t (Value av)) tenv (f: Comp W -> W -> Comp W),
    GLabelMap.MapsTo fpop (Axiomatic List_pop) env ->
    GLabelMap.MapsTo fempty (Axiomatic List_empty) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (A := list W))) env ->
    vtest ∉ ext ->
    NotInTelescope vtest tenv ->
    vlst ∉ ext ->
    NotInTelescope vlst tenv ->
    vret ∉ ext ->
    NotInTelescope vret tenv ->
    vhead ∉ ext ->
    NotInTelescope vhead tenv ->
    vtest <> vret ->
    vtest <> vlst ->
    vtest <> vhead ->
    vret <> vlst ->
    vret <> vhead ->
    vlst <> vhead ->
    {{ [[`vlst <~~ lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <~~ init as _]] :: [[`vlst <~~ lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    (forall head (acc: Comp W) (s: Comp (list W)),
        {{ [[vhead <-- head as _]] :: [[`vlst <~~ s as _]] :: [[vtest <-- (bool2w false) as _]] :: [[`vret <~~ acc as _]] :: tenv }}
          facadeBody
        {{ [[`vlst <~~ s as _]] :: [[vtest <-- (bool2w false) as _]] :: [[`vret <~~ (f acc head) as _]] :: tenv }} ∪ {{ ext }} // env) ->
    {{ [[`vlst <~~ lst as _]] :: tenv }}
      (Seq facadeInit (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call vtest fdealloc (vlst :: nil))))
    {{ [[lst as ls]] :: [[`vret <~~ (fold_comp f ls init) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  Require Import FacadeLoops.
  loop_t.

  rewrite TelEq_swap by congruence;
    eapply CompileCallEmpty_spec; loop_t.

  2:eapply CompileCallFacadeImplementationOfDestructor; loop_t.

  rewrite (TelEq_swap (k' := None)) by loop_t.

  apply miniChomp'; loop_t.

  clear dependent facadeInit;
  generalize dependent init;
  generalize dependent lst;
  induction vv; loop_t.

  rewrite TelEq_swap by loop_t.

  apply CompileWhileFalse_Loop; loop_t.

  eapply CompileWhileTrue; loop_t.

  apply generalized CompileCallPop; loop_t.

  apply CompileCallEmpty_spec; loop_t.

  loop_t.
Qed.

Lemma CompileLoop' :
  forall {A} `{FacadeWrapper av (list W)} `{FacadeWrapper av A}
    (lst: Comp (list W)) init vhead vtest vlst vret fpop fempty fdealloc facadeInit facadeBody env (ext: StringMap.t (Value av)) tenv (f: Comp A -> W -> Comp A),
    GLabelMap.MapsTo fpop (Axiomatic List_pop) env ->
    GLabelMap.MapsTo fempty (Axiomatic List_empty) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (A := list W))) env ->
    vtest ∉ ext ->
    NotInTelescope vtest tenv ->
    vlst ∉ ext ->
    NotInTelescope vlst tenv ->
    vret ∉ ext ->
    NotInTelescope vret tenv ->
    vhead ∉ ext ->
    NotInTelescope vhead tenv ->
    vtest <> vret ->
    vtest <> vlst ->
    vtest <> vhead ->
    vret <> vlst ->
    vret <> vhead ->
    vlst <> vhead ->
    {{ [[`vlst <~~ lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <~~ init as _]] :: [[`vlst <~~ lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    (forall head (acc: Comp A) (s: Comp (list W)),
        {{ [[vhead <-- head as _]] :: [[`vlst <~~ s as _]] :: [[vtest <-- (bool2w false) as _]] :: [[`vret <~~ acc as _]] :: tenv }}
          facadeBody
        {{ [[`vlst <~~ s as _]] :: [[vtest <-- (bool2w false) as _]] :: [[`vret <~~ (f acc head) as _]] :: tenv }} ∪ {{ ext }} // env) ->
    {{ [[`vlst <~~ lst as _]] :: tenv }}
      (Seq facadeInit (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call vtest fdealloc (vlst :: nil))))
    {{ [[lst as ls]] :: [[`vret <~~ (fold_comp f ls init) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  loop_t.

  rewrite TelEq_swap by congruence;
    eapply CompileCallEmpty_spec; loop_t.

  2:eapply (CompileCallFacadeImplementationOfDestructor (A := list W)); loop_t.

  loop_unify_with_nil_t.
  
  rewrite (TelEq_swap (k' := None)) by loop_t.

  apply miniChomp'; loop_t.

  clear dependent facadeInit;
  generalize dependent init;
  generalize dependent lst;
  induction vv; loop_t.

  rewrite TelEq_swap by loop_t.

  apply CompileWhileFalse_Loop; loop_t.

  eapply CompileWhileTrue; loop_t.

  apply generalized CompileCallPop; loop_t.

  apply CompileCallEmpty_spec; loop_t.

  loop_t.
Qed.

Lemma CompileLoop_strong :
  forall `{FacadeWrapper av (list W)}
    lst init vhead vtest vlst vret fpop fempty fdealloc facadeInit facadeBody facadeConclude
    env (ext: StringMap.t (Value av)) tenv tenv' (f: Comp W -> W -> Comp W),
    GLabelMap.MapsTo fpop (Axiomatic List_pop) env ->
    GLabelMap.MapsTo fempty (Axiomatic List_empty) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (A := list W))) env ->
    vtest ∉ ext ->
    NotInTelescope vtest tenv ->
    vlst ∉ ext ->
    NotInTelescope vlst tenv ->
    vret ∉ ext ->
    NotInTelescope vret tenv ->
    vhead ∉ ext ->
    NotInTelescope vhead tenv ->
    vtest <> vret ->
    vtest <> vlst ->
    vtest <> vhead ->
    vret <> vlst ->
    vret <> vhead ->
    vlst <> vhead ->
    {{ [[`vlst <~~ lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <~~ init as _]] :: [[`vlst <~~ lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    {{ [[lst as ls]] :: [[`vret <~~ (fold_comp f ls init) as _]] :: tenv }}
      facadeConclude
    {{ [[lst as ls]] :: [[`vret <~~ (fold_comp f ls init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (acc: Comp W) (s: Comp (list W)),
        {{ [[vhead <-- head as _]] :: [[`vlst <~~ s as _]] :: [[vtest <-- (bool2w false) as _]] :: [[`vret <~~ acc as _]] :: tenv }}
          facadeBody
        {{ [[`vlst <~~ s as _]] :: [[vtest <-- (bool2w false) as _]] :: [[`vret <~~ (f acc head) as _]] :: tenv }} ∪ {{ ext }} // env) ->
    {{ [[`vlst <~~ lst as _]] :: tenv }}
      (Seq (Seq facadeInit (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call vtest fdealloc (vlst :: nil)))) facadeConclude)
    {{ [[lst as ls]] :: [[`vret <~~ (fold_comp f ls init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros.
  eapply CompileSeq;
    [ apply CompileLoop | eassumption ];
    assumption.
Qed.

Parameter TSearchTerm : Type.
Parameter TAcc : Type.
Definition av := (list W + TSearchTerm + TAcc)%type.

Definition MyEnvListsB : Env (list W + TSearchTerm + TAcc) :=
  (GLabelMap.add ("std", "rand") (Axiomatic FRandom))
    ((GLabelMap.add ("list", "nil") (Axiomatic (FacadeImplementationOfConstructor (@nil W))))
       ((GLabelMap.add ("list", "push!") (Axiomatic (FacadeImplementationOfMutation (@cons W))))
          ((GLabelMap.add ("list", "pop!") (Axiomatic List_pop))
             ((GLabelMap.add ("list", "delete!") (Axiomatic (FacadeImplementationOfDestructor (A := list W))))
                ((GLabelMap.add ("list", "empty?") (Axiomatic List_empty))
                   ((GLabelMap.add ("search", "delete!") (Axiomatic (FacadeImplementationOfDestructor (A := TSearchTerm))))
                      ((GLabelMap.add ("acc", "delete!") (Axiomatic (FacadeImplementationOfDestructor (A := TAcc))))
                         (GLabelMap.empty (FuncSpec _))))))))).

Example other_test_with_adt''':
  sigT (fun prog => forall (searchTerm: TSearchTerm) (init: TAcc),
            {{ [["search" <-- searchTerm as _]] :: [["init" <-- init as _]] :: (@Nil av) }}
              prog
            {{ [[`"ret" <~~  ( seq <- {s: list W | True };
                             fold_comp (fun acc elem =>
                                          acc <- acc;
                                          { x: W | Word.wlt (Word.wplus acc elem) x })
                                       seq (ret (Word.natToWord 32 0: W))) as _]] :: (@Nil av) }} ∪ {{ StringMap.empty (Value av) }} // MyEnvListsB).
Proof.
  Unset Ltac Debug.
  econstructor; intros.

  repeat setoid_rewrite SameValues_Fiat_Bind_TelEq.

  eapply ProgOk_Transitivity_Name' with "seq".

  instantiate (1 := Skip).       (* FIXME alloc *)
  admit.

  let av := av_from_ext (StringMap.empty (Value av)) in
  let fpop := find_function_pattern_in_env
               (fun w => (Axiomatic (List_pop (av := av) (H := w)))) MyEnvListsB in
  let fempty := find_function_pattern_in_env
                 (fun w => (Axiomatic (List_empty (av := av) (H := w)))) MyEnvListsB in
  let fdealloc := find_function_pattern_in_env
                   (fun w => (Axiomatic (FacadeImplementationOfDestructor
                                        (A := list W) (av := av) (H := w)))) MyEnvListsB in
  let vtest := gensym "test" in
  let vhead := gensym "head" in
  apply (CompileLoop_strong (vtest := vtest) (vhead := vhead) (fpop := fpop) (fempty := fempty) (fdealloc := fdealloc));
    try compile_do_side_conditions.

  repeat compile_step.
  repeat compile_step.

  eapply CompileSeq.
  let fdealloc := find_function_pattern_in_env
                   (fun w => (Axiomatic (FacadeImplementationOfDestructor
                                        (A := TSearchTerm) (av := av) (H := w)))) MyEnvListsB in
  let vtmp := gensym "tmp" in
  apply (CompileCallFacadeImplementationOfDestructor (fpointer := fdealloc) (vtmp := vtmp));
    try compile_do_side_conditions.

  let fdealloc := find_function_pattern_in_env
                   (fun w => (Axiomatic (FacadeImplementationOfDestructor
                                        (A := TAcc) (av := av) (H := w)))) MyEnvListsB in
  let vtmp := gensym "tmp" in
  apply (CompileCallFacadeImplementationOfDestructor (fpointer := fdealloc) (vtmp := vtmp));
    try compile_do_side_conditions.

  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  apply miniChomp.
  intros.
  rewrite Propagate_anonymous_ret.

  instantiate (1 := Skip).
  admit.
Defined.

Eval compute in (extract_facade other_test_with_adt''').

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
 
