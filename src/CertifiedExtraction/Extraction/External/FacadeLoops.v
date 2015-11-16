Require Import
        CertifiedExtraction.Extraction.AllInternal
        CertifiedExtraction.Extraction.External.Core
        CertifiedExtraction.Extraction.External.Loops
        CertifiedExtraction.Extraction.External.GenericADTMethods
        CertifiedExtraction.Extraction.External.FacadeADTs.

Ltac loop_unify_with_nil_t :=
  match goal with
  | [  |- context[Cons (T := list ?A) _ (ret ?val) _] ] => is_evar val; unify val (@nil A)
  end.

Ltac loop_t :=
  repeat (intros || unfold Fold || Lifted_t || compile_do_side_conditions || clean_DropName_in_ProgOk || rewrite Propagate_ret || eapply CompileSeq || eauto 2).

Ltac apply_generalized_t compilation_lemma :=
  erewrite ProgOk_TelEq_morphism;
  try eapply compilation_lemma;
  repeat match goal with
         | [  |- _ = _ ] => reflexivity
         | [  |- TelEq _ _ _ ] => decide_TelEq_instantiate
         end.

Tactic Notation "apply" "generalized" constr(compilation_lemma) :=
  apply_generalized_t compilation_lemma.

Lemma CompileLoop :
  forall `{FacadeWrapper (Value av) A} `{FacadeWrapper (Value av) A'} `{FacadeWrapper av (list A)}
    lst init facadeInit facadeBody vhead vtest vlst vret env (ext: StringMap.t (Value av)) tenv fpop fempty fdealloc (f: A' -> A -> A'),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
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
    {{ [[`vlst <-- lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <-- init as _]] :: [[`vlst <-- lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    (forall head acc (s: list A),
        {{ [[`vhead <-- head as _]] :: [[`vlst <-- s as _]] :: [[`vtest <-- (bool2w false) as _]] :: [[`vret <-- acc as _]] :: tenv }}
          facadeBody
        {{ [[`vlst <-- s as _]] :: [[`vtest <-- (bool2w false) as _]] :: [[`vret <-- (f acc head) as _]] :: tenv }} ∪ {{ ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq facadeInit (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call vtest fdealloc (vlst :: nil))))
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  loop_t.

  rewrite TelEq_swap;
    eapply (CompileCallEmpty (lst := lst)); loop_t.

  loop_t.
  2:eapply CompileCallFacadeImplementationOfDestructor; loop_t.

  loop_unify_with_nil_t. (* instantiate early to prevent bad unification heuristics *)

  clear dependent facadeInit;
    generalize dependent init;
    induction lst; simpl; intros.

  apply CompileWhileFalse_Loop; loop_t.

  eapply CompileWhileTrue; loop_t.

  apply generalized @CompileCallPop; loop_t.

  apply generalized @CompileCallEmpty; loop_t.
Qed.
