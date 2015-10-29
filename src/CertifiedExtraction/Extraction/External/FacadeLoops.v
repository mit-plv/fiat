Require Import
        CertifiedExtraction.Extraction.AllInternal
        CertifiedExtraction.Extraction.External.Core
        CertifiedExtraction.Extraction.External.Loops
        CertifiedExtraction.Extraction.External.GenericADTMethods
        CertifiedExtraction.Extraction.External.FacadeADTs.

Lemma CompileLoop :
  forall lst init facadeInit facadeBody vhead vtest vlst vret env (ext: StringMap.t (Value (list W))) tenv fpop fempty fdealloc f,
    GLabelMap.MapsTo fpop (Axiomatic List_pop) env ->
    GLabelMap.MapsTo fempty (Axiomatic List_empty) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor _)) env ->
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
    {{ [[vlst <-- ADT lst as _]] :: tenv }}
      facadeInit
    {{ [[vret <-- SCA _ init as _]] :: [[vlst <-- ADT lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    (forall head acc s,
        {{ [[vhead <-- SCA _ head as _]] :: [[vlst <-- ADT s as _]] :: [[vtest <-- SCA _ (bool2w false) as _]] :: [[vret <-- SCA _ acc as _]] :: tenv }}
          facadeBody
        {{ [[vlst <-- ADT s as _]] :: [[vtest <-- SCA _ (bool2w false) as _]] :: [[vret <-- SCA _ (f acc head) as _]] :: tenv }} ∪ {{ ext }} // env) ->
    {{ [[vlst <-- ADT lst as _]] :: tenv }}
      (Seq facadeInit (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call vtest fdealloc (vlst :: nil))))
    {{ [[vret <-- SCA _ (fold_left f lst init) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  eapply CompileSeq; eauto; clear dependent facadeInit.

  unfold Fold.
  eapply CompileSeq.

  eapply CompileSeq.

  rewrite TelEq_swap by congruence;
    eapply CompileCallEmpty'; Lifted_t.

  clean_DropName_in_ProgOk.

  2:eapply CompileCallFacadeImplementationOfDestructor; Lifted_t.

  generalize dependent init;
    induction lst; simpl; intros.

  apply CompileWhileFalse_Loop; try instantiate (1 := nil); Lifted_t. (* instantiate due to Coq bug *)

  eapply CompileWhileTrue; Lifted_t.

  eapply CompileSeq.
  eapply CompileCallPop'; Lifted_t.
  clean_DropName_in_ProgOk.

  eapply CompileSeq; eauto.

  apply CompileCallEmpty'; Lifted_t.
  clean_DropName_in_ProgOk.

  eauto.
Qed.
