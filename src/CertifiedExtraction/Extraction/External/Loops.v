Require Import
        CertifiedExtraction.Extraction.DeallocSCA
        CertifiedExtraction.Extraction.External.Core.

Lemma CompileWhileFalse:
  forall {av} (env : GLabelMap.t (FuncSpec av)) (ext : StringMap.t (Value av))
    (tenv : Telescope av) tenv' test body,
    TelEq ext tenv tenv' ->
    Lifted_is_false ext tenv test ->
    {{ tenv }} (DFacade.While test body) {{ tenv' }} ∪ {{ ext }} // env.
Proof.
  intros * H **.
  rewrite <- H; clear H.
  repeat match goal with
         | [ H: forall st, st ≲ _ ∪ _ -> _, H': ?st ≲ _ ∪ _ |- _ ] => learn (H _ H')
         | [ H: is_true ?t ?st, H': is_false ?t ?st |- _ ] => exfalso; exact (is_true_is_false_contradiction H H')
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         | _ => LiftPropertyToTelescope_t
         | _ => apply SafeWhileFalse
         | [ H: RunsTo _ (DFacade.While _ _) _ _ |- _ ] => inversion H; unfold_and_subst; clear H
         end.
Qed.

Lemma CompileWhileTrue:
  forall {av} (env : GLabelMap.t (FuncSpec av)) (ext : StringMap.t (Value av))
    (tenv : Telescope av) tenv' tenv'' test body,
    Lifted_is_true ext tenv test ->
    {{ tenv }}  body                      {{ tenv' }}  ∪ {{ ext }} // env ->
    {{ tenv' }} (DFacade.While test body) {{ tenv'' }} ∪ {{ ext }} // env ->
    {{ tenv }}  (DFacade.While test body) {{ tenv'' }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | [ H: forall st, st ≲ _ ∪ _ -> _, H': ?st ≲ _ ∪ _ |- _ ] => learn (H _ H')
         | [ H: is_true ?t ?st, H': is_false ?t ?st |- _ ] => exfalso; exact (is_true_is_false_contradiction H H')
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         | _ => LiftPropertyToTelescope_t
         | _ => apply SafeWhileTrue
         | [ H: RunsTo _ (DFacade.While _ _) _ _ |- _ ] => inversion H; unfold_and_subst; clear H
         end.
Qed.

Lemma CompileWhileFalse_Loop:
  forall {av} (vtest : StringMap.key)
    (env : GLabelMap.t (FuncSpec av)) (ext : StringMap.t (Value av))
    (tenv : Telescope av) tenv' body,
    TelEq ext tenv tenv' ->
    vtest ∉ ext ->
    NotInTelescope vtest tenv ->
    {{[[`vtest ->> (Word.natToWord 32 1) as _]]::tenv }}
      (DFacade.While (TestE IL.Eq vtest O) body)
    {{ tenv' }} ∪ {{ ext }} // env.
Proof.
  intros * H **.
  rewrite <- H.
  apply CompileDeallocW_discretely; eauto.
  apply CompileWhileFalse.
  reflexivity.
  unfold Lifted_is_false, LiftPropertyToTelescope, is_true, is_false, eval_bool, eval;
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         | _ => progress simpl
         end.
Qed.

