Require Import
        CertifiedExtraction.Extraction.Internal
        CertifiedExtraction.Extraction.External.Core
        CertifiedExtraction.Extraction.External.Loops
        CertifiedExtraction.Extraction.External.GenericADTMethods
        CertifiedExtraction.Extraction.External.FacadeADTs.

Ltac loop_unify_with_nil_t :=
  match goal with
  | [  |- context[Cons (T := list ?A) _ (ret ?val) _] ] => is_evar val; unify val (@nil A)
  end.

Ltac loop_t :=
  repeat (intros || unfold Fold || solve [PreconditionSet_t; Lifted_t] || compile_do_side_conditions || clean_DropName_in_ProgOk || rewrite Propagate_ret || eapply CompileSeq || eauto 2).

Lemma CompileLoopBase :
  forall `{FacadeWrapper (Value av) A} `{FacadeWrapper (Value av) A'} `{FacadeWrapper av (list A)}
    lst init vhead vtest vlst vret fpop fempty fdealloc facadeBody env (ext: StringMap.t (Value av)) tenv (f: Comp A' -> A -> Comp A'),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    (forall head (acc: Comp A') (s: list A),
        {{ [[`vret ~~> acc as _]] :: [[`vhead ->> head as _]] :: tenv }}
          facadeBody
        {{ [[`vret ~~> (f acc head) as _]] :: tenv }} ∪
        {{ [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) ->
    {{ [[`vret ~~> init as _]] :: [[`vlst ->> lst as _]] :: tenv }}
      (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil)))
    {{ [[`vret ~~> (fold_left f lst init) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  unfold DummyArgument; loop_t.

  rewrite TelEq_swap by loop_t;
    eapply CompileCallEmpty_spec; loop_t.

  2:eapply CompileCallFacadeImplementationOfDestructor; loop_t.

  loop_unify_with_nil_t.

  loop_t.
  generalize dependent init;
  induction lst; loop_t.

  move_to_front vtest;
  apply CompileWhileFalse_Loop; loop_t.

  eapply CompileWhileTrue; [ loop_t.. | ].

  apply generalized @CompileCallPop; loop_t.

  move_to_front vlst; apply ProgOk_Chomp_Some; loop_t.
  move_to_front vtest; apply ProgOk_Chomp_Some; loop_t.
  computes_to_inv; subst; defunctionalize_evar; eauto.

  rewrite TelEq_swap; eauto.
  apply CompileCallEmpty_spec; loop_t.

  loop_t.
Qed.

Lemma CompileLoop :
  forall `{FacadeWrapper (Value av) A} `{FacadeWrapper (Value av) A'} `{FacadeWrapper av (list A)}
    lst init vhead vtest vlst vret fpop fempty fdealloc facadeBody facadeConclude
    env (ext: StringMap.t (Value av)) tenv tenv' (f: Comp A' -> A -> Comp A'),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    {{ [[`vret ~~> (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret ~~> (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (acc: Comp A') (s: list A),
        {{ [[`vret ~~> acc as _]] :: [[`vhead ->> head as _]] :: tenv }}
          facadeBody
        {{ [[`vret ~~> (f acc head) as _]] :: tenv }} ∪
        {{ [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) ->
    {{ [[`vret ~~> init as _]] :: [[`vlst ->> lst as _]] :: tenv }}
      (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
    {{ [[`vret ~~> (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  eauto using @CompileSeq, @CompileLoopBase.
Qed.

Lemma CompileLoopAlloc :
  forall `{FacadeWrapper (Value av) A} `{FacadeWrapper (Value av) A'} `{FacadeWrapper av (list A)}
    lst init vhead vtest vlst vret fpop fempty fdealloc facadeInit facadeBody facadeConclude
    env (ext: StringMap.t (Value av)) tenv tenv' (f: Comp A' -> A -> Comp A'),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    {{ [[`vlst ->> lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret ~~> init as _]] :: [[`vlst ->> lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    {{ [[`vret ~~> (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret ~~> (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (acc: Comp A') (s: list A),
        {{ [[`vret ~~> acc as _]] :: [[`vhead ->> head as _]] :: tenv }}
          facadeBody
        {{ [[`vret ~~> (f acc head) as _]] :: tenv }} ∪
        {{ [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) ->
    {{ [[`vlst ->> lst as _]] :: tenv }}
      (Seq facadeInit (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude))
    {{ [[`vret ~~> (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  eauto using @CompileSeq, @CompileLoop.
Qed.

Definition revmap {A B} f := fun seq => @map A B f (rev seq).

Open Scope list_scope.

Lemma revmap_fold_helper:
  forall (A A' : Type) (f : A -> A') (a : A) (vv : list A) (base : list A'),
    revmap f (a :: vv) ++ base = revmap f vv ++ f a :: base.
Proof.
  unfold revmap; intros; simpl.
  rewrite map_rev.
  rewrite map_app.
  simpl.
  rewrite <- app_assoc.
  simpl.
  rewrite <- map_rev.
  reflexivity.
Qed.

Lemma revmap_fold_generalized :
  forall {A B} (f: A -> B) (seq: list A) (base: list B),
    fold_left (fun acc elem => f elem :: acc) seq base = (@revmap A B f seq) ++ base.
Proof.
  induction seq; simpl; intros.
  - reflexivity.
  - rewrite revmap_fold_helper; eauto.
Qed.

Lemma revmap_fold :
  forall {A B} (f: A -> B) (seq: list A),
    fold_left (fun acc elem => f elem :: acc) seq nil = @revmap A B f seq.
Proof.
  intros.
  rewrite <- (app_nil_r (revmap f seq)).
  apply revmap_fold_generalized.
Qed.

Lemma revmap_fold_comp_generalized :
  forall {A B} (f: A -> B) (seq: list A) base,
    Monad.equiv
      (fold_left (fun cacc elem => (acc <- cacc; ret (f elem :: acc))%comp) seq base)
      ( b <- base;
        ret ((@revmap A B f seq) ++ b)).
Proof.
  intros; etransitivity.
  2: apply Monad.computes_under_bind; intros; rewrite <- revmap_fold_generalized; apply SetoidMorphisms.equiv_refl.

  generalize dependent base; induction seq; simpl;
  [ | setoid_rewrite IHseq ];
  split; intros; computes_to_inv; subst; eauto using BindComputes.
Qed.

Lemma revmap_fold_comp :
  forall {A B} (f: A -> B) (seq: list A),
    Monad.equiv
      (fold_left (fun cacc elem => (acc <- cacc; ret (f elem :: acc))%comp) seq (ret nil))
      (ret (@revmap A B f seq)).
Proof.
  intros.
  rewrite <- (app_nil_r (revmap f seq)).
  rewrite revmap_fold_comp_generalized.
  split; intros; computes_to_inv; subst; eauto using BindComputes.
Qed.

Lemma CompileMap_ADT :
  forall {av A A'} `{FacadeWrapper av (list A)} `{FacadeWrapper av (list A')} `{FacadeWrapper (Value av) A} `{FacadeWrapper av A'}
    (lst: list A) vhead vhead' vtest vlst vret vtmp fpop fempty falloc fdealloc fcons facadeBody facadeCoda env (ext: StringMap.t (Value av)) tenv tenv' (f: A -> A'),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo falloc (Axiomatic (FacadeImplementationOfConstructor (list A') nil)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    GLabelMap.MapsTo fcons (Axiomatic (FacadeImplementationOfMutation_ADT A' (list A') cons)) env ->
    (* GLabelMap.MapsTo fdealloc_one (Axiomatic (FacadeImplementationOfDestructor A)) env -> *)
    PreconditionSet tenv ext [[[vhead; vhead'; vtest; vlst; vret; vtmp]]] ->
    {{ [[`vret ->> (revmap f lst) as _]] :: tenv }}
      facadeCoda
    {{ [[`vret ->> (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (s: list A) (s': list A'),
        {{ [[`vhead ->> head as _]] :: tenv }}
          facadeBody
        {{ [[`vhead' ->> f head as _]] :: tenv }} ∪
        {{ [vret |> wrap s'] :: [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) ->
    {{ [[`vlst ->> lst as _]] :: tenv }}
      (Seq
         (Call vret falloc nil)
         (Seq
            (Seq
               (Fold vhead vtest vlst fpop fempty
                     (Seq facadeBody
                          (Call vtmp fcons (vret :: vhead' :: nil))))
               (Call vtest fdealloc (vlst :: nil)))
            facadeCoda))
    {{ [[`vret ->> (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite <- revmap_fold_comp.
  apply CompileLoopAlloc; eauto.
  PreconditionSet_t; eauto.
  eapply (CompileCallFacadeImplementationOfConstructor (A := list A')); loop_t.
  setoid_rewrite revmap_fold_comp; eassumption.
  intros.
  rewrite SameValues_Fiat_Bind_TelEq.
  move_to_front vret.
  apply miniChomp'; intros.
  hoare.
  apply ProgOk_Chomp_Some; loop_t; defunctionalize_evar; eauto.
  apply CompileCallFacadeImplementationOfMutation_ADT; compile_do_side_conditions.
Qed.

Lemma CompileMap_SCA :
  forall {av A} `{FacadeWrapper av (list A)} `{FacadeWrapper av (list W)} `{FacadeWrapper (Value av) A}
    (lst: list A) vhead vhead' vtest vlst vret vtmp fpop fempty falloc fdealloc fcons facadeBody facadeCoda env (ext: StringMap.t (Value av)) tenv tenv' (f: A -> W),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo falloc (Axiomatic (FacadeImplementationOfConstructor (list W) nil)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    GLabelMap.MapsTo fcons (Axiomatic (FacadeImplementationOfMutation_SCA (list W) cons)) env ->
    (* GLabelMap.MapsTo fdealloc_one (Axiomatic (FacadeImplementationOfDestructor A)) env -> *)
    PreconditionSet tenv ext [[[vhead; vhead'; vtest; vlst; vret; vtmp]]] ->
    {{ [[`vret ->> (revmap f lst) as _]] :: tenv }}
      facadeCoda
    {{ [[`vret ->> (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (s: list A) (s': list W),
        {{ [[`vhead ->> head as _]] :: tenv }}
          facadeBody
        {{ [[`vhead' ->> f head as _]] :: tenv }} ∪
        {{ [vret |> wrap s'] :: [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) ->
    {{ [[`vlst ->> lst as _]] :: tenv }}
      (Seq
         (Call vret falloc nil)
         (Seq
            (Seq
               (Fold vhead vtest vlst fpop fempty
                     (Seq facadeBody
                          (Call vtmp fcons (vret :: vhead' :: nil))))
               (Call vtest fdealloc (vlst :: nil)))
            facadeCoda))
    {{ [[`vret ->> (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite <- revmap_fold_comp.
  apply CompileLoopAlloc; eauto.
  PreconditionSet_t; eauto.
  eapply (CompileCallFacadeImplementationOfConstructor (A := list W)); loop_t.
  setoid_rewrite revmap_fold_comp; eassumption.
  intros.
  rewrite SameValues_Fiat_Bind_TelEq.
  move_to_front vret.
  apply miniChomp'; intros.
  hoare.
  apply ProgOk_Chomp_Some; loop_t; defunctionalize_evar; eauto.
  apply CompileCallFacadeImplementationOfMutation_SCA; unfold DummyArgument; compile_do_side_conditions.
Qed.

(* NOTE: Could prove lemma for un-reved map using temp variable *)

Lemma ret_fold_fold_ret_lemma :
  forall {TElem TAcc} (f: TAcc -> TElem -> TAcc) lst (init: TAcc) init_comp,
    Monad.equiv (ret init) init_comp ->
    Monad.equiv (ret (fold_left f lst init))
                (fold_left (fun (acc: Comp TAcc) x => (a <- acc; ret (f a x))%comp) lst init_comp).
Proof.
  induction lst; simpl; intros.
  - trivial.
  - etransitivity; [ apply IHlst | reflexivity ].
    unfold Monad.equiv in *; repeat (cleanup_pure || computes_to_inv || subst).
    + eapply BindComputes; try rewrite <- H; apply ReturnComputes.
    + rewrite <- H in *; computes_to_inv; subst; apply ReturnComputes.
Qed.

Lemma ret_fold_fold_ret :
  forall {TElem TAcc} (f: TAcc -> TElem -> TAcc) lst (init: TAcc),
    Monad.equiv (ret (fold_left f lst init))
                (fold_left (fun (acc: Comp TAcc) x => (a <- acc; ret (f a x))%comp) lst (ret init)).
Proof.
  intros; apply ret_fold_fold_ret_lemma; apply SetoidMorphisms.equiv_refl.
Qed.

Lemma CompileLoop_ret :
  forall {av A} `{FacadeWrapper (Value av) A} `{FacadeWrapper (Value av) A'} `{FacadeWrapper av (list A)}
    lst init facadeBody facadeConclude vhead vtest vlst vret env (ext: StringMap.t (Value av)) tenv tenv' fpop fempty fdealloc (f: A' -> A -> A'),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    (forall head acc (s: list A),
        {{ [[`vret ->> acc as _]] :: [[`vhead ->> head as _]] :: tenv }}
          facadeBody
        {{ [[`vret ->> (f acc head) as _]] :: tenv }} ∪ {{ [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) ->
    {{ [[`vret ->> (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret ->> (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[`vret ->> init as _]] :: [[`vlst ->> lst as _]] :: tenv }}
      (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
    {{ [[`vret ->> (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite ret_fold_fold_ret.
  eapply CompileSeq.
  apply CompileLoopBase; eauto.
  2: apply ProkOk_specialize_to_ret; intros * h; apply ret_fold_fold_ret in h; computes_to_inv; subst; eauto.
  intros; rewrite SameValues_Fiat_Bind_TelEq.
  apply miniChomp'; intros; eauto.
Qed.

Lemma CompileLoopAlloc_ret :
  forall {av A} `{FacadeWrapper (Value av) A} `{FacadeWrapper (Value av) A'} `{FacadeWrapper av (list A)}
    lst init facadeInit facadeBody facadeConclude vhead vtest vlst vret env (ext: StringMap.t (Value av)) tenv tenv' fpop fempty fdealloc (f: A' -> A -> A'),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    {{ [[`vlst ->> lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret ->> init as _]] :: [[`vlst ->> lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    (forall head acc (s: list A),
        {{ [[`vret ->> acc as _]] :: [[`vhead ->> head as _]] :: tenv }}
          facadeBody
        {{ [[`vret ->> (f acc head) as _]] :: tenv }} ∪ {{ [vtest |> wrap (bool2w false)] :: [vlst |> wrap s] :: ext }} // env) ->
    {{ [[`vret ->> (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret ->> (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[`vlst ->> lst as _]] :: tenv }}
      (Seq facadeInit (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude))
    {{ [[`vret ->> (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  eauto using @CompileSeq, @CompileLoop_ret.
Qed.
