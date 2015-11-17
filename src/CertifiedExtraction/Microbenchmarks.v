Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Examples
        CertifiedExtraction.Extraction.AllInternal
        CertifiedExtraction.Extraction.Extraction.

(* FIXME move *)


Require Import
        CertifiedExtraction.Extraction.AllInternal
        CertifiedExtraction.Extraction.External.Core
        CertifiedExtraction.Extraction.External.Loops
        CertifiedExtraction.Extraction.External.GenericADTMethods
        CertifiedExtraction.Extraction.External.FacadeADTs.

(* Opaque WrapInstance.            (* FIXME simpl never? *) *)

Require Import FacadeLoops.

Ltac defunctionalize_evar :=
  match goal with
  | [  |- context[?e] ] =>
    is_evar e;
      match type of e with
      | ?a -> ?b => let ee := fresh in
                  evar (ee: b);
                    unify e (fun _:a => ee);
                    unfold ee in *;
                    clear ee
      end
  end.

Ltac move_to_front var :=
  repeat
    lazymatch goal with         (* `at 1' prevents setoid_rewrite from modifying evars *)
    | [  |- context[Cons ?k _ (fun _ => Cons var _ _)] ] => setoid_rewrite (TelEq_swap k var) at 1
    | [  |- context[Cons ?k _ (fun _ => Cons (@NTSome _ _ var _) _ _)] ] => setoid_rewrite (TelEq_swap k (@NTSome _ _ var _)) at 1
    end.

Lemma CompileLoopBase :
  forall `{FacadeWrapper (Value av) A} `{FacadeWrapper (Value av) A'} `{FacadeWrapper av (list A)}
    lst init vhead vtest vlst vret fpop fempty fdealloc facadeBody env (ext: StringMap.t (Value av)) tenv (f: Comp A' -> A -> Comp A'),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    (forall head (acc: Comp A') (s: list A),
        {{ [[`vret <~~ acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <~~ (f acc head) as _]] :: tenv }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vret <~~ init as _]] :: [[`vlst <-- lst as _]] :: tenv }}
      (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil)))
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv }} ∪ {{ ext }} // env.
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
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (acc: Comp A') (s: list A),
        {{ [[`vret <~~ acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <~~ (f acc head) as _]] :: tenv }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vret <~~ init as _]] :: [[`vlst <-- lst as _]] :: tenv }}
      (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
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
    {{ [[`vlst <-- lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <~~ init as _]] :: [[`vlst <-- lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (acc: Comp A') (s: list A),
        {{ [[`vret <~~ acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <~~ (f acc head) as _]] :: tenv }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq facadeInit (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude))
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  eauto using @CompileSeq, @CompileLoop.
Qed.

Definition revmap {A B} f := fun seq => @map A B f (rev seq).

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

Lemma CompileMapAlloc_ADT :
  forall {av A A'} `{FacadeWrapper av (list A)} `{FacadeWrapper av (list A')} `{FacadeWrapper (Value av) A} `{FacadeWrapper av A'}
    (lst: list A) vhead vhead' vtest vlst vret vtmp fpop fempty falloc fdealloc fcons facadeBody facadeCoda env (ext: StringMap.t (Value av)) tenv tenv' (f: A -> A'),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo falloc (Axiomatic (FacadeImplementationOfConstructor (list A') nil)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    GLabelMap.MapsTo fcons (Axiomatic (FacadeImplementationOfMutation_ADT A' (list A') cons)) env ->
    (* GLabelMap.MapsTo fdealloc_one (Axiomatic (FacadeImplementationOfDestructor A)) env -> *)
    PreconditionSet tenv ext [[[vhead; vhead'; vtest; vlst; vret; vtmp]]] ->
    {{ [[`vret <-- (revmap f lst) as _]] :: tenv }}
      facadeCoda
    {{ [[`vret <-- (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (s: list A) (s': list A'),
        {{ [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vhead' <-- f head as _]] :: tenv }} ∪
        {{ [vret <-- wrap s'] :: [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq
         (Call vret falloc nil)
         (Seq
            (Seq
               (Fold vhead vtest vlst fpop fempty
                     (Seq facadeBody
                          (Call vtmp fcons (vret :: vhead' :: nil))))
               (Call vtest fdealloc (vlst :: nil)))
            facadeCoda))
    {{ [[`vret <-- (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env.
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

Lemma CompileMapAlloc_SCA :
  forall {av A} `{FacadeWrapper av (list A)} `{FacadeWrapper av (list W)} `{FacadeWrapper (Value av) A}
    (lst: list A) vhead vhead' vtest vlst vret vtmp fpop fempty falloc fdealloc fcons facadeBody facadeCoda env (ext: StringMap.t (Value av)) tenv tenv' (f: A -> W),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo falloc (Axiomatic (FacadeImplementationOfConstructor (list W) nil)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    GLabelMap.MapsTo fcons (Axiomatic (FacadeImplementationOfMutation_SCA (list W) cons)) env ->
    (* GLabelMap.MapsTo fdealloc_one (Axiomatic (FacadeImplementationOfDestructor A)) env -> *)
    PreconditionSet tenv ext [[[vhead; vhead'; vtest; vlst; vret; vtmp]]] ->
    {{ [[`vret <-- (revmap f lst) as _]] :: tenv }}
      facadeCoda
    {{ [[`vret <-- (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (s: list A) (s': list W),
        {{ [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vhead' <-- f head as _]] :: tenv }} ∪
        {{ [vret <-- wrap s'] :: [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq
         (Call vret falloc nil)
         (Seq
            (Seq
               (Fold vhead vtest vlst fpop fempty
                     (Seq facadeBody
                          (Call vtmp fcons (vret :: vhead' :: nil))))
               (Call vtest fdealloc (vlst :: nil)))
            facadeCoda))
    {{ [[`vret <-- (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env.
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
        {{ [[`vret <-- acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <-- (f acc head) as _]] :: tenv }} ∪ {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[`vret <-- init as _]] :: [[`vlst <-- lst as _]] :: tenv }}
      (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
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
    {{ [[`vlst <-- lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <-- init as _]] :: [[`vlst <-- lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    (forall head acc (s: list A),
        {{ [[`vret <-- acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <-- (f acc head) as _]] :: tenv }} ∪ {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq facadeInit (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude))
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  eauto using @CompileSeq, @CompileLoop_ret.
Qed.


Lemma SameValues_Fiat_Bind_TelEq_Pair :
  forall {av A1 A2 B} key compA compB tail ext,
    TelEq ext
          (Cons (av := av) key (@Bind (A1 * A2) B compA compB) tail)
          (Cons NTNone compA (fun a => Cons NTNone (ret (fst a)) (fun a1 => Cons NTNone (ret (snd a)) (fun a2 => Cons key (compB (a1, a2)) tail)))).
Proof.
  unfold TelEq;
  repeat match goal with
         | _ => progress subst
         | _ => progress SameValues_Fiat_t_step
         | _ => rewrite <- surjective_pairing in *
         end.
Qed.

Lemma ProgOk_Transitivity_Name_Pair :
  forall {av A1 A2} `{FacadeWrapper av A1} `{FacadeWrapper av A2} {ext env}
    vfst vsnd tenv tenv' (pair: Comp (A1 * A2)) prog d1 d2,
    {{ tenv }}
      prog
    {{ [[pair as p]] :: [[`vfst <-- fst p as p1]] :: [[`vsnd <-- snd p as p2]] :: tenv' p1 p2 }} ∪ {{ext}} // env ->
    {{ [[pair as p]] :: [[`vfst <-- fst p as p1]] :: [[`vsnd <-- snd p as p2]] :: tenv' p1 p2 }}
      d1
    {{ [[pair as p]] :: [[ret (fst p) as p1]] :: [[`vsnd <-- snd p as p2]] :: tenv' p1 p2 }} ∪ {{ext}} // env ->
    {{ [[pair as p]] :: [[ret (fst p) as p1]] :: [[`vsnd <-- snd p as p2]] :: tenv' p1 p2 }}
      d2
    {{ [[pair as p]] :: [[ret (fst p) as p1]] :: [[ret (snd p) as p2]] :: tenv' p1 p2 }} ∪ {{ext}} // env ->
    {{ tenv }}
      Seq prog (Seq d1 d2)
    {{ [[pair as p]] :: [[ret (fst p) as p1]] :: [[ret (snd p) as p2]] :: tenv' p1 p2 }} ∪ {{ext}} // env.
Proof.
  repeat hoare.
Qed.

Lemma CompileDeallocADT_discretely : (* TODO create a specialized version that hardcodes the deallocation call *)
  forall {av A} {env ext} (k: NameTag av A) comp tenv tenv' prog dealloc,
    {{ [[k <~~ comp as kk]] :: tenv kk }}
      prog
      {{ [[k <~~ comp as kk]] :: tenv' kk }} ∪ {{ext}} // env ->
    {{ [[k <~~ comp as kk]] :: tenv' kk }}
      dealloc
      {{ [[comp as kk]] :: tenv' kk }} ∪ {{ext}} // env ->
    {{ [[k <~~ comp as kk]] :: tenv kk }}
      (Seq prog dealloc)
      {{ [[comp as kk]] :: tenv' kk }} ∪ {{ext}} // env.
Proof.
  repeat hoare.
Qed.

Lemma CompileDeallocADT_discretely' : (* TODO create a specialized version that hardcodes the deallocation call *)
  forall {av A} {env ext} (k: NameTag av A) v tenv tenv' prog dealloc,
    {{ [[k <-- v as _]] :: tenv }}
      prog
    {{ [[k <-- v as _]] :: tenv' }} ∪ {{ext}} // env ->
    {{ [[k <-- v as _]] :: tenv' }}
      dealloc
    {{ tenv' }} ∪ {{ext}} // env ->
    {{ [[k <-- v as _]] :: tenv }}
      (Seq prog dealloc)
    {{ tenv' }} ∪ {{ext}} // env.
Proof.
  repeat hoare.
Qed.

  Ltac facade_if_helper ::=     (* Add an eauto 3 to prevent spurious existentials from popping up *)
  match goal with
  | H:is_true ?st (isTrueExpr ?k),
    H':StringMap.MapsTo ?k (wrap (bool2w ?test)) ?st
    |- _ => learn (is_true_isTrueExpr H H')
  | H:is_false ?st (isTrueExpr ?k),
    H':StringMap.MapsTo ?k (wrap (bool2w ?test)) ?st
    |- _ => learn (is_false_isTrueExpr H H')
  | _ => solve
  [ eauto 3 using isTrueExpr_is_false, isTrueExpr_is_true  with SameValues_db ]
  | _ => solve
  [ eauto using isTrueExpr_is_false, isTrueExpr_is_true  with SameValues_db ]
  end.

Lemma CompileIf :
  forall {av A} k tmp (gallinaTest: bool) (gallinaT gallinaF: Comp A) facadeTest facadeT facadeF
    env (ext: StringMap.t (Value av)) tenv tenv',
    tmp ∉ ext ->
    NotInTelescope tmp tenv ->
    {{ tenv }}
      facadeTest
    {{ [[`tmp <-- (bool2w gallinaTest) as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ [[`tmp <-- (bool2w gallinaTest) as _]]::tenv }}
      facadeT
    {{ [[`tmp <-- (bool2w gallinaTest) as _]]::[[k <~~ gallinaT as v]]::tenv' v }} ∪ {{ ext }} // env ->
    {{ [[`tmp <-- (bool2w gallinaTest) as _]]::tenv }}
      facadeF
    {{ [[`tmp <-- (bool2w gallinaTest) as _]]::[[k <~~ gallinaF as v]]::tenv' v }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq facadeTest (DFacade.If (isTrueExpr tmp) facadeT facadeF))
    {{ [[k <~~ if gallinaTest then gallinaT else gallinaF as v]]::tenv' v }} ∪ {{ ext }} // env.
Proof.
  intros; hoare.
  repeat (SameValues_Facade_t_step || facade_if_helper).
Qed.

(* FIXME move stuff above to Extraction.Extraction *)


Lemma SameValues_remove_SCA:
  forall (av0 : Type) (tenv' : Telescope av0)
    (ext : StringMap.t (Value av0)) (k : StringMap.key)
    (final_state : State av0) (x : W),
    StringMap.MapsTo k (wrap x) final_state ->
    StringMap.remove (elt:=Value av0) k final_state ≲ tenv' ∪ ext ->
    final_state ≲ tenv' ∪ ext.
Proof.
  induction tenv'; simpl; intros.
  - rewrite (add_redundant_cancel H).
    rewrite <- add_remove_cancel; try reflexivity.
    apply WeakEq_pop_SCA.
    apply StringMap.remove_1; reflexivity.
    assumption.
  - destruct key; repeat cleanup.
    + eauto.
    + SameValues_Fiat_t.
      StringMap_t.
      rewrite remove_mapsto_iff in *.
      cleanup.
      StringMap_t.
      repeat cleanup.
      eapply H.
      2: rewrite remove_remove_comm; eauto.
      rewrite remove_mapsto_iff in *; eauto.
Qed.

Hint Resolve SameValues_remove_SCA : SameValues_db.

Lemma CompileDeallocSCA_discretely :
  forall {av} (tenv tenv': Telescope av) ext env k (v: Comp W) prog,
    k ∉ ext ->
    NotInTelescope k tenv ->
    {{ [[`k <~~ v as _]] :: tenv }} prog {{ [[`k <~~ v as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[`k <~~ v as _]] :: tenv }} prog {{ tenv' }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma ProgOk_Chomp_Some_snd :
  forall {av A T} `{FacadeWrapper (Value av) A} `{FacadeWrapper (Value av) T} env key value k (v': Comp T) prog
    (tail1: A -> Telescope av)
    (tail2: A -> Telescope av)
    ext,
    key ∉ ext ->
    (forall v: A, value ↝ v -> {{ tail1 v }} prog {{ Cons (NTSome k) v' (fun _ => tail2 v) }} ∪ {{ [key <-- wrap v] :: ext }} // env) ->
    ({{ Cons (NTSome key) value tail1 }} prog {{ Cons (NTSome k) v' (fun _ => Cons (NTSome key) value tail2) }} ∪ {{ ext }} // env).
Proof.
  intros.
  rewrite TelEq_swap.
  apply ProgOk_Chomp_Some; eauto.
Qed.

Lemma ProgOk_Chomp_None_snd :
  forall {av A T} `{FacadeWrapper (Value av) T} env key value prog
    (tail1: A -> Telescope av)
    (tail2: A -> Telescope av)
    ext k (v': Comp T),
    key ∉ ext ->
    (forall v: A, value ↝ v -> {{ tail1 v }} prog {{ Cons (NTSome k) v' (fun _ => tail2 v) }} ∪ {{ ext }} // env) ->
    ({{ Cons NTNone value tail1 }} prog {{ Cons (NTSome k) v' (fun _ => Cons NTNone value tail2) }} ∪ {{ ext }} // env).
Proof.
  intros.
  rewrite TelEq_swap.
  apply ProgOk_Chomp_None; eauto.
Qed.

Lemma CompileCallFacadeImplementationOfMutation_ADT_Replace_strong:
  forall {av Targ Tadt} `{FacadeWrapper av Tadt} `{FacadeWrapper av Targ} {env} fADT,
  forall fpointer varg vtmp (arg: Targ) (target: Tadt) tenv tenv',
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation_ADT Targ Tadt fADT)) env ->
    forall vret ext pArg pCoda,
      PreconditionSet tenv ext [[[varg; vtmp; vret]]] ->
      {{ [[ `vret <-- target as _]] :: tenv }}
        pArg
        {{ [[ `vret <-- target as _]] :: [[ `varg <-- arg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[ `vret <-- (fADT arg target) as _]] :: tenv }}
        pCoda
        {{ [[ `vret <-- (fADT arg target) as _]] :: tenv' }} ∪ {{ ext }} // env ->
      {{ [[ `vret <-- target as _]] :: tenv }}
        Seq (Seq pArg (Call vtmp fpointer (vret :: varg :: nil))) pCoda
        {{ [[ `vret <-- (fADT arg target) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros; hoare.
  apply CompileCallFacadeImplementationOfMutation_ADT_Replace; PreconditionSet_t; eauto.
Qed.

Lemma CompileCallFacadeImplementationOfMutation_SCA_Replace_strong:
  forall {av Tadt} `{FacadeWrapper av Tadt} {env} fADT,
  forall fpointer varg vtmp (arg: W) (target: Tadt) tenv tenv',
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation_SCA Tadt fADT)) env ->
    forall vret ext pArg pCoda,
      PreconditionSet tenv ext [[[varg; vtmp; vret]]] ->
      {{ [[ `vret <-- target as _]] :: tenv }}
        pArg
        {{ [[ `vret <-- target as _]] :: [[ `varg <-- arg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[ `vret <-- (fADT arg target) as _]] :: tenv }}
        pCoda
        {{ [[ `vret <-- (fADT arg target) as _]] :: tenv' }} ∪ {{ ext }} // env ->
      {{ [[ `vret <-- target as _]] :: tenv }}
        Seq (Seq pArg (Call vtmp fpointer (vret :: varg :: nil))) pCoda
        {{ [[ `vret <-- (fADT arg target) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros; hoare.
  apply CompileCallFacadeImplementationOfMutation_SCA_Replace; PreconditionSet_t; eauto.
Qed.

(* FIXME rename ProkOk_specialize_to_ret *)
(* FIXME Move stuff above *)

(* Ltac compile_chomp := *)
(*   match_ProgOk *)
(*     ltac:(fun prog pre post ext env => *)
(*             match pre with    (* FIXME could be generalized beyond the first binding *) *)
(*             | Cons ?k ?v ?tenv => *)
(*               match post with *)
(*               | Cons k v _ => fail 1 *)
(*               | context[Cons k v _] => move_to_front k *)
(*               end *)
(*             end). *)

Ltac _compile_map :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            let vhead := gensym "head" in
            let vhead' := gensym "head'" in
            let vtest := gensym "test" in
            let vtmp := gensym "tmp" in
            match constr:(pre, post) with
            | (Cons (NTSome ?vseq) (ret ?seq) ?tenv, Cons (NTSome ?vret) (ret (revmap _ ?seq')) ?tenv') =>
              unify seq seq';
                first [
                    apply (CompileMapAlloc_SCA seq (vhead := vhead) (vhead' := vhead') (vtest := vtest) (vtmp := DummyArgument vtmp)) |
                    apply (CompileMapAlloc_ADT seq (vhead := vhead) (vhead' := vhead') (vtest := vtest) (vtmp := DummyArgument vtmp)) ]
            end).

Ltac _compile_chomp :=         (* This is a weak version of the real compile_chomp, which is too slow *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | (Cons ?k ?v ?tenv, Cons ?k' ?v' ?tenv') =>
              unify k k'; unify v v';
              match k with
              | NTNone => apply ProgOk_Chomp_None
              | _ => apply ProgOk_Chomp_Some
              end
            | (Cons ?k ?v ?tenv, Cons _ _ (fun _ => Cons ?k' ?v' ?tenv')) =>
              unify k k'; unify v v';
              match k with
              | NTNone => apply ProgOk_Chomp_None_snd
              | _ => apply ProgOk_Chomp_Some_snd
              end
            end).

Ltac tenv_mentions env v :=
  first [ match env with
          | context[?vv] => first [ is_evar vv; fail 1
                                 | unify v vv; fail 2 ]
          | _ => idtac
          end; fail 1 | idtac ].

Ltac tenv_mentions_fast env v :=
  lazymatch v with
  | ?f => match env with context[f] => idtac end
  | ?f ?a => match env with context[f ?a'] => unify a a' end
  | ?f ?a ?b => match env with context[f ?a' ?b'] => unify a a'; unify b b' end
  | ?f ?a ?b ?c => match env with context[f ?a' ?b' ?c'] => unify a a'; unify b b'; unify c c' end
  | ?f ?a ?b ?c ?d => match env with context[f ?a' ?b' ?c' ?d'] => unify a a'; unify b b'; unify c c'; unify d d' end
  end.

Ltac _compile_destructor_unsafe vtmp tenv tenv' :=
  (apply CompileDeallocSCA_discretely ||
   first [ unify tenv tenv';
           apply (CompileCallFacadeImplementationOfDestructor (vtmp := DummyArgument vtmp))
         | eapply CompileSeq;
           [ apply (CompileCallFacadeImplementationOfDestructor (vtmp := DummyArgument vtmp)) | ] ]);
  try compile_do_side_conditions.

Ltac _compile_destructor :=
  match_ProgOk
     ltac:(fun prog pre post ext env =>
             let vtmp := gensym "tmp" in
             match pre with
             | Cons _ ?v (fun _ => ?tenv) =>
               match tenv with
               | context[post] => _compile_destructor_unsafe vtmp tenv post
               | _ => unify tenv post; _compile_destructor_unsafe vtmp tenv post
               | _ => lazymatch v with
                 | ret ?vv => first [ tenv_mentions_fast post vv; fail 1
                                   | _compile_destructor_unsafe vtmp tenv post ]
                 | ?vv => first [ tenv_mentions_fast post vv; fail 1
                               | _compile_destructor_unsafe vtmp tenv post ]
                 end
               end
             end).

Ltac unifiable t1 t2 :=
  match constr:(true) with
  | _ => let pr := constr:(eq_refl t1 : t1 = t2) in
        constr:true
  | _ => constr:false
  end.

Ltac is_sca_comp v :=
  match type of v with
  | Comp ?w => let r := unifiable w W in constr:r
  end.

Ltac _compile_destructor ::=
    match_ProgOk
      ltac:(fun prog pre post ext env =>
              let vtmp := gensym "tmp" in
              match pre with
              | Cons (NTSome ?k) ?v (fun _ => ?tenv) =>
                match tenv with
                | context[post] => (* post is a suffix of pre *)
                  _compile_destructor_unsafe vtmp tenv post
                | _ => (* post is pre *)
                  unify tenv post; _compile_destructor_unsafe vtmp tenv post
                | _ => let is_sca := is_sca_comp v in
                      lazymatch is_sca with
                      | true => (match post with
                                | context[k] => fail 1
                                | _ => apply CompileDeallocSCA_discretely
                                end)
                      | false => (lazymatch v with
                                  | ret ?vv => first [ tenv_mentions_fast post vv; fail 1
                                                    | _compile_destructor_unsafe vtmp tenv post ]
                                  | ?vv => first [ tenv_mentions_fast post vv; fail 1
                                                | _compile_destructor_unsafe vtmp tenv post ]
                                  end)
                      end
                end
              end).

Ltac _compile_skip :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | (?tenv, ?tenv') => not_evar tenv; not_evar tenv'; unify tenv tenv'; apply CompileSkip
            end).

Ltac _compile_if :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | (_, Cons _ (if _ then _ else _) _) =>
              let vtest := gensym "test" in
              apply (CompileIf (tmp := vtest))
            end).

Ltac __compile_prepare_chomp tenv tenv' :=
  match tenv with
  | Cons ?k ?v _ =>
    match tenv' with
    | Cons ?k' ?v' _ =>
      unify k k'; unify v v';
      fail 1 (* Nothing to do: can already chomp *)
    | Cons _ _ (fun _ => ?tail) =>
      unify tenv tail; idtac;
      fail 1 (* This is a job for deallocation, not chomping *)
    | context[Cons k v _] =>
      move_to_front k
    end
  end.

Ltac _compile_prepare_chomp :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            is_evar prog;
            first [ __compile_prepare_chomp pre post
                  | __compile_prepare_chomp post pre ]).

Ltac useless_binder term :=
  lazymatch term with
  | (fun _ => ?body) => let capture := body in idtac
  end.

Ltac _compile_rewrite_bind :=
  (* setoid_rewrite at the speed of light *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | context[Cons ?k (ret _) ?tail] =>
              first [ useless_binder tail; fail 1 |
                      match k with
                      | NTSome _ => setoid_rewrite Propagate_ret
                      | NTNone => setoid_rewrite Propagate_anonymous_ret
                      end ]
            | context[Cons _ (Bind _ _) _] => setoid_rewrite SameValues_Fiat_Bind_TelEq
            end).

Ltac first_arg f :=
  match type of f with
  | ?a -> _ => a
  end.

Ltac _compile_mutation :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | [[`?s <-- ?f _ _ as _]]::?tenv =>
              let arg := gensym "arg" in
              let tmp := gensym "tmp" in
              let fst := first_arg f in
              let uses_sca := unifiable fst W in
              lazymatch uses_sca with
              | true => match pre with
                       | context[Cons (NTSome s) _ _] =>
                         move_to_front s;
                           first [ eapply (CompileCallFacadeImplementationOfMutation_SCA (vtmp:=DummyArgument tmp))
                                 | eapply (CompileCallFacadeImplementationOfMutation_SCA_Replace (varg:=arg) (vtmp:=DummyArgument tmp))
                                 | eapply (CompileCallFacadeImplementationOfMutation_SCA_Replace_strong (varg:=arg) (vtmp:=DummyArgument tmp))
                                 | fail 1 ]
                       | tenv => eapply (CompileCallFacadeImplementationOfMutation_SCA_Alloc (varg:=arg) (vtmp:=DummyArgument tmp))
                       end
              | false => match pre with
                        | context[Cons (NTSome s) _ _] =>
                          move_to_front s;
                            first [ eapply (CompileCallFacadeImplementationOfMutation_ADT (vtmp:=DummyArgument tmp))
                                  | eapply (CompileCallFacadeImplementationOfMutation_ADT_Replace (varg:=arg) (vtmp:=DummyArgument tmp))
                                  | eapply (CompileCallFacadeImplementationOfMutation_ADT_Replace_strong (varg:=arg) (vtmp:=DummyArgument tmp))
                                  | fail 1 ]
                        | tenv => eapply (CompileCallFacadeImplementationOfMutation_ADT_Alloc (varg:=arg) (vtmp:=DummyArgument tmp))
                        end
              end; ensure_all_pointers_found
            end).

Ltac _compile_constructor :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | (?tenv, [[?s <-- ?adt as _]]::?tenv') =>
              match type of adt with
              | W => fail 1
              | _ => call_tactic_after_moving_head_binding_to_separate_goal
                      ltac:(apply CompileCallFacadeImplementationOfConstructor);
                  ensure_all_pointers_found
              end
            end).
Ltac _compile_loop :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            let vtest := gensym "test" in
            let vhead := gensym "head" in
            match constr:(pre, post) with
            | ([[`?vinit <~~ ?init as _]] :: [[`?vseq <-- ?seq as _]] :: ?tenv, [[`?vret <~~ fold_left _ ?seq ?init as _]] :: ?tenv') =>
              apply (CompileLoop seq init (vtest := vtest) (vhead := vhead))
            | ([[`?vinit <-- ?init as _]] :: [[`?vseq <-- ?seq as _]] :: ?tenv, [[`?vret <-- fold_left _ ?seq ?init as _]] :: ?tenv') =>
              apply (CompileLoop_ret seq init (vtest := vtest) (vhead := vhead))
            | ([[`?vseq <-- ?seq as _]] :: ?tenv, [[`?vret <~~ fold_left _ ?seq _ as _]] :: ?tenv') =>
              apply (CompileLoopAlloc (vtest := vtest) (vhead := vhead))
            | ([[`?vseq <-- ?seq as _]] :: ?tenv, [[`?vret <-- fold_left _ ?seq _ as _]] :: ?tenv') =>
              apply (CompileLoopAlloc_ret (vtest := vtest) (vhead := vhead))
            end).

(* Ltac compile_miniChomp := *)
(*   match_ProgOk *)
(*     ltac:(fun prog pre post ext env => *)
(*             match post with *)
(*             | Cons NTNone ?v ?tenv' => *)
(*               match pre with *)
(*               | context[Cons ?k v _] => *)
(*                 move_to_front k; *)
(*                   apply miniChomp' *)
(*               end *)
(*             end). *)

Ltac start_compiling :=
  match goal with
  | |- sigT _ => eexists; intros
  end.                        (* FIXME format of progOk notation *)

Ltac _compile_rewrite_if :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | appcontext [if ?b then ?x else ?y] => is_dec b; setoid_rewrite (dec2bool_correct b x y)
            | appcontext [?f (if ?b then ?x else ?y)] => is_pushable_head_constant f; setoid_rewrite (push_if f x y b)
            end).

Ltac _compile_early_hook := fail.
Ltac _compile_late_hook := fail.

Ltac _compile_step :=
  match goal with
  | _ => start_compiling
  | _ => progress subst
  | _ => progress intros
  | _ => progress computes_to_inv
  | _ => compile_do_side_conditions
  | _ => _compile_early_hook
  | _ => _compile_rewrite_bind
  | _ => _compile_skip
  | _ => _compile_map
  | _ => _compile_loop
  (* | _ => _compile_CallBagFind *)
  (* | _ => _compile_CallBagInsert *)
  (* | _ => _compile_CallGetAttribute *)
  | _ => _compile_chomp
  | _ => _compile_prepare_chomp
  | _ => _compile_if
  | _ => _compile_mutation
  | _ => _compile_constructor
  | _ => compile_simple
  | _ => _compile_destructor
  | _ => _compile_rewrite_if
  | _ => _compile_late_hook
  (* | _ => progress simpl *)
  end.

Ltac _compile :=
  repeat _compile_step.

Ltac compile_do_side_conditions_internal ::=
  repeat cleanup; PreconditionSet_t;
   match goal with
   | _ => exact I
   | |- _ <> _ => discriminate 1
   | |- _ ∉ _ => decide_not_in
   | |- NotInTelescope _ _ => decide_NotInTelescope
   | |- StringMap.find _ _ = Some _ => decide_mapsto_maybe_instantiate
   | |- StringMap.MapsTo _ _ _ => decide_mapsto_maybe_instantiate
   | |- GLabelMap.MapsTo _ _ _ => GLabelMapUtils.decide_mapsto_maybe_instantiate
   end.

Opaque DummyArgument.
Opaque Word.wordToNat.
Opaque Word.natToWord.
Opaque nat_as_constant nat_as_word string_as_var.

Definition Microbenchmarks_Carrier : Type := sum (list W) (list (list W)).

Definition Microbenchmarks_Env : Env Microbenchmarks_Carrier :=
  (GLabelMap.empty (FuncSpec _))
    ### ("std", "rand") ->> (Axiomatic FRandom)
    ### ("list", "nil") ->> (Axiomatic (FacadeImplementationOfConstructor (list W) nil))
    ### ("list[W]", "push") ->> (Axiomatic (FacadeImplementationOfMutation_SCA (list W) cons))
    ### ("list[W]", "pop") ->> (Axiomatic (List_pop W))
    ### ("list[W]", "delete") ->> (Axiomatic (FacadeImplementationOfDestructor (list W)))
    ### ("list[W]", "empty?") ->> (Axiomatic (List_empty W))
    ### ("list[list[W]]", "nil") ->> (Axiomatic (FacadeImplementationOfConstructor (list (list W)) nil))
    ### ("list[list[W]]", "push") ->> (Axiomatic (FacadeImplementationOfMutation_ADT (list W) (list (list W)) cons))
    ### ("list[list[W]]", "pop") ->> (Axiomatic (List_pop (list W)))
    ### ("list[list[W]]", "delete") ->> (Axiomatic (FacadeImplementationOfDestructor (list (list W))))
    ### ("list[list[W]]", "empty?") ->> (Axiomatic (List_empty (list W))).

Notation "'ParametricExtraction' '#vars' x .. y '#program' post '#arguments' pre '#env' env '#carrier' carrier" :=
  (sigT (fun prog => (forall x, .. (forall y, {{ pre }} prog {{ [[`"out" <~~ post as _]]::Nil }} ∪ {{ ∅ }} // (env: Env carrier)) ..)))
    (at level 200,
     x binder,
     y binder,
     format "'ParametricExtraction' '//'    '#vars'       x .. y '//'    '#program'     post '//'    '#arguments'  pre '//'    '#env'        env '//'    '#carrier'    carrier").

Notation "'ParametricExtraction' '#vars' x .. y '#program' post '#arguments' pre '#env' env" :=
  (sigT (fun prog => (forall x, .. (forall y, {{ pre }} prog {{ [[`"out" <~~ post as _]]::Nil }} ∪ {{ ∅ }} // env) ..)))
    (at level 200,
     x binder,
     y binder,
     format "'ParametricExtraction' '//'    '#vars'       x .. y '//'    '#program'     post '//'    '#arguments'  pre '//'    '#env'         env").

Notation "'ParametricExtraction' '#program' post '#env' env" :=
  (sigT (fun prog => {{ Nil }} prog {{ [[`"out" <~~ post as _]]::Nil }} ∪ {{ ∅ }} // env))
    (at level 200,
     format "'ParametricExtraction' '//'    '#program'  post '//'    '#env'      env").

Notation "'FacadeMethod' '#prog' prog '#requires' pre '#ensures' post '#ext' ext '#env' env" :=
  ({{ pre }} prog {{ post }} ∪ {{ ext }} // env)
    (at level 200,
     format "'FacadeMethod' '//'    '#prog'      prog '//'    '#requires'  pre '//'    '#ensures'   post '//'    '#ext'       ext '//'    '#env'       env").

Example micro_plus :
  ParametricExtraction
    #vars      x y
    #program   ret (Word.wplus x y)
    #arguments [[`"x" <-- x as _ ]] :: [[`"y" <-- y as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_plus).

Example micro_plus_minus :
  ParametricExtraction
    #vars      x y
    #program   ret (Word.wplus x (Word.wminus y x))
    #arguments [[`"x" <-- x as _ ]] :: [[`"y" <-- y as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  repeat (_compile_step || apply ProgOk_Chomp_Some_snd).
Defined.

Time Eval lazy in (extract_facade micro_plus_minus).

Example micro_min :
  ParametricExtraction
    #vars      x y
    #program   ret (if Word.wlt_dec x y then x else y)
    #arguments [[`"x" <-- x as _ ]] :: [[`"y" <-- y as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_min).

Example micro_max :
  ParametricExtraction
    #vars      x y
    #program   ret (if Word.wlt_dec x y then y else x)
    #arguments [[`"x" <-- x as _ ]] :: [[`"y" <-- y as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_max).

Example micro_squared_max :
  ParametricExtraction
    #vars      x y
    #program   ret (if Word.wlt_dec x y then Word.wmult y y else Word.wmult x x)
    #arguments [[`"x" <-- x as _ ]] :: [[`"y" <-- y as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_squared_max).

Example micro_make_singleton :
  ParametricExtraction
    #vars      x y
    #program   ret (x :: y :: nil)
    #arguments [[`"x" <-- x as _ ]] :: [[`"y" <-- y as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_make_singleton).

Example micro_duplicate_word :
  ParametricExtraction
    #vars      x
    #program   ret (x :: x :: nil)
    #arguments [[`"x" <-- x as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_duplicate_word).

Example micro_sort_pair_1 :
  ParametricExtraction
    #vars      x y
    #program   ret (if Word.wlt_dec x y then x :: y :: nil else y :: x :: nil)
    #arguments [[`"x" <-- x as _ ]] :: [[`"y" <-- y as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_sort_pair_1).

Example micro_sort_pair_2 :
  ParametricExtraction
    #vars      x y
    #program   ret ((if Word.wlt_dec x y then x else y) :: (if Word.wlt_dec x y then y else x) :: nil)
    #arguments [[`"x" <-- x as _ ]] :: [[`"y" <-- y as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_sort_pair_2).

Example micro_double :
  ParametricExtraction
    #vars      seq
    #program   ret (revmap (fun w => Word.wmult w 2) seq)
    #arguments [[`"seq" <-- seq as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.                               (* FIXME prove something for maps *)
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_double).

Example micro_fold_plus :
  ParametricExtraction
    #vars      seq
    #program   ret (fold_left (@Word.wplus 32) seq 0)
    #arguments [[`"seq" <-- seq as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
  instantiate (1 := Skip).
  admit.
  (* let fop := translate_op Word.wplus in (* FIXME *) *)
  (* apply (CompileBinopOrTest_right_inPlace fop); compile_do_side_conditions. *)
Defined.

Time Eval lazy in (extract_facade micro_fold_plus).

Example micro_fold_plus_x :
  ParametricExtraction
    #vars      seq x
    #program   ret (fold_left (@Word.wplus 32) seq x)
    #arguments [[`"seq" <-- seq as _ ]] :: [[`"x" <-- x as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
  instantiate (1 := Skip).
  admit.
  (* let fop := translate_op Word.wplus in (* FIXME *) *)
  (* apply (CompileBinopOrTest_right_inPlace fop); compile_do_side_conditions. *)
Defined.

Time Eval lazy in (extract_facade micro_fold_plus_x).

Lemma List_rev_as_fold_generalized :
  forall A l init,
    @List.rev A l ++ init = fold_left (fun acc x => x :: acc) l init.
Proof.
  induction l; simpl; intros; [ | rewrite <- IHl, <- app_assoc ]; reflexivity.
Qed.

Lemma List_rev_as_fold :
  forall A l, @List.rev A l = fold_left (fun acc x => x :: acc) l nil.
Proof.
  intros; rewrite <- (List_rev_as_fold_generalized _ nil), app_nil_r; reflexivity.
Qed.

Ltac _compile_early_hook ::= rewrite List_rev_as_fold.

Example micro_fold_reverse :
  ParametricExtraction
    #vars      seq
    #program   ret (List.rev seq)
    #arguments [[`"seq" <-- seq as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_fold_reverse).

Example micro_fold_flatten_rev :
  ParametricExtraction
    #vars      seqs
    #program   ret (fold_left (fun acc seq => fold_left (fun acc' x => x :: acc') seq acc) seqs nil)
    #arguments [[`"seqs" <-- seqs as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_fold_flatten_rev).

Lemma ProgOk_Remove_Skip_L :
  forall {av} ext (t1 t2: Telescope av) env prog,
    {{ t1 }} (Seq Skip prog) {{ t2 }} ∪ {{ ext }} // env ->
    {{ t1 }} prog {{ t2 }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
  learn (RunsToSkip env (Equal_refl initial_state)); eauto.
  learn (RunsToSeq (RunsToSkip _ (Equal_refl _)) H1); eauto.
Qed.

Lemma ProgOk_Remove_Skip_R :
  forall {av} ext (t1 t2: Telescope av) env prog,
    {{ t1 }} (Seq prog Skip) {{ t2 }} ∪ {{ ext }} // env ->
    {{ t1 }} prog {{ t2 }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
  learn (RunsToSeq H1 (RunsToSkip _ (Equal_refl _))); eauto.
Qed.

Lemma ProgOk_Transitivity_Name_SCA :
  forall {av} k env ext t1 (t2: W -> Telescope av) prog1 (v: Comp W),
    {{ t1 }} prog1 {{ [[`k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ t1 }} prog1 {{ [[v as kk]]::t2 kk }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
  eauto using SameValues_Dealloc_SCA.
Qed.

Ltac _compile_random :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | (?tenv, Cons ?k Random ?tenv') =>
              match k with
              | NTNone => let vrandom := gensym "random" in
                         apply ProgOk_Transitivity_Name_SCA with vrandom
              | _ => idtac
              end;
                first [ call_tactic_after_moving_head_binding_to_separate_goal ltac:(apply CompileCallRandom)
                      | apply miniChomp'; apply CompileDeallocSCA_discretely ]
            end).

Ltac _compile_early_hook ::= _compile_random.

Example micro_pick_random :
  ParametricExtraction
    #program Random
    #env     Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_pick_random).

Example micro_sum_random :
  ParametricExtraction
    #program ( r1 <- Random;
               r2 <- Random;
               ret (Word.wplus r1 r2) )
    #env     Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_sum_random).

(* FIXME loops on zips? *)

Example micro_randomize :
  ParametricExtraction
    #vars      seq: list W
    #program   fold_left (fun acc elem => ( a <- acc;
                                         r <- Random;
                                         ret (r :: a) )%comp) seq (ret nil)
    #arguments [[`"seq" <-- seq as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
  apply miniChomp'.             (* FIXME *)
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_randomize).

Example micro_double_larger_than_random :
  ParametricExtraction
    #vars      seq
    #program   ( threshold <- Random;
                 ret (revmap (fun w => if Word.wlt_dec threshold w then Word.wmult w 2 else w) seq) )
    #arguments [[`"seq" <-- seq as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.                               (* FIXME prove something for maps *)
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_double_larger_than_random).

Example micro_drop_larger_than_random :
  ParametricExtraction
    #vars      seq
    #program   ( threshold <- Random;
                 ret (fold_left (fun acc w => if Word.wlt_dec threshold w then acc else w :: acc) seq nil) )
    #arguments [[`"seq" <-- seq as _ ]] :: Nil
    #env       Microbenchmarks_Env.
Proof.
  _compile.
Defined.

Time Eval lazy in (extract_facade micro_drop_larger_than_random).
