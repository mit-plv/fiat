Require Import Common Computation ADT Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

(* Specification of mutator method. *)
Definition mutatorMethodSpec (Ty : Type) :=
  Ty    (* Initial model *)
  -> nat (* Actual argument*)
  -> Ty (* Final Model *)
  -> Prop.

(* Specification of an observer method *)
Definition observerMethodSpec (Ty : Type) :=
  Ty    (* Initial model *)
  -> nat (* Actual argument*)
  -> nat (* Return value *)
  -> Prop.

(** Every spec is trivially implementable using [Pick]. *)
Section pick.
  Variable rep : Type.
  Variable mutatorMethodIndex : Type.
  Variable observerMethodIndex : Type.
  Variable mutatorMethodSpecs : mutatorMethodIndex -> mutatorMethodSpec rep.
  Variable observerMethodSpecs : observerMethodIndex -> observerMethodSpec rep.

  Local Obligation Tactic := econstructor; eauto.

  Program Definition pickImpl : ADT :=
    {|
      Rep := rep;
      RepInv m := True;
      MutatorIndex := mutatorMethodIndex;
      ObserverIndex := observerMethodIndex;
      MutatorMethods idx :=
        fun r x =>
          { r' : rep
          | mutatorMethodSpecs idx r x r'}%comp;
      ObserverMethods idx :=
        fun r n =>
          { n' : nat
          | observerMethodSpecs idx r n n'}%comp
    |}.

End pick.

Section MethodRefinement.
  Variables oldRep newRep : Type.
  (** Old and new representations **)

  Variable oldRepInv : Ensemble oldRep.
  Variable newRepInv : Ensemble newRep.
  (** Old and new representation invariants **)

  Variable abs : newRep -> Comp oldRep.
  (** Abstraction function *)

  (** Refinement of a mutator method: if we first do the new
      computation and then abstract, this is a refinement of first
      abstracting and then doing the old computation.  That is, the
      following diagram commutes:
<<
                   old mutator
       old rep --------------> old rep
          ↑                         ↑
      abs |                         | abs
          |                         |
       new rep --------------> new rep
                   new mutator
>>  *)

  Definition refineMutator
             (oldMutator : mutatorMethodType oldRep)
             (newMutator : mutatorMethodType newRep)
    := forall new_state n,
         newRepInv new_state ->
         refine (old_state <- abs new_state;
                 oldMutator old_state n)
                (new_state' <- newMutator new_state n;
                 abs new_state').

  (** Refinement of an observer method: the new computation should be
      a refinement of first abstracting and then doing the old
      computation.  That is, the following diagram should commute:
<<
                  old observer
       old rep --------------> ℕ
          ↑                      ∥
      abs |                      ∥ id
          |                      ∥
       new rep --------------> ℕ
                  new observer
>>
   *)
  Definition refineObserver
             (oldObserver : observerMethodType oldRep)
             (newObserver : observerMethodType newRep)
    := forall new_state n,
         newRepInv new_state ->
         refine (old_state <- abs new_state;
                 oldObserver old_state n)
                (newObserver new_state n).

  (**  Abstraction should preserve representation invariants:
       The abstraction of a new representation that satisfies its
       representation invariant should satisfy the old invariant.
       Diagrammatically,

  (Old RepInv holds)
      old rep
        ↑
        | abs
        |
       new rep
  (New RepInv holds)
   **)

  Definition absPreservesInv
    := forall new_state,
         newRepInv new_state ->
         computational_inv oldRepInv (abs new_state).

End MethodRefinement.

(** We map from old indices to new indices because every method that
    used to be callable should still be callable, and we don't care
    about the other methods. *)
Inductive refineADT (A B : ADT) : Prop :=
| refinesADT :
    forall abs mutatorMap observerMap,
      (forall idx, @refineMutator
                     (Rep A) (Rep B)
                     (RepInv B) abs
                     (MutatorMethods A idx)
                     (MutatorMethods B (mutatorMap idx)))
      -> (forall idx, @refineObserver
                     (Rep A) (Rep B)
                     (RepInv B) abs
                     (ObserverMethods A idx)
                     (ObserverMethods B (observerMap idx)))
      -> (@absPreservesInv (Rep A) (Rep B)
                 (RepInv A) (RepInv B) abs)
      -> refineADT A B.

(** We should always just unfold [refineMutator] and [refineObserver]
    into [refine], so that we can rewrite with lemmas about [refine]. *)
Arguments refineMutator / .
Arguments refineObserver / .
Arguments absPreservesInv / .

Instance refineMutator_refl rep repInv
: Reflexive (@refineMutator rep rep repInv (@Return _)).
Proof.
  intro; simpl; intros.
  autorewrite with refine_monad; reflexivity.
Qed.

Instance refineObserver_refl rep repInv
: Reflexive (@refineObserver rep rep repInv (@Return _)).
Proof.
  intro; simpl; intros.
  autorewrite with refine_monad; reflexivity.
Qed.

Global Instance refineADT_PreOrder : PreOrder refineADT.
Proof.
  split; compute in *.
  - intro x.
    econstructor 1 with
    (abs := @Return _)
      (mutatorMap := id)
      (observerMap := id);
      unfold id;
      try reflexivity.
    simpl; intros;
      inversion_by computes_to_inv; subst; eauto.
  - intros x y z
           [abs mutMap obsMap mutH obsH]
           [abs' mutMap' obsMap' mutH' obsH'].
    econstructor 1 with
    (abs := fun z => (z' <- abs' z; abs z')%comp)
    (mutatorMap := mutMap' ∘ mutMap)
    (observerMap := obsMap' ∘ obsMap);
    unfold id, compose; simpl in *; intros.
    + autorewrite with refine_monad.
      rewrite <- !refineEquiv_bind_bind, <- (mutH' _ _ _ H1).
      rewrite !refineEquiv_bind_bind.
      unfold refine; intros; inversion_by computes_to_inv.
      econstructor; eauto.
      eapply mutH; eauto.
    + autorewrite with refine_monad.
      rewrite <- !refineEquiv_bind_bind, <- (obsH' _ _ _ H1).
      rewrite !refineEquiv_bind_bind.
      unfold refine; intros; inversion_by computes_to_inv.
      econstructor; eauto.
      eapply obsH; eauto.
    + inversion_by computes_to_inv; eauto.
Qed.

Add Parametric Relation : ADT refineADT
    reflexivity proved by reflexivity
    transitivity proved by transitivity
      as refineADT_rel.

Add Parametric Morphism rep repInv mutIdx obsIdx mutInv
  : (fun ms os => @Build_ADT rep repInv mutIdx obsIdx ms os (mutInv ms))
  with signature
  (pointwise_relation _ (@refineMutator _ _ repInv (@Return _)))
    ==> (pointwise_relation _ (@refineObserver _ _ repInv (@Return _)))
    ==> refineADT
    as refineADT_Build_ADT.
Proof.
  intros.
  let A := match goal with |- refineADT ?A ?B => constr:(A) end in
  let B := match goal with |- refineADT ?A ?B => constr:(B) end in
  eapply (@refinesADT A B (@Return _) id id);
    unfold id, pointwise_relation in *; simpl in *; intros;
    auto; inversion_by computes_to_inv; subst; eauto.
Qed.

Add Parametric Morphism rep repInv mutIdx obsIdx ms mutInv
  : (fun os => @Build_ADT rep repInv mutIdx obsIdx ms os mutInv)
  with signature
    (pointwise_relation _ (@refineObserver _ _ repInv (@Return _)))
    ==> refineADT
    as refineADT_Build_ADT_observer_only.
Proof.
  intros.
  let A := match goal with |- refineADT ?A ?B => constr:(A) end in
  let B := match goal with |- refineADT ?A ?B => constr:(B) end in
  eapply (@refinesADT A B (@Return _) id id);
    unfold id, pointwise_relation in *; simpl in *; intros;
    auto; try inversion_by computes_to_inv; subst; eauto;
    autorewrite with refine_monad; reflexivity.
Qed.

(** If we had dependent setoid relations in [Type], then we could write

<<
Add Parametric Morphism : @Build_ADT
  with signature
  (fun oldM newM => newM -> Comp oldM)
    ==> arrow
    ==> arrow
    ==> (pointwise_relation _ (@refineMutator _ _ _))
    ==> (pointwise_relation _ (@refineObserver _ _ _))
    ==> refineADT
    as refineADT_Build_ADT.
Proof.
  ...
Qed.
>>

    But, alas, Matthieu is still working on those.  So the rewrite
    machinery won't work very well when we're switching reps, and
    we'll instead have to use [etransitivity] and [apply] things. *)

(* Given an abstraction function, we can transform the rep of a pickImpl ADT. *)

Section GeneralRefinements.

  Theorem refines_rep_pickImpl
          newRep oldRep
          (abs : newRep -> oldRep)
          MutatorIndex ObserverIndex
          ObserverSpec MutatorSpec :
    refineADT
      (@pickImpl oldRep MutatorIndex ObserverIndex MutatorSpec ObserverSpec)
      (@pickImpl newRep MutatorIndex ObserverIndex
                 (fun idx nm n nm' => MutatorSpec idx (abs nm) n (abs nm'))
                 (fun idx nm => ObserverSpec idx (abs nm))).
  Proof.
    econstructor 1 with (abs := fun nm => Return (abs nm))
                          (mutatorMap := @id MutatorIndex)
                          (observerMap := @id ObserverIndex);
    compute; intros; inversion_by computes_to_inv; subst; eauto.
  Qed.

  Open Scope comp_scope.

  Section addCache.

  (* We can cache an observer value by refining the rep and the mutators. *)

    Variable rep observerIndex : Type.
    Variable ObserverIndex_eq : forall idx idx' : observerIndex,
                                  {idx = idx'} + {idx <> idx'}.

    Notation "x == y" := (ObserverIndex_eq x y) (at level 36).
    Record cachedObservers := cOb
      { origRep : rep;
        observerCache : observerIndex -> option (nat -> nat)}.

    (* A cache is well-formed if it refines all the observer methods
     included in the [cachedSet]. *)
    Definition ValidCache (cachedSet : observerIndex -> bool) ObserverMethods
               (r : cachedObservers) :=
      forall idx,
        if cachedSet idx then
          exists func,
            observerCache r idx = Some func /\
            forall n, refine (ObserverMethods idx (origRep r) n) (ret (func n))
        else
          observerCache r idx = None.
    Arguments ValidCache _ ObserverMethods r / .

    Variable RepInv : Ensemble rep. (* The old Representation Invariant *)
    Definition AddValidCacheInv cachedSet ObserverMethods
               (r : cachedObservers) :=
      RepInv (origRep r) /\ ValidCache cachedSet ObserverMethods r.
    Arguments AddValidCacheInv _ ObserverMethods r / .

    (* Inserting and removing indices from the [cachedSet] *)
    Definition insertCachedSet cachedSet cachedIndex (idx : observerIndex) : bool :=
      if (idx == cachedIndex) then
        true
      else
        cachedSet idx.

    Definition removeCachedSet cachedSet cachedIndex (idx : observerIndex) : bool :=
      if (idx == cachedIndex) then
        false
      else
        cachedSet idx.

    Arguments insertCachedSet _ _ idx / .
    Arguments removeCachedSet _ _ idx / .

    (* To implement the cache, we update an ADT's mutators to include cached
       values, one observer index at a time. There are two cases:

       1. If the observer index is not already in the cache, it is cached
          by running the old mutators with just the old cached values. *)

    Definition removeCachedValue cachedIndex cachedRep
    : cachedObservers :=
      {| origRep := origRep cachedRep;
         observerCache idx := if idx == cachedIndex then None else observerCache cachedRep idx |}.
    Arguments removeCachedValue _ _ / .

    Definition AddCachedValue cachedIndex cachedRep cachedFunc
    : cachedObservers :=
      {| origRep := origRep cachedRep;
         observerCache idx :=
           if idx == cachedIndex then
             Some (cachedFunc cachedRep)
           else observerCache cachedRep idx |}.
    Arguments AddCachedValue _ _ _ / .

    Definition AddCachedObv
               {MutatorIndex}
               (MutatorMethods : MutatorIndex -> mutatorMethodType cachedObservers)
               (cachedIndex : observerIndex) (* Index of the Observer to Cache *)
               (cachedFunc : cachedObservers -> nat -> nat)
               idx m n :=
      om <- MutatorMethods idx (removeCachedValue cachedIndex m) n;
      ret (AddCachedValue cachedIndex om cachedFunc).

    (* 2. If the observer index *is* already in the cache, it is recached
          by running the old mutators and then updating the cache of the result
          (potentially using the initial cache value). *)
    Definition UpdateCachedObv
               {MutatorIndex}
               (MutatorMethods : MutatorIndex -> mutatorMethodType cachedObservers)
               (cachedIndex : observerIndex) (* Index of the Observer to Cache *)
               (cachedFunc : cachedObservers -> cachedObservers -> nat -> nat)
               idx m n :=
      om <- MutatorMethods idx m n;
      ret (AddCachedValue cachedIndex om (cachedFunc m)).

    (* [AddValidCacheInv] is preservered under several updates to the cached values. *)

    Lemma RemoveValidCacheInv
    : forall cachedSet cachedIndex ObserverMethods r
             (NInCachedSet : cachedSet cachedIndex = false),
        AddValidCacheInv (insertCachedSet cachedSet cachedIndex) ObserverMethods r ->
        AddValidCacheInv cachedSet
                         ObserverMethods
                         (removeCachedValue cachedIndex r).
    Proof.
      simpl; intros; intuition.
      generalize (H1 idx); destruct (idx == cachedIndex); subst; eauto;
      try rewrite NInCachedSet; eauto.
    Qed.
    Hint Resolve RemoveValidCacheInv.

    Lemma AddValidCacheInv'
    : forall cachedSet cachedIndex ObserverMethods r cachedFunc
             (NInCachedSet : cachedSet cachedIndex = false)
             (refines_cached : forall r n,
                                 refine (ObserverMethods cachedIndex (origRep r) n)
                                        (ret (cachedFunc r n)))
             (RepInvr : AddValidCacheInv cachedSet ObserverMethods r),
        AddValidCacheInv (insertCachedSet cachedSet cachedIndex) ObserverMethods
                         (AddCachedValue cachedIndex r cachedFunc).
    Proof.
      simpl; intros; intuition.
      generalize (H0 idx); intros; destruct (ObserverIndex_eq idx cachedIndex);
      subst; eauto.
    Qed.

    Lemma UpdateValidCacheInv
    : forall cachedSet cachedIndex ObserverMethods (r m : cachedObservers) cachedFunc
             (InCachedSet : cachedSet cachedIndex = true)
             (refines_cached : forall n, refine (ObserverMethods cachedIndex (origRep r) n)
                                        (ret (cachedFunc m r n))),
      AddValidCacheInv cachedSet ObserverMethods r ->
      observerCache r cachedIndex = Some (cachedFunc m r) ->
      AddValidCacheInv cachedSet ObserverMethods
                       (AddCachedValue cachedIndex r (cachedFunc m)).
    Proof.
      simpl; intros; intuition.
      generalize (H2 idx); intros.
      destruct (ObserverIndex_eq idx cachedIndex); subst; eauto.
      rewrite InCachedSet in *|-*; eauto.
    Qed.

    Hint Resolve UpdateValidCacheInv.
    Hint Resolve RemoveValidCacheInv.
    Hint Resolve AddValidCacheInv'.

    (* Both approaches to updating mutators continue to satisfy the [AddValidCacheInv]
       invariant.
       1. If the index is not already cached: *)

    (* Removing a cached value from a well-formed cache will produce
       another well-formed cache value *)

    Lemma AddCachedInv
          {MutatorIndex cachedSet}
          ObserverMethods MutatorMethods
          (cachedIndex : observerIndex)
          (NInCachedSet : cachedSet cachedIndex = false)
          cachedFunc
          (refines_cached : forall r n,
                              refine (ObserverMethods cachedIndex (origRep r) n)
                                     (ret (cachedFunc r n)))
    : (forall idx  r n, AddValidCacheInv cachedSet ObserverMethods r ->
                        computational_inv (AddValidCacheInv cachedSet ObserverMethods)
                                          (MutatorMethods idx r n)) ->
      forall (idx : MutatorIndex) r n,
        AddValidCacheInv (insertCachedSet cachedSet cachedIndex) ObserverMethods r ->
        computational_inv
          (AddValidCacheInv (insertCachedSet cachedSet cachedIndex) ObserverMethods)
          (AddCachedObv MutatorMethods cachedIndex cachedFunc
                            idx r n).
    Proof.
      unfold AddCachedObv, computational_inv; intros.
      apply_in_hyp computes_to_inv; destruct_ex; intuition;
      apply_in_hyp computes_to_inv; destruct_ex; subst; eauto.
    Qed.

    (* 2. If the index is already cached: *)

    Lemma UpdateCachedInv
          {MutatorIndex cachedSet}
          ObserverMethods MutatorMethods
          (cachedIndex : observerIndex)
          (InCachedSet : cachedSet cachedIndex = true)
          cachedFunc
          (FuncEqv :
             forall idx r n,
               AddValidCacheInv cachedSet ObserverMethods r ->
               computational_inv
                 (fun r' => observerCache r' cachedIndex = Some (cachedFunc r r'))
                 (MutatorMethods idx r n))
          (refines_cached : forall m r n,
                              AddValidCacheInv cachedSet ObserverMethods m ->
                              AddValidCacheInv cachedSet ObserverMethods r ->
                              observerCache r cachedIndex = Some (cachedFunc m r) ->
                              refine (ObserverMethods cachedIndex (origRep r) n)
                                     (ret (cachedFunc m r n)))
    : (forall idx  r n, AddValidCacheInv cachedSet ObserverMethods r ->
                        computational_inv (AddValidCacheInv cachedSet ObserverMethods)
                                          (MutatorMethods idx r n)) ->
      forall (idx : MutatorIndex) r n,
        AddValidCacheInv cachedSet ObserverMethods r ->
        computational_inv
          (AddValidCacheInv cachedSet ObserverMethods)
          (UpdateCachedObv MutatorMethods cachedIndex cachedFunc idx r n).
    Proof.
      unfold UpdateCachedObv, computational_inv; intros.
      unfold computational_inv in FuncEqv.
      apply_in_hyp computes_to_inv; destruct_ex; intuition;
      apply_in_hyp computes_to_inv; destruct_ex; subst; eapply UpdateValidCacheInv; eauto.
    Qed.

  End addCache.

  Arguments ValidCache _ _ _ _ _ / .

  (* Adding the empty cache to an ADT. *)
  Program Definition addCache adt : ADT :=
    {| Rep := cachedObservers (Rep adt) (ObserverIndex adt);
       RepInv := AddValidCacheInv (RepInv adt) (fun _ => false) (ObserverMethods adt);
       ObserverIndex := ObserverIndex adt;
       MutatorIndex := MutatorIndex adt;
       ObserverMethods idx r n :=
         ObserverMethods adt idx (origRep r) n;
       MutatorMethods idx r n :=
         om <- MutatorMethods adt idx (origRep r) n;
       ret {| origRep := om;
              observerCache := fun _ => None |}
    |}.
  Next Obligation.
    inversion_by computes_to_inv; subst; unfold AddValidCacheInv in *|-*; simpl; intuition.
    eapply MutatorMethodsInv; eauto.
  Defined.

  Arguments addCache adt /.
  Arguments Rep _ /.

  (* Adding the empty cache is a valid refinement. *)
  Lemma refines_addCache : forall adt, refineADT adt (addCache adt).
  Proof.
    intros; destruct adt; simpl; econstructor 1 with
                          (abs := fun m : @cachedObservers Rep ObserverIndex =>
                                    ret (origRep m))
                            (mutatorMap := @id MutatorIndex)
                            (observerMap := @id ObserverIndex); simpl.
    - intros; autorewrite with refine_monad; rewrite refineEquiv_under_bind with (g := @Return _);
      intros; autorewrite with refine_monad; reflexivity.
    - intros; autorewrite with refine_monad; unfold id; intuition.
    - unfold AddValidCacheInv; intros; inversion_by computes_to_inv; subst; intuition.
  Qed.

  (* ADT which includes new cache value. *)

  Lemma refine_under_bind X Y (P : Ensemble X) (f g : X -> Comp Y) x y
        (compInv : computational_inv P x)
        (compInv' : computational_inv P y)
        (eqv_f_g : forall x, P x -> refine (f x) (g x))
        (refine_x_y : refine x y)
  : refine (Bind x f)
           (Bind y g).
  Proof.
    unfold refine; intros.
    inversion_by computes_to_inv; econstructor; eauto.
    eapply eqv_f_g; eauto.
  Qed.

  Definition addCachedObserver
          {Rep ObserverIndex MutatorIndex}
          (cachedSet : ObserverIndex -> bool)
          (repInv : Ensemble Rep)
          ObserverMethods
          (ObserverIndex_eq : forall idx idx' : ObserverIndex,
                                   {idx = idx'} + {idx <> idx'})
          (cachedIndex : ObserverIndex)
          NInCachedSet
          (MutatorMethods : MutatorIndex -> mutatorMethodType (cachedObservers Rep ObserverIndex))

          (MutatorMethodsInv :
             forall idx r n, AddValidCacheInv repInv cachedSet ObserverMethods r ->
                             computational_inv (AddValidCacheInv repInv cachedSet ObserverMethods)
                                       (MutatorMethods idx r n))
          cachedFunc
          refines_cached
  : ADT :=
    {| Rep := cachedObservers Rep ObserverIndex;
       RepInv := AddValidCacheInv repInv (insertCachedSet _ cachedSet cachedIndex)
                                  ObserverMethods;
       ObserverIndex := ObserverIndex;
       MutatorIndex := MutatorIndex;
       ObserverMethods idx r := ObserverMethods idx (origRep r);
       MutatorMethods idx r n :=
         AddCachedObv ObserverIndex_eq MutatorMethods cachedIndex cachedFunc idx
                          r n;
       MutatorMethodsInv :=
         @AddCachedInv Rep ObserverIndex ObserverIndex_eq repInv
                          MutatorIndex cachedSet ObserverMethods
                          MutatorMethods cachedIndex NInCachedSet cachedFunc refines_cached
                          MutatorMethodsInv
    |}.

  Hint Resolve UpdateValidCacheInv.
  Hint Resolve RemoveValidCacheInv.
  Hint Resolve AddValidCacheInv'.

  (* [addCachedObserver] from above is a valid refinement *)

  Lemma RemoveAddCachedValue
        {Rep ObserverIndex}
  : forall ObserverIndex_eq
           cachedSet
           (cachedIndex : ObserverIndex)
           (repInv : Ensemble Rep)
           ObserverMethods r cachedFunc
           (NInCachedSet : cachedSet cachedIndex = false),
          AddValidCacheInv repInv cachedSet ObserverMethods r ->
           r = removeCachedValue ObserverIndex_eq cachedIndex
                             (AddCachedValue ObserverIndex_eq cachedIndex r cachedFunc).
  Proof.
    unfold removeCachedValue, AddCachedValue, AddValidCacheInv; simpl; intros; intuition.
    destruct r; simpl; f_equal; apply functional_extensionality.
    intros; destruct (ObserverIndex_eq x cachedIndex); subst; eauto.
    generalize (H1 cachedIndex); rewrite NInCachedSet; auto.
  Qed.
  Hint Resolve RemoveAddCachedValue.

  Theorem refinesAddCachedObserver
          {Rep ObserverIndex MutatorIndex}
          cachedSet
          (repInv : Ensemble Rep)
          ObserverMethods
          MutatorMethods
          MutatorMethodsInv
          ObserverIndex_eq
          cachedIndex
          NInCachedSet
          cachedFunc
          refines_cached
  : refineADT {| Rep := cachedObservers Rep ObserverIndex;
                 RepInv := AddValidCacheInv repInv cachedSet ObserverMethods;
                  ObserverIndex := ObserverIndex;
                  MutatorIndex := MutatorIndex;
                  ObserverMethods idx r := ObserverMethods idx (origRep r);
                  MutatorMethods := MutatorMethods;
                  MutatorMethodsInv := MutatorMethodsInv
               |}
              (addCachedObserver ObserverIndex_eq cachedIndex NInCachedSet
                                 MutatorMethods MutatorMethodsInv cachedFunc refines_cached).
  Proof.
    unfold addCachedObserver.
    econstructor 1 with
    (abs := fun nm : cachedObservers Rep _ =>
              ret (removeCachedValue ObserverIndex_eq cachedIndex nm))
      (mutatorMap := @id MutatorIndex) (* Have to specify MutatorIndex in order to
                                        unify- 8.5 might fix this? *)
      (observerMap := @id ObserverIndex); simpl; unfold id; intros.
    - unfold AddCachedObv; simpl; autorewrite with refine_monad.
      rewrite <- refineEquiv_unit_bind.
      apply refine_under_bind with
      (P := AddValidCacheInv repInv cachedSet ObserverMethods); intros; eauto.
      + eapply refineCompInv; eauto; autorewrite with refine_monad;
        reflexivity.
      + autorewrite with refine_monad; destruct x; simpl;
        f_equiv; eauto.
      + autorewrite with refine_monad; reflexivity.
    - autorewrite with refine_monad; simpl; reflexivity.
    - apply computes_to_inv in H0; subst; eauto.
  Qed.

  Lemma refine_is_computational_val
    {Rep ObserverIndex}
    (ObserverMethods : ObserverIndex -> Rep -> nat -> Comp nat)
    (cachedIndex : ObserverIndex)
    (CompCachedIndex : forall (r : cachedObservers Rep ObserverIndex)
            n, is_computational (ObserverMethods cachedIndex (origRep r) n))
  : forall r n, refine (ObserverMethods cachedIndex (origRep r) n)
                       (ret (is_computational_val (CompCachedIndex r n))).
  Proof.
    unfold refine; simpl in *|-*; intros.
    inversion_by computes_to_inv; subst.
    apply is_computational_val_computes_to.
  Qed.

  Definition refinesComputationalAddCachedObserver
          {Rep ObserverIndex MutatorIndex}
          cachedSet
          (repInv : Ensemble Rep)
          ObserverMethods
          MutatorMethods
          MutatorMethodsInv
          (ObserverIndex_eq : forall idx idx' : ObserverIndex,
                                  {idx = idx'} + {idx <> idx'})
          (cachedIndex : ObserverIndex)
          (NInCachedSet : cachedSet cachedIndex = false)
          (CompCachedIndex : forall (r : cachedObservers Rep ObserverIndex)
                  n, is_computational (ObserverMethods cachedIndex (origRep r) n))
  : refineADT {| Rep := cachedObservers Rep ObserverIndex;
                           RepInv := AddValidCacheInv repInv cachedSet ObserverMethods;
                           ObserverIndex := ObserverIndex;
                           MutatorIndex := MutatorIndex;
                           ObserverMethods idx r := ObserverMethods idx (origRep r);
                           MutatorMethods := MutatorMethods;
                           MutatorMethodsInv := MutatorMethodsInv |}
              (addCachedObserver ObserverIndex_eq cachedIndex NInCachedSet
                                 MutatorMethods MutatorMethodsInv _
                                 (refine_is_computational_val _ _ CompCachedIndex)).
  Proof.
    apply refinesAddCachedObserver.
  Qed.

  (* ADT which updates an existing cached value. *)

  Definition UpdateCachedObserver
          {Rep ObserverIndex MutatorIndex}
          (cachedSet : ObserverIndex -> bool)
          (repInv : Ensemble Rep)
          ObserverMethods
          (ObserverIndex_eq : forall idx idx' : ObserverIndex,
                                   {idx = idx'} + {idx <> idx'})
          (cachedIndex : ObserverIndex)
          InCachedSet
          (MutatorMethods : MutatorIndex -> mutatorMethodType (cachedObservers Rep ObserverIndex))
          (MutatorMethodsInv :
             forall idx r n, AddValidCacheInv repInv cachedSet ObserverMethods r ->
                             computational_inv (AddValidCacheInv repInv cachedSet ObserverMethods)
                                       (MutatorMethods idx r n))
          cachedFunc
          refines_cached
          FuncEqv
  : ADT :=
    {| Rep := cachedObservers Rep ObserverIndex;
       RepInv := AddValidCacheInv repInv cachedSet ObserverMethods;
       ObserverIndex := ObserverIndex;
       MutatorIndex := MutatorIndex;
       ObserverMethods idx r := ObserverMethods idx (origRep r);
       MutatorMethods idx r n :=
         UpdateCachedObv ObserverIndex_eq MutatorMethods cachedIndex cachedFunc idx
                          r n;
       MutatorMethodsInv :=
         @UpdateCachedInv Rep ObserverIndex ObserverIndex_eq repInv
                          MutatorIndex cachedSet ObserverMethods
                          MutatorMethods cachedIndex InCachedSet cachedFunc refines_cached
                          FuncEqv MutatorMethodsInv
    |}.

  Lemma split_computational_inv
        X (P Q : Ensemble X) x
        (compInvP : computational_inv P x)
        (compInvQ : computational_inv Q x)
        : computational_inv (fun r : X => P r /\ Q r) x.
  Proof.
    simpl in *|-*; eauto.
  Qed.
  Hint Resolve split_computational_inv.

  (* [updateCachedObserver] from above is a valid refinement *)

  Theorem refinesUpdateCachedObserver
          {Rep ObserverIndex MutatorIndex}
          cachedSet
          (repInv : Ensemble Rep)
          ObserverMethods
          MutatorMethods
          MutatorMethodsInv
          ObserverIndex_eq
          cachedIndex
          InCachedSet
          cachedFunc
          refines_cached
          FuncEqv
  : refineADT {| Rep := cachedObservers Rep ObserverIndex;
                 RepInv := AddValidCacheInv repInv cachedSet ObserverMethods;
                  ObserverIndex := ObserverIndex;
                  MutatorIndex := MutatorIndex;
                  ObserverMethods idx r := ObserverMethods idx (origRep r);
                  MutatorMethods := MutatorMethods;
                  MutatorMethodsInv := MutatorMethodsInv
               |}
              (UpdateCachedObserver ObserverIndex_eq cachedIndex InCachedSet
                                 MutatorMethods MutatorMethodsInv cachedFunc refines_cached FuncEqv).
  Proof.
    unfold UpdateCachedObserver.
    econstructor 1 with
    (abs := fun nm : cachedObservers Rep ObserverIndex => ret nm)
      (mutatorMap := @id MutatorIndex) (* Have to specify MutatorIndex in order to
                                        unify- 8.5 might fix this? *)
      (observerMap := @id ObserverIndex); simpl; unfold id; intros.
    - unfold UpdateCachedObv; simpl; autorewrite with refine_monad.
      rewrite <- refineEquiv_unit_bind at 1.
      apply refine_under_bind with
      (P := fun r => AddValidCacheInv repInv cachedSet ObserverMethods r /\
              observerCache r cachedIndex = Some (cachedFunc new_state r)); intros; eauto; try reflexivity.
      + destruct x; unfold AddCachedValue; f_equiv; f_equal; intuition;
        simpl in *|-*.
        apply functional_extensionality.
        intros; destruct (ObserverIndex_eq x cachedIndex); subst; eauto.
    - autorewrite with refine_monad; reflexivity.
    - apply computes_to_inv in H0; subst; eauto.
  Qed.

  (* Finally, we can always change the observers to use the cache. *)

  Definition CacheObservers
          {Rep ObserverIndex MutatorIndex}
          (cachedSet : ObserverIndex -> bool)
          (repInv : Ensemble Rep)
          ObserverMethods
          (ObserverIndex_eq : forall idx idx' : ObserverIndex,
                                   {idx = idx'} + {idx <> idx'})
          (MutatorMethods : MutatorIndex -> mutatorMethodType (cachedObservers Rep ObserverIndex))
          MutatorMethodsInv
  : ADT :=
    {| Rep := cachedObservers Rep ObserverIndex;
       RepInv := AddValidCacheInv repInv cachedSet ObserverMethods;
       ObserverIndex := ObserverIndex;
       MutatorIndex := MutatorIndex;
       ObserverMethods idx r :=
         match observerCache r idx with
           | Some f => fun n => ret (f n)
           | None => ObserverMethods idx (origRep r)
         end;
       MutatorMethods := MutatorMethods;
       MutatorMethodsInv := MutatorMethodsInv
    |}.

  (* [CacheObservers] from above is a valid refinement *)

  Theorem refinesCacheObservers
          {Rep ObserverIndex MutatorIndex}
          cachedSet
          (repInv : Ensemble Rep)
          ObserverMethods
          MutatorMethods
          MutatorMethodsInv
          ObserverIndex_eq
  : refineADT {| Rep := cachedObservers Rep ObserverIndex;
                 RepInv := AddValidCacheInv repInv cachedSet ObserverMethods;
                 ObserverIndex := ObserverIndex;
                 MutatorIndex := MutatorIndex;
                 ObserverMethods idx r := ObserverMethods idx (origRep r);
                 MutatorMethods := MutatorMethods;
                 MutatorMethodsInv := MutatorMethodsInv
               |}
              (CacheObservers ObserverIndex_eq MutatorMethods
                              MutatorMethodsInv).
  Proof.
    econstructor 1 with
    (abs := fun nm : cachedObservers Rep ObserverIndex => ret nm)
      (mutatorMap := @id MutatorIndex) (* Have to specify MutatorIndex in order to
                                        unify- 8.5 might fix this? *)
      (observerMap := @id ObserverIndex); simpl; unfold id; intros.
    - autorewrite with refine_monad; reflexivity.
    - autorewrite with refine_monad; caseEq (observerCache new_state idx); try reflexivity.
      unfold AddValidCacheInv in *|-*; intuition; simpl in *|-*.
      generalize (H2 idx); find_if_inside; intros.
      + destruct_ex; intuition; substss; injections; eauto.
      + destruct_ex; intuition; substss; discriminate.
    -  apply computes_to_inv in H0; subst; eauto.
  Qed.

(** TODO: Update this to reflect the new definition of ADT + ADT
    Refinement *)

(* If you mutate and then observe, you can do it before or after
    refinement.  I'm not actually sure this isn't obvious.
 *)

(* Lemma ADTRefinementOk
      (old new : ADT)
      (new_initial_value : Comp (Rep new))
      abs mutatorMap observerMap H H'
      (ref : refineADT old new
       := @refinesADT old new abs mutatorMap observerMap H H')
      mutIdx obsIdx n n'
: refine (v0 <- new_initial_value;
          v <- abs v0;
          v' <- MutatorMethods old mutIdx v n;
          ObserverMethods old obsIdx v' n')
         (v <- new_initial_value;
          v' <- MutatorMethods new (mutatorMap mutIdx) v n;
          ObserverMethods new (observerMap obsIdx) v' n').
Proof.
  simpl in *.
  apply refine_bind; [ reflexivity | ].
  intro.
  interleave_autorewrite_refine_monad_with setoid_rewrite_hyp.
Qed. *)

End GeneralRefinements.
