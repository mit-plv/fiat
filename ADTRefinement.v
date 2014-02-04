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

Global Instance refineADT_PreOrder : PreOrder refineADT.
Proof.
  split; compute in *.
  - intro x.
    econstructor 1 with
    (abs := @Return _)
      (mutatorMap := id)
      (observerMap := id);
      unfold id; simpl; intros;
      autorewrite with refine_monad;
      try reflexivity;
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
    Record cachedObservers :=
      { origRep : rep;
        observerCache : observerIndex -> option (nat -> nat)}.

    (* A cache is well-formed if it refines all the observer methods
     included in the cacheSet. *)
    Definition ValidCache (cacheSet : observerIndex -> bool) ObserverMethods
               (r : cachedObservers) :=
      forall idx,
        if cacheSet idx then
          exists func,
            observerCache r idx = Some func /\
            forall n, refine (ObserverMethods idx r n) (ret (func n))
        else
          observerCache r idx = None.
    Arguments ValidCache _ ObserverMethods r / .

    Variable RepInv : Ensemble rep.
    Definition AddValidCacheInv cacheSet ObserverMethods
               (r : cachedObservers) :=
      RepInv (origRep r) /\ ValidCache cacheSet ObserverMethods r.
    Arguments AddValidCacheInv _ ObserverMethods r / .

    (* A value is cached by applying a function to the representation
      built by a mutator. *)
    Definition ReplaceCachedObv
               {MutatorIndex}
               (MutatorMethods : MutatorIndex -> mutatorMethodType (cachedObservers))
               (cachedIndex : observerIndex) (* Index of the Observer to Cache *)
               (cachedFunc : rep -> nat -> nat)
               idx m n :=
      om <- MutatorMethods idx m n;
      ret (Build_cachedObservers (origRep om)
                                 (fun idx => if (idx == cachedIndex) then
                                               Some (cachedFunc (origRep om))
                                             else
                                               observerCache om idx)).

    Definition insertCachedSet cachedSet cachedIndex (idx : observerIndex) : bool :=
      if (idx == cachedIndex) then
        true
      else
        cachedSet idx.
    Arguments insertCachedSet _ _ idx / .

    (* Well-formed cached observer methods use the cache if it is available (naturally).
     *)
    Definition cachedObserverMethodsWF cachedObserverMethods :=
      forall r idx f,
        observerCache r idx = Some f ->
        forall n,
          refineEquiv (cachedObserverMethods idx r n) (ret (f n)).
    Arguments cachedObserverMethodsWF _ / .

    (* Well-formed cached observer methods will default to the original
       observer methods for uncached indices.
     *)
    Definition cachedObserverMethodsWF' ObserverMethods cachedObserverMethods :=
      forall r idx,
        observerCache r idx = None ->
        forall n : nat,
          refine (A := nat) (ObserverMethods idx r n) (cachedObserverMethods idx r n).
    Arguments cachedObserverMethodsWF' _ _ / .

    (* Removing a cached value from a well-formed cache will produce
       another well-formed cache value *)
    Lemma RemoveValidCacheInv
    : forall cachedSet cachedIndex ObserverMethods cachedObserverMethods r,
        cachedObserverMethodsWF cachedObserverMethods ->
        cachedObserverMethodsWF' ObserverMethods cachedObserverMethods ->
        AddValidCacheInv cachedSet cachedObserverMethods r ->
        AddValidCacheInv (fun idx =>
                            if idx == cachedIndex
                            then false
                            else cachedSet idx)
                         cachedObserverMethods
    {| origRep := origRep r;
       observerCache idx :=
         if idx == cachedIndex then None else observerCache r idx |}.
    Proof.
      simpl; intros; intuition.
      generalize (H3 idx); destruct (idx == cachedIndex);
      find_if_inside; intuition; destruct_ex; intuition;
      try (eexists; subst; split; eauto;
           intros; generalize (H3 n); intros;
           rewrite <- H; eauto; fail).
      eexists; split; eauto; intros.
      eapply H; simpl; eauto; find_if_inside; congruence.
    Qed.
    Hint Resolve RemoveValidCacheInv.

    (* Removing a replaced cached value from a well-formed cache will produce
       another well-formed cache value *)
    Lemma ReplaceValidCacheInv
    : forall cachedSet ObserverMethods cachedObserverMethods r
        (refines_Observers : forall idx r n,
                               refine (ObserverMethods idx r n) (cachedObserverMethods idx r n)),
        AddValidCacheInv cachedSet cachedObserverMethods r ->
        AddValidCacheInv cachedSet ObserverMethods r.
    Proof.
      simpl; intros; intuition.
      generalize (H1 idx); find_if_inside; intuition; destruct_ex; intuition;
      try (eexists; subst; split; eauto;
           intros; generalize (H3 n); intros;
           rewrite <- H; eauto; fail).
    Qed.
    Hint Resolve ReplaceValidCacheInv.

    Lemma ReplaceCacheInv
          {MutatorIndex cachedSet}
          cachedObserverMethods
          ObserverMethods MutatorMethods
          (cachedIndex : observerIndex)
          (cachedSetIndex : cachedSet cachedIndex = true)
          cachedFunc
          (refines_cached : forall r n,
                              refine (cachedObserverMethods cachedIndex r n)
                                     (ret (cachedFunc (origRep r) n)))
          (refines_cached' : forall r idx f,
                              observerCache r idx = Some f ->
                              forall n,
                                refineEquiv (ret (f n)) (cachedObserverMethods idx r n))
          (refines_Observers : forall idx r n,
                                 refine (ObserverMethods idx r n) (cachedObserverMethods idx r n))
    : (forall idx  r n, AddValidCacheInv cachedSet ObserverMethods r ->
                        computational_inv (AddValidCacheInv cachedSet ObserverMethods)
                                          (MutatorMethods idx r n)) ->
      forall (idx : MutatorIndex) r n,
        AddValidCacheInv cachedSet cachedObserverMethods r ->
        computational_inv
          (AddValidCacheInv cachedSet cachedObserverMethods)
          (ReplaceCachedObv MutatorMethods cachedIndex cachedFunc
                            idx r n).
    Proof.
      unfold ReplaceCachedObv, computational_inv; intros.
      apply_in_hyp computes_to_inv; destruct_ex; intuition;
      apply_in_hyp computes_to_inv; destruct_ex; subst; simpl.
      generalize (H idx r n (ReplaceValidCacheInv _ refines_Observers H0) _ H2); simpl; intuition.
      generalize (H4 idx0); intros.
      destruct (ObserverIndex_eq idx0 cachedIndex); subst; eauto.
      rewrite cachedSetIndex in *|-*; eexists; split; eauto.
      intros.
      eapply refines_cached'; simpl; find_if_inside; congruence.
      find_if_inside; destruct_ex; intuition; eauto.
      eexists; intuition; eauto.
      rewrite refines_cached'; subst; simpl; [reflexivity | eauto].
      simpl; find_if_inside; subst; eauto.
      congruence.
    Qed.

    Lemma AddCachedInv
          {MutatorIndex cachedSet}
          cachedObserverMethods
          ObserverMethods MutatorMethods
          (cachedIndex : observerIndex)
          (cachedSetIndex : cachedSet cachedIndex = false)
          cachedFunc
          (refines_cached : forall r n,
                              refine (cachedObserverMethods cachedIndex r n)
                                     (ret (cachedFunc (origRep r) n)))
          (refines_cached' : forall r idx f,
                              observerCache r idx = Some f ->
                              forall n,
                                refineEquiv (ret (f n)) (cachedObserverMethods idx r n))
          (refines_Observers : forall idx r n,
                                 refine (ObserverMethods idx r n) (cachedObserverMethods idx r n))
    : (forall idx  r n, AddValidCacheInv cachedSet ObserverMethods r ->
                        computational_inv (AddValidCacheInv cachedSet ObserverMethods)
                                          (MutatorMethods idx r n)) ->
      forall (idx : MutatorIndex) r n,
        AddValidCacheInv (insertCachedSet cachedSet cachedIndex) cachedObserverMethods r ->
        computational_inv
          (AddValidCacheInv (insertCachedSet cachedSet cachedIndex) cachedObserverMethods)
          (ReplaceCachedObv MutatorMethods cachedIndex cachedFunc
                            idx r n).
    Proof.
      unfold ReplaceCachedObv, computational_inv; intros.
      apply_in_hyp computes_to_inv; destruct_ex; intuition;
      apply_in_hyp computes_to_inv; destruct_ex; subst; simpl.
      generalize (H idx r n (ReplaceValidCacheInv _ refines_Observers H0) _ H2); simpl; intuition.
      generalize (H4 idx0); intros.
      destruct (ObserverIndex_eq idx0 cachedIndex); subst; eauto.
      rewrite cachedSetIndex in *|-*; eexists; split; eauto.
      intros.
      eapply refines_cached'; simpl; find_if_inside; congruence.
      find_if_inside; destruct_ex; intuition; eauto.
      eexists; intuition; eauto.
      rewrite refines_cached'; subst; simpl; [reflexivity | eauto].
      simpl; find_if_inside; subst; eauto.
      congruence.
    Qed.

  End addCache.

  Arguments ValidCache _ _ _ _ _ / .

  Program Definition addCache adt : ADT :=
    {| Rep := cachedObservers (Rep adt) (ObserverIndex adt);
       RepInv := AddValidCacheInv (RepInv adt) (fun _ => false)
                                  (fun idx r => ObserverMethods adt idx (origRep r)) ;
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
  Arguments AddValidCacheInv _ _ _ _ _ _ / .

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
    - intros; inversion_by computes_to_inv; subst; intuition.
  Qed.

  Definition addCachedObserver
          {Rep ObserverIndex MutatorIndex}
          (cachedSet : ObserverIndex -> bool)
          (repInv : Ensemble Rep)
          ObserverMethods
          (ObserverIndex_eq : forall idx idx' : ObserverIndex,
                                   {idx = idx'} + {idx <> idx'})
          (cachedIndex : ObserverIndex)
          (cachedObserverMethods : ObserverIndex -> observerMethodType (cachedObservers Rep ObserverIndex))
          (MutatorMethods : MutatorIndex -> mutatorMethodType (cachedObservers Rep ObserverIndex))
          (MutatorMethodsInv :
             forall idx r n, AddValidCacheInv repInv cachedSet ObserverMethods r ->
                             computational_inv (AddValidCacheInv repInv cachedSet ObserverMethods)
                                       (MutatorMethods idx r n))
          cachedFunc
          refines_cached
          refines_Observers
          cachedObserver_OK
  : ADT :=
    {| Rep := cachedObservers Rep ObserverIndex;
       RepInv := AddValidCacheInv repInv (insertCachedSet _ cachedSet cachedIndex)
                                  cachedObserverMethods;
       ObserverIndex := ObserverIndex;
       MutatorIndex := MutatorIndex;
       ObserverMethods idx r n :=
         match observerCache r idx with
             Some func => ret (func n)
           | _ => cachedObserverMethods idx r n
         end;
       MutatorMethods idx r n :=
         ReplaceCachedObv ObserverIndex_eq MutatorMethods cachedIndex cachedFunc idx
                          r n;
       MutatorMethodsInv :=
         @ReplaceCacheInv Rep ObserverIndex ObserverIndex_eq repInv
                          MutatorIndex cachedSet cachedObserverMethods ObserverMethods
                          MutatorMethods cachedIndex cachedFunc refines_cached refines_Observers
                          cachedObserver_OK MutatorMethodsInv
    |}.

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

  Print Implicit addCachedObserver.

  Lemma refine_ret_eq : forall (A : Type) (a a' : A),
                          refine (ret a) (ret a') -> a = a'.
  Proof.
    unfold refine; intros; generalize (H a' (ReturnComputes _)).
    intros; inversion_by computes_to_inv; auto.
  Qed.

  Theorem refines_addCachedObserver
          {Rep ObserverIndex MutatorIndex}
          cachedSet
          (repInv : Ensemble Rep)
          ObserverMethods
          cachedObserverMethods
          MutatorMethods
          (MutatorMethodsInv :
             forall (idx : MutatorIndex) (r : cachedObservers Rep ObserverIndex)
                    (n : nat),
               AddValidCacheInv cachedSet ObserverMethods repInv r ->
               computational_inv (AddValidCacheInv cachedSet ObserverMethods repInv)
                                 (MutatorMethods idx r n))
          ObserverIndex_eq
          cachedIndex
          cachedFunc
          refines_cached
          refines_cached'
          refines_Observers
  : cachedSet cachedIndex = true ->
    refineADT {| Rep := cachedObservers Rep ObserverIndex;
                 RepInv := AddValidCacheInv cachedSet ObserverMethods repInv;
                  ObserverIndex := ObserverIndex;
                  MutatorIndex := MutatorIndex;
                  ObserverMethods := cachedObserverMethods;
                  MutatorMethods := MutatorMethods;
                  MutatorMethodsInv := MutatorMethodsInv
               |}
              (addCachedObserver ObserverIndex_eq cachedIndex
                                 cachedObserverMethods MutatorMethods
                                 MutatorMethodsInv cachedFunc
                                 refines_cached refines_cached' refines_Observers).
  Proof.
    idtac.
    unfold addCachedObserver.
    econstructor 1 with (abs := fun nm : cachedObservers Rep ObserverIndex =>
                                  if (cachedSet cachedIndex) then
                                    ret nm
                                  else
                                    ret {| origRep := origRep nm;
                                           observerCache idx :=
                                             if ObserverIndex_eq idx cachedIndex then
                                               None
                                             else observerCache nm idx |})
                          (mutatorMap := @id MutatorIndex)
                          (observerMap := @id ObserverIndex); simpl.
    - intros; rewrite H; autorewrite with refine_monad; unfold ReplaceCachedObv.
      unfold insertCachedSet in H0.
      unfold AddValidCacheInv in MutatorMethodsInv.
      rewrite <- refineEquiv_unit_bind; apply refine_under_bind with
                                        (P := AddValidCacheInv cachedSet ObserverMethods repInv); intros.
      + eapply MutatorMethodsInv; simpl; intuition.
        generalize (H2 idx0).
        destruct (ObserverIndex_eq idx0 cachedIndex); intros; eauto.
        subst; rewrite H.
        destruct H0 as [func [func_eq refine_func] ]; eexists; split; eauto.
        intros; rewrite refines_Observers; eauto.
        find_if_inside; destruct_ex; eexists; intuition; eauto.
        rewrite refines_Observers; eauto.
      + eapply MutatorMethodsInv; simpl; intuition.
        generalize (H2 idx0).
        destruct (ObserverIndex_eq idx0 cachedIndex); intros; eauto.
        subst; rewrite H.
        destruct H0 as [func [func_eq refine_func] ]; eexists; split; eauto.
        intros; rewrite refines_Observers; eauto.
        find_if_inside; destruct_ex; eexists; intuition; eauto.
        rewrite refines_Observers; eauto.
      + simpl in H1; intuition; destruct x; simpl in *|-*.
        assert (observerCache0 = fun idx0 =>
                                   if ObserverIndex_eq idx0 cachedIndex
                                   then Some (cachedFunc origRep0)
                                   else observerCache0 idx0).
        * apply functional_extensionality; intros.
          find_if_inside; subst; eauto.
          generalize (H4 cachedIndex); rewrite H; intros; destruct_ex;
          intuition.
          rewrite H5.
          apply f_equal; apply functional_extensionality; intros.
          generalize (refines_cached' {| origRep := origRep0; observerCache := observerCache0 |} _ _ H5 x0); intros.
          destruct H1.
          rewrite refines_cached in H1.
          rewrite (refine_ret_eq H1); auto.
        * rewrite H1 at 1; reflexivity.
      + reflexivity.
    - intros; rewrite H; autorewrite with refine_monad;
      intuition; unfold insertCachedSet in H2.
      generalize (H2 idx); simpl.
      destruct (ObserverIndex_eq idx cachedIndex); intros; eauto.
      subst.
      unfold id; destruct H0 as [func [func_eq refine_func] ]; rewrite func_eq;
      eauto.
      generalize (refines_cached' new_state idx).
      unfold id; destruct (observerCache new_state idx).
      intros; rewrite H3; eauto; reflexivity.
      intros; reflexivity.
    - rewrite H; intros; inversion_by computes_to_inv; subst; intuition.
      unfold insertCachedSet in H3; generalize (H3 idx); simpl.
      destruct (ObserverIndex_eq idx cachedIndex); intros; eauto;
      subst.
      rewrite H; destruct_ex; eexists; intuition; eauto.
      rewrite refines_Observers; eauto.
      destruct (cachedSet idx); eauto.
      destruct_ex; eexists; intuition; eauto.
      rewrite refines_Observers; eauto.
  Qed.

  Theorem refines_addCachedObserver'
          {Rep ObserverIndex MutatorIndex}
          cachedSet
          (repInv : Ensemble Rep)
          ObserverMethods
          cachedObserverMethods
          MutatorMethods
          (MutatorMethodsInv :
             forall (idx : MutatorIndex) (r : cachedObservers Rep ObserverIndex)
                    (n : nat),
               AddValidCacheInv cachedSet ObserverMethods repInv r ->
               computational_inv (AddValidCacheInv cachedSet ObserverMethods repInv)
                                 (MutatorMethods idx r n))
          ObserverIndex_eq
          cachedIndex
          cachedFunc
          refines_cached
          refines_cached'
          refines_Observers
  : cachedSet cachedIndex = false ->
    refineADT {| Rep := cachedObservers Rep ObserverIndex;
                 RepInv := AddValidCacheInv cachedSet ObserverMethods repInv;
                  ObserverIndex := ObserverIndex;
                  MutatorIndex := MutatorIndex;
                  ObserverMethods := cachedObserverMethods;
                  MutatorMethods := MutatorMethods;
                  MutatorMethodsInv := MutatorMethodsInv
               |}
              (addCachedObserver ObserverIndex_eq cachedIndex
                                 cachedObserverMethods MutatorMethods
                                 MutatorMethodsInv cachedFunc
                                 refines_cached refines_cached' refines_Observers).
  Proof.
    idtac.
    unfold addCachedObserver.
    econstructor 1 with (abs := fun nm : cachedObservers Rep ObserverIndex =>
                                  if (cachedSet cachedIndex) then
                                    ret nm
                                  else
                                    ret {| origRep := origRep nm;
                                           observerCache idx :=
                                             if ObserverIndex_eq idx cachedIndex then
                                               None
                                             else observerCache nm idx |})
                          (mutatorMap := @id MutatorIndex)
                          (observerMap := @id ObserverIndex); simpl.
    - intros; rewrite H; autorewrite with refine_monad; unfold ReplaceCachedObv.
      unfold insertCachedSet in H0.
      unfold AddValidCacheInv in MutatorMethodsInv.
      autorewrite with refine_monad.
      generalize MutatorMethodsInv; simpl.
      rewrite <- refineEquiv_unit_bind. apply refine_under_bind with
                                        (P := AddValidCacheInv cachedSet ObserverMethods repInv); intros.
      + eapply MutatorMethodsInv; simpl; intuition.
        generalize (H2 idx0).
        destruct (ObserverIndex_eq idx0 cachedIndex); intros; eauto.
        subst; rewrite H.
        destruct H0 as [func [func_eq refine_func] ]; eexists; split; eauto.
        intros; rewrite refines_Observers; eauto.
        find_if_inside; destruct_ex; eexists; intuition; eauto.
        rewrite refines_Observers; eauto.
      + simpl in H1; intuition; destruct x; simpl in *|-*.
        assert (observerCache0 = fun idx0 =>
                                   if ObserverIndex_eq idx0 cachedIndex
                                   then Some (cachedFunc origRep0)
                                   else observerCache0 idx0).
        * apply functional_extensionality; intros.
          find_if_inside; subst; eauto.
          generalize (H4 cachedIndex); rewrite H; intros; destruct_ex;
          intuition.
          rewrite H5.
          apply f_equal; apply functional_extensionality; intros.
          generalize (refines_cached' {| origRep := origRep0; observerCache := observerCache0 |} _ _ H5 x0); intros.
          destruct H1.
          rewrite refines_cached in H1.
          rewrite (refine_ret_eq H1); auto.
        * rewrite H1 at 1; reflexivity.
    - intros; rewrite H; autorewrite with refine_monad;
      intuition; unfold insertCachedSet in H2.
      generalize (H2 idx); simpl.
      destruct (ObserverIndex_eq idx cachedIndex); intros; eauto.
      subst.
      unfold id; destruct H0 as [func [func_eq refine_func] ]; rewrite func_eq;
      eauto.
      generalize (refines_cached' new_state idx).
      unfold id; destruct (observerCache new_state idx).
      intros; rewrite H3; eauto; reflexivity.
      intros; reflexivity.
    - rewrite H; intros; inversion_by computes_to_inv; subst; intuition.
      unfold insertCachedSet in H3; generalize (H3 idx); simpl.
      destruct (ObserverIndex_eq idx cachedIndex); intros; eauto;
      subst.
      rewrite H; destruct_ex; eexists; intuition; eauto.
      rewrite refines_Observers; eauto.
      destruct (cachedSet idx); eauto.
      destruct_ex; eexists; intuition; eauto.
      rewrite refines_Observers; eauto.
  Qed.

rewrite func

eexists; split; eauto.
      intros; rewrite refines_Observers; eauto.
      find_if_inside; destruct_ex; eexists; intuition; eauto.
        rewrite refines_Observers; eauto.
      unfold insertCachedSet in H0.
      unfold insertO
      destruct (observerCache new_state (id idx)).
      simpl.
      case (cachedSet cachedIndex).
      find_if_inside; autorewrite with refine_monad.

      generalize (MutatorMethodsInv idx _ n H); simpl; intros.
      unfold refine; intros v H3; apply computes_to_inv in H3; destruct_ex; intuition.
      apply computes_to_inv in H4; subst.
      destruct (H0 _ H); destruct x; simpl in *.
      assert (observerCache0 = fun idx0 : ObserverIndex =>
                      if ObserverIndex_eq idx0 cachedIndex
                      then Some (cachedFunc origRep0)
                      else observerCache0 idx0).
      apply functional_extensionality; intros.


      setoid_replace (fun idx0 : ObserverIndex =>
                        if ObserverIndex_eq idx0 cachedIndex
                      then Some (cachedFunc origRep0)
                      else observerCache0 idx0) with observerCache0.



      rewrite <- refineEquiv_unit_bind; apply refine_under_bind; intros.
      destruct x; simpl.
      apply
      rewrite (proj1 (refineEquiv_under_bind _ (@Return _) _ _)); autorewrite with refine_monad.
      reflexivity.
      intuition; split; simpl.
      assert (observerCache0 = fun idx0 : ObserverIndex =>
                         if ObserverIndex_eq idx0 cachedIndex
                         then Some (cachedFunc origRep0)
                         else observerCache0 idx0).
      apply functional_extensionality; intros; find_if_inside.


      intros; autorewrite with refine_monad.


  Theorem refines_cached_Observer adt
          (ObserverIndex_eq : forall idx idx' : ObserverIndex adt,
                                {idx = idx'} + {idx <> idx'})
          (cachedIndex : ObserverIndex adt) (* Index of the Observer to Cache *)
          (cached_func : Rep adt -> nat -> nat)
          (refines_cached : forall om n,
                              refine (ObserverMethods adt cachedIndex om n)
                                     (ret (cached_func om n)))

  :
    refineADT adt
              {| Rep := {om : (Rep adt) * (nat -> nat) |
                           forall n, refine (ObserverMethods adt cachedIndex (fst om) n) (ret (snd om n))};
                 ObserverMethods idx nm n :=
                   if (ObserverIndex_eq idx cachedIndex) then
                     ret ((snd (proj1_sig nm)) n)
                   else
                     ObserverMethods adt idx (fst (proj1_sig nm)) n;
                 MutatorMethods idx nm n :=
                   origRep <- (MutatorMethods adt idx (fst (proj1_sig nm)) n);
                 ret (exist
                        (fun om => forall n, refine (ObserverMethods adt cachedIndex (fst om) n) (ret (snd om n)))
                        (origRep, cached_func origRep)
                        (refines_cached origRep))|}.
  Proof.
    destruct adt;
    econstructor 1 with
    (abs := fun om : {om | forall n, refine (ObserverMethods cachedIndex (fst om) n) (ret (snd om n))} =>
              ret (fst (proj1_sig om)))
      (mutatorMap := @id MutatorIndex)
      (observerMap := @id ObserverIndex); simpl; intros.
    - autorewrite with refine_monad; rewrite refineEquiv_under_bind with (g := @Return _);
      intros; autorewrite with refine_monad; reflexivity.
    - autorewrite with refine_monad; find_if_inside;
      [ destruct new_state; subst; auto
      | reflexivity].
  Qed.

  Theorem refines_cached_computational_Observer adt
          (ObserverIndex_eq : forall idx idx' : ObserverIndex adt,
                                {idx = idx'} + {idx <> idx'})
          (cachedIndex : ObserverIndex adt) (* Index of the Observer to Cache *)
          (computational_Index : forall om n, is_computational (ObserverMethods adt cachedIndex om n))
  :
    refineADT adt
              {| Rep := {om : (Rep adt) * (nat -> nat) |
                           forall n, refine (ObserverMethods adt cachedIndex (fst om) n) (ret (snd om n))};
                 MutatorIndex := MutatorIndex adt;
                 ObserverIndex := ObserverIndex adt;
                 ObserverMethods idx nm n :=
                   if (ObserverIndex_eq idx cachedIndex) then
                     ret ((snd (proj1_sig nm)) n)
                   else
                     ObserverMethods adt idx (fst (proj1_sig nm)) n;
                 MutatorMethods idx nm n :=
                   origRep <- (MutatorMethods adt idx (fst (proj1_sig nm)) n);
                 ret (exist
                        (fun om => forall n, refine (ObserverMethods adt cachedIndex (fst om) n) (ret (snd om n)))
                        (origRep, fun n => proj1_sig (is_computational_val (computational_Index origRep n)))
                        (fun n => refine_is_computational (computational_Index origRep n))) |}.
  Proof.
    apply refines_cached_Observer.
  Qed.

(** If you mutate and then observe, you can do it before or after
    refinement.  I'm not actually sure this isn't obvious.  *)

Lemma ADTRefinementOk
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
Qed.
