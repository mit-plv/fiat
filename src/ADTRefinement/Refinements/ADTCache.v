Require Import Fiat.Common Fiat.Computation Fiat.ADT Coq.Sets.Ensembles Fiat.ADTRefinement Fiat.ADTRefinement.Refinements.ADTRepInv.

Generalizable All Variables.
Set Implicit Arguments.

Open Scope comp_scope.

Section addCache.

  (* A cache simply adds a new value to an ADT's representation [rep]. *)

  Variable rep : Type.
  Variable cacheTyp : Type.

  Record cachedRep :=
    { origRep : rep;
      cachedVal : cacheTyp
    }.

  Variable cacheSpec : rep -> cacheTyp -> Prop.

  (* A representation with an added value [nr] is related to any representation [or]
     when the cached value [cachedVal] satisfies the original [cacheSpec] and
     the original representation of [nr] is equal to [or]. *)

  Definition cachedRep_AbsR (or : rep) (nr : cachedRep) :=
    or = origRep nr /\ cacheSpec or (cachedVal nr).

  (* To add a cache, we update an ADT's methods to include cached values.
       We first run the old method to obtain the original result [or],
       then we add a Pick implementation of a [cacheVal]
       that satisfies our specification [cacheSpec] to the result. *)

  Fixpoint addCacheToMethod'
    (Dom : list Type)
    (Cod : option Type)
    (oldMethod : methodType' rep Dom Cod)
    : methodType' cachedRep Dom Cod :=
    match Dom return methodType' rep Dom Cod
                     -> methodType' cachedRep Dom Cod with
    | nil => match Cod return methodType' rep nil Cod
                                -> methodType' cachedRep nil Cod with
             | Some C => fun oldMethod =>
                           or <- oldMethod;
                           cv <- {cv | cacheSpec (fst or) cv};
                           ret ({| origRep := (fst or);
                                   cachedVal := cv |}, snd or)
               | None => fun oldMethod =>
                           or <- oldMethod;
                           cv <- {cv | cacheSpec or cv};
                           ret {| origRep := or;
                                  cachedVal := cv |}
               end
    | cons D Dom' => fun oldMethod (d : D) => addCacheToMethod' Dom' Cod (oldMethod d)
    end oldMethod.

  (*Definition addCacheToMethod
             arity
             {Dom : list Type}
             {Cod : option Type}
             (oldMethod : methodType arity rep Dom Cod)
             (nr : cachedRep)
    : methodType' cachedRep Dom Cod :=
    addCacheToMethod' Dom Cod (oldMethod (origRep nr)).

  Lemma refine_addCacheToMethod
        {Dom : list Type}
        {Cod : option Type}
        (oldMethod : methodType rep Dom Cod)
  : @refineMethod rep cachedRep cachedRep_AbsR _ _
                  oldMethod
                  (addCacheToMethod oldMethod).
  Proof.
    unfold refineMethod, addCacheToMethod, methodType,
    cachedRep_AbsR, refine in *; intros; intuition; subst.
    induction Dom; simpl.
    - destruct Cod.
      + unfold cachedRep_AbsR in *; intuition; subst.
        repeat (f_equiv; intro).
        computes_to_inv; subst.
        repeat computes_to_econstructor.
        simpl; split; eauto.
      + unfold cachedRep_AbsR in *; intuition; subst.
        repeat (f_equiv; intro).
        computes_to_inv; subst.
        repeat computes_to_econstructor.
        simpl; split; eauto.
    - intros; eapply (IHDom (fun r_n => oldMethod r_n d)).
  Qed.

  (* For use in honing tactics. *)
  Lemma refine_addCacheToMethod_step
        {Dom : list Type}
        {Cod : option Type}
        (oldMethod : methodType rep Dom Cod)
        (newMethod : methodType cachedRep Dom Cod)
    : @refineMethod_eq cachedRep _ _
                     (addCacheToMethod oldMethod)
                     newMethod ->
      @refineMethod rep cachedRep cachedRep_AbsR _ _
                    oldMethod
                    newMethod.
  Proof.
    intros; eapply refineMethod_eq_trans;
    eauto using refine_addCacheToMethod.
  Qed.

  (* A similar approach works for constructors. *)
  Fixpoint addCacheToConstructor
           {Dom : list Type}
    (oldConstructor : constructorType rep Dom)
    : constructorType cachedRep Dom :=
    match Dom return constructorType rep Dom
                     -> constructorType cachedRep Dom with
    | nil => fun oldConstructor =>
               or <- oldConstructor;
               cv <- {cv | cacheSpec or cv};
               ret {| origRep := or;
                      cachedVal := cv |}
    | cons D Dom' => fun oldConstructor (d : D) => @addCacheToConstructor Dom' (oldConstructor d)
    end oldConstructor.

  Lemma refine_addCacheToConstructor
        (Dom : list Type)
        (oldConstr : constructorType rep Dom)
  : @refineConstructor rep cachedRep cachedRep_AbsR _
                  oldConstr
                  (addCacheToConstructor oldConstr).
  Proof.
    unfold cachedRep_AbsR, refine in *; intros; intuition; subst.
    induction Dom; simpl.
    - repeat (f_equiv; intro).
      computes_to_inv; subst.
      repeat computes_to_econstructor; eauto.
    - intros; eapply IHDom.
  Qed.

  (* For use in honing tactics. *)
  Lemma refine_addCacheToConstructor_step
        (Dom : list Type)
        (oldConstr : constructorType rep Dom)
        (newConstr : constructorType cachedRep Dom)
    : refineConstructor_eq _ (addCacheToConstructor oldConstr) newConstr
      -> @refineConstructor rep cachedRep cachedRep_AbsR _
                  oldConstr newConstr.
  Proof.
    eapply refineConstructor_eq_trans;
    eauto using refine_addCacheToConstructor.
  Qed.

  (* We can refine an ADT using the default caching implementations
     provided by [absMutatorMethod] and [absObserverMethod]. *)
  Lemma refine_addCacheToADT
        Sig
        oldConstrs oldMeths :
    refineADT
      (@Build_ADT Sig rep oldConstrs oldMeths)
      (@Build_ADT Sig cachedRep
                  (fun idx => addCacheToConstructor (oldConstrs idx))
                  (fun idx => addCacheToMethod (oldMeths idx))).
  Proof.
    eapply refineADT_Build_ADT_Rep;
    eauto using refine_addCacheToConstructor,
    refine_addCacheToMethod.
  Qed.

  (* After caching, we can resolve [Pick]s of the new
   representation by showing how to build the cache. *)
  Lemma refine_pick_cachedRep
  : forall or,
      refine {nr | cachedRep_AbsR or nr}
             (cv <- {cv | cacheSpec or cv};
              ret {| origRep := or;
                     cachedVal := cv |}).
  Proof.
    unfold refine; intros or v ComputesTo_v;
    computes_to_inv; subst; econstructor;
    unfold cachedRep_AbsR; simpl; intuition.
  Qed. *)

End addCache.
