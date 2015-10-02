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

  (*Definition addCacheToMethod
        (Dom Cod : Type)
        (oldMethod : methodType rep Dom Cod) nr n
  : Comp (cachedRep * Cod) :=
    or <- oldMethod (origRep nr) n;
    cv <- {cv | cacheSpec (fst or) cv};
    ret ({| origRep := (fst or);
            cachedVal := cv |}, snd or).

  Lemma refine_addCacheToMethod
        (Dom Cod : Type)
        (oldMethod : methodType rep Dom Cod)
  : @refineMethod rep cachedRep cachedRep_AbsR _ _
                  oldMethod
                  (addCacheToMethod oldMethod).
  Proof.
    unfold refineMethod, addCacheToMethod, refine; intros.
    computes_to_inv; subst.
    destruct H; subst.
    repeat computes_to_econstructor; eauto; split; eauto.
  Qed.

  (* A similar approach works for constructors. *)
  Definition addCacheToConstructor
        (Dom : Type)
        (oldConstr : constructorType rep Dom) n
  : Comp cachedRep :=
    or <- oldConstr n;
    cv <- {cv | cacheSpec or cv};
    ret {| origRep := or;
           cachedVal := cv |}.

  Lemma refine_addCacheToConstructor
        (Dom : Type)
        (oldConstr : constructorType rep Dom)
  : @refineConstructor rep cachedRep cachedRep_AbsR _
                  oldConstr
                  (addCacheToConstructor oldConstr).
  Proof.
    unfold refineConstructor, addCacheToConstructor, refine; intros.
    computes_to_inv; subst.
    repeat computes_to_econstructor; eauto; split; eauto.
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
