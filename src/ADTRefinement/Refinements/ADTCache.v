Require Import Common Computation ADT Ensembles ADTRefinement ADTRepInv.

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

  Definition addCacheToMethod
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
    inversion_by computes_to_inv; subst.
    destruct H; subst.
    repeat econstructor; eauto.
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
    inversion_by computes_to_inv; subst.
    repeat econstructor; eauto.
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
    inversion_by computes_to_inv; subst; econstructor.
    unfold cachedRep_AbsR; simpl; intuition.
  Qed.

End addCache.



(* Old Caching Definitions.

Definition addCachedValue Sig cacheTyp adt cacheSpec
: ADT Sig :=
  {| Rep := cachedRep (Rep adt) cacheTyp;
     Constructors := ConstructorAddCacheEntry cacheSpec (Constructors adt);
     Methods := MethodAddCacheEntry cacheSpec (Methods adt)|}.

Theorem refinesAddCachedValue Sig
        {cacheTyp}
        adt
        (cacheSpec : Rep adt -> cacheTyp -> Prop)
: @refineADT Sig adt (addCachedValue adt cacheSpec).
Proof.
  unfold addCachedValue; destruct adt.
  econstructor 1 with
  (AbsR := fun r_o r_n => r_o = origRep r_n /\ cacheSpec (origRep r_n) (cachedVal r_n)); unfold MethodAddCacheEntry, ConstructorAddCacheEntry; simpl;
  intros; autorewrite with refine_monad.
  - unfold refine; intros; inversion_by computes_to_inv; subst; eauto.
  - intros v CompV; inversion_by computes_to_inv; subst;
    repeat econstructor; eauto.
Qed.

(* Currently think it's good practice to expand ADT building blocks. *)
Arguments addCachedValue / .
Arguments MethodAddCacheEntry / .
Arguments ConstructorAddCacheEntry / .

Local Obligation Tactic := intros; subst; eauto.

Program Definition replaceMethod Sig adt
           (MethodIndex_eq : forall idx idx' : MethodIndex Sig, {idx = idx'} + {idx <> idx'})
           (cachedIndex : MethodIndex Sig)
           (f : Rep adt -> (fst (MethodDomCod Sig cachedIndex))
                -> Comp (Rep adt * snd (MethodDomCod Sig cachedIndex)))
: ADT Sig :=
  {| Rep := Rep adt;
     Constructors := Constructors adt;
     Methods idx :=
       if (MethodIndex_eq idx cachedIndex) then
         _
       else
         Methods adt idx|}.

Arguments replaceMethod / .

Arguments addCachedValue / .
Arguments MethodAddCacheEntry / .

Lemma refinesReplaceMethodCache
      Sig
      adt
      (repInv : Ensemble (Rep adt))
      (MethodIndex_eq : forall idx idx' : MethodIndex Sig, {idx = idx'} + {idx <> idx'})
      (cachedIndex : MethodIndex Sig)
      (f : Rep adt -> (fst (MethodDomCod Sig cachedIndex))
           -> Comp (Rep adt * snd (MethodDomCod Sig cachedIndex)))
      (ConstrAbsR : forall idx d,
                     refine (r_o' <- Constructors adt idx d;
                             {r_n | r_o' = r_n /\ repInv r_n})
                            (Constructors adt idx d))
      (MethAbsR : forall idx (r : Rep adt) n,
                  repInv r ->
                  refine
                    (r' <- Methods adt idx r n;
                     r'' <- {r'' : Rep adt | repInvAbsR repInv (fst r') r''};
                    ret (r'', snd r'))
                    (Methods adt idx r n))
      (refines_f : forall r n,
                     repInv r ->
                     refine (Methods adt cachedIndex r n) (f r n))
: refineADT adt (replaceMethod adt MethodIndex_eq cachedIndex f).
Proof.
  unfold replaceMethod; destruct adt; simpl.
  econstructor 1 with (AbsR := repInvAbsR repInv (rep := Rep));
    simpl in *|-*; unfold id, repInvAbsR; intros; intuition; subst; eauto.
  - destruct (MethodIndex_eq idx cachedIndex);
    [unfold replaceMethod_obligation_1, eq_rect_r, eq_rect;
      destruct e; simpl; eauto; eauto; rewrite <- refines_f;
      eauto;      intros v Comp_v; repeat econstructor; eauto
    | eauto].
Qed.




(* Combining the above two refinements to replace an observer with a cached value.
Lemma refinesReplaceAddCache
      Sig
      adt
      (MethodIndex_eq : forall idx idx' : MethodIndex Sig, {idx = idx'} + {idx <> idx'})
      (cachedIndex : MethodIndex Sig)
      (cacheSpec : Rep adt -> snd (MethodDomCod Sig cachedIndex) -> Prop)
      (refines_f : forall r n v, cacheSpec r v ->
                                 refine (r' <- Methods adt cachedIndex r n;
                                        ret (snd r'))
                                        (ret v))
: refineADT adt
            (replaceMethod (addCachedValue adt cacheSpec)
                             MethodIndex_eq cachedIndex
                             (fun r _ => ret (cachedVal r))).
Proof.
  eapply transitivityT. (* Example of where we can't rewrite? *)
  eapply refinesAddCachedValue.
  eapply refinesReplaceMethodCache with (repInv := fun r => cacheSpec (origRep r) (cachedVal r));
    intros; simpl.
  - intros v CompV; inversion_by computes_to_inv; subst; repeat econstructor; eauto.
  - unfold addCachedValue; simpl; intuition; eapply refines_f.
Qed. *)

(* Goals with a [pick]-ed cache value bound in a return appear when
   adding a cache to a fully deterministic method; we should simply
   consider the cache values in that case. *)
Lemma refine_pick_cache (A : Type) (m : A) cv' P :
  refine {x | P x} (ret cv') ->
  refine (cv <- {x : nat | P x};
          ret {| origRep := m; cachedVal := cv |})
         (ret {| origRep := m; cachedVal := cv' |}).
Proof.
  intros; rewrite <- refineEquiv_bind_unit with
          (x := cv') (f := fun cv => ret {| origRep := m; cachedVal := cv |}).
  apply refine_bind; eauto; reflexivity.
Qed.

Hint Resolve refine_pick_cache : cache_refinements.

(* Honing tactic for replacing an observer with a cached value. *)
(*Tactic Notation "cache" "observer" "using" "spec" constr(cSpec) :=
    let A :=
        match goal with
            |- Sharpened ?A => constr:(A) end in
    let ASig := match type of A with
                    ADT ?Sig => Sig
                end in
    let mutIdx_eq' := fresh in
    let Rep' := eval simpl in (Rep A) in
    let MethodIndex' := eval simpl in (MethodIndex ASig) in
    let ConstructorIndex' := eval simpl in (ConstructorIndex ASig) in
    let Methods' := eval simpl in (Methods A) in
  assert (forall idx idx' : MethodIndex', {idx = idx'} + {idx <> idx'})
    as mutIdx_eq' by (decide equality);
  eapply SharpenStep;
    [ eapply refinesReplaceAddCache
      with (cacheSpec := cSpec)
             (adt := A)
             (cachedIndex := ())
             (MethodIndex_eq := mutIdx_eq'); simpl
    | idtac]; cbv beta in *; simpl in *. *) *)
