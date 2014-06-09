Require Import Common Computation ADT Ensembles ADTRefinement ADTRepInv.

Generalizable All Variables.
Set Implicit Arguments.

Open Scope comp_scope.

Section addCache.

  (* A cache simply adds a new value to an ADT's representation [rep]. *)

  Variable rep : Type.
  Variable cacheTyp : Type.

  Record cachedRep := cOb
                        { origRep : rep;
                          cachedVal : cacheTyp
                        }.

  (* To add a cache, we update an ADT's methods to include cached values.
       We first run the old mutators to obtain the original mutated
       representation [r_o], then we add a Pick implementation of a [cacheVal]
       that satisfies our specification [cacheSpec] to the result. *)

  Variable cacheSpec : rep -> cacheTyp -> Prop.

  Definition MethodAddCacheEntry
             {MethodIndex}
             {MethodDomCod : MethodIndex -> Type * Type}
             (Methods :
                forall idx,
                  methodType rep
                             (fst (MethodDomCod idx))
                             (snd (MethodDomCod idx)))
             idx r n :=
    or <- Methods idx (origRep r) n;
    cv <- {cr : cacheTyp | cacheSpec (fst or) cr };
    ret ({| origRep := fst or;
           cachedVal := cv |}, snd or).

  Definition ConstructorAddCacheEntry
             {ConstructorIndex}
             {ConstructorDom : ConstructorIndex -> Type}
             (Constructors :
                forall idx,
                  constructorType rep (ConstructorDom idx))
             idx n :=
    or <- Constructors idx n;
    cv <- {cr : cacheTyp | cacheSpec or cr };
    ret {| origRep := or;
           cachedVal := cv |}.

  (* A representation with an added value [r_n] is related to any representation [r_o]
     when the cached value [cachedVal] satisfies the original [cacheSpec] and
     the original representation of [r_n] is equal to [r_o]. *)

  Definition cachedRepAbsR
	     (r_o : rep)
             (r_n : cachedRep) :=
    r_o = origRep r_n /\ cacheSpec (origRep r_n) (cachedVal r_n).

End addCache.

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
    | idtac]; cbv beta in *; simpl in *. *)
