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

  (* To add a cache, we update an ADT's mutators to include cached values.
       We first run the old mutators to obtain the original mutated
       representation [r_o], then we add a Pick implementation of a [cacheVal]
       that satisfies our specification [cacheSpec] to the result. *)

  Variable cacheSpec : rep -> cacheTyp -> Prop.

  Definition AddCacheEntry
             {MutatorIndex}
             {MutatorDom : MutatorIndex -> Type}
             (MutatorMethods :
                forall idx, mutatorMethodType rep (MutatorDom idx))
             idx r n :=
    or <- MutatorMethods idx (origRep r) n;
    cv <- {cr : cacheTyp | cacheSpec or cr };
    ret {| origRep := or;
           cachedVal := cv |}.

  (* A representation with an added value [r_n] is related to any representation [r_o]
     when the cached value [cachedVal] satisfies the original [cacheSpec] and
     the original representation of [r_n] is equal to [r_o]. *)

  Definition cachedRepBiR
	     (r_o : rep)
             (r_n : cachedRep) :=
    r_o = origRep r_n /\ cacheSpec (origRep r_n) (cachedVal r_n).

End addCache.

Definition addCachedValue Sig cacheTyp adt cacheSpec
: ADT Sig :=
  {| Rep := cachedRep (Rep adt) cacheTyp;
     ObserverMethods idx r := ObserverMethods adt idx (origRep r);
     MutatorMethods := AddCacheEntry cacheSpec (MutatorMethods adt)|}.

Theorem refinesAddCachedValue Sig
        {cacheTyp}
        adt
        (cacheSpec : Rep adt -> cacheTyp -> Prop)
: @refineADT Sig adt (addCachedValue adt cacheSpec).
Proof.
  unfold addCachedValue; destruct adt.
  econstructor 1 with
  (SiR := fun r_o r_n => r_o = origRep r_n /\ cacheSpec (origRep r_n) (cachedVal r_n)); unfold AddCacheEntry; simpl;
  intros; autorewrite with refine_monad.
  - unfold refine; intros; inversion_by computes_to_inv; subst; eauto.
  - intros v CompV; inversion_by computes_to_inv; subst; eauto.
Qed.

(* Currently think it's good practice to expand ADT building blocks. *)
Arguments addCachedValue / .
Arguments AddCacheEntry / .

Local Obligation Tactic := intros; subst; eauto.

Program Definition replaceObserver Sig adt
           (ObserverIndex_eq : forall idx idx' : ObserverIndex Sig, {idx = idx'} + {idx <> idx'})
           (cachedIndex : ObserverIndex Sig)
           (f : Rep adt -> (ObserverDom Sig cachedIndex)
                -> Comp (ObserverCod Sig cachedIndex))
: ADT Sig :=
  {| Rep := Rep adt;
     ObserverMethods idx :=
       if (ObserverIndex_eq idx cachedIndex) then
         _
       else
         ObserverMethods adt idx;
     MutatorMethods := MutatorMethods adt|}.

Arguments replaceObserver / .

Arguments addCachedValue / .
Arguments AddCacheEntry / .

Lemma refinesReplaceObserverCache
      Sig
      adt
      (repInv : Ensemble (Rep adt))
      (ObserverIndex_eq : forall idx idx' : ObserverIndex Sig, {idx = idx'} + {idx <> idx'})
      (cachedIndex : ObserverIndex Sig)
      (f : Rep adt -> (ObserverDom Sig cachedIndex)
           -> Comp (ObserverCod Sig cachedIndex))
      (MutBiR : forall idx (r : Rep adt) n,
                  repInv r ->
                  refine
                    (r' <- MutatorMethods adt idx r n;
                     {r'' : Rep adt | repInvSiR repInv r' r''})
                    (MutatorMethods adt idx r n))
      (refines_f : forall r n,
                     repInv r ->
                     refine (ObserverMethods adt cachedIndex r n) (f r n))
: refineADT adt (replaceObserver adt ObserverIndex_eq cachedIndex f).
Proof.
  unfold replaceObserver; destruct adt; simpl.
  econstructor 1 with (SiR := repInvSiR repInv (rep := Rep));
    simpl in *|-*; unfold id, repInvSiR; intros; intuition; subst; eauto.
  - destruct (ObserverIndex_eq idx cachedIndex);
    [unfold replaceObserver_obligation_1, eq_rect_r, eq_rect; 
      destruct e; simpl; eauto
     | reflexivity ].
Qed.

(* Combining the above two refinements to replace an observer with a cached value. *)
Lemma refinesReplaceAddCache
      Sig
      adt
      (ObserverIndex_eq : forall idx idx' : ObserverIndex Sig, {idx = idx'} + {idx <> idx'})
      (cachedIndex : ObserverIndex Sig)
      (cacheSpec : Rep adt -> ObserverCod Sig cachedIndex -> Prop)
      (refines_f : forall r n v, cacheSpec r v ->
                                 refine (ObserverMethods adt cachedIndex r n) (ret v))
: refineADT adt
            (replaceObserver (addCachedValue adt cacheSpec)
                             ObserverIndex_eq cachedIndex
                             (fun r _ => ret (cachedVal r))).
Proof.
  etransitivity. (* Example of where we can't rewrite? *)
  eapply refinesAddCachedValue.
  eapply refinesReplaceObserverCache with (repInv := fun r => cacheSpec (origRep r) (cachedVal r));
    intros; simpl.
  - intros v CompV; inversion_by computes_to_inv; subst; repeat econstructor; eauto.
  - unfold addCachedValue; simpl; intuition; eapply refines_f.
Qed.

(* Goals with a [pick]-ed cache value bound in a return appear when
   adding a cache to a fully deterministic mutator; we should simply
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
Tactic Notation "cache" "observer" "using" "spec" constr(cSpec) :=
  let A := match goal with |- Sharpened ?A => constr:(A) end in
  let mutIdx_eq' := fresh in
  let Rep' := eval simpl in (Rep A) in
    let MutatorIndex' := eval simpl in (MutatorIndex A) in
    let ObserverIndex' := eval simpl in (ObserverIndex A) in
    let MutatorMethods' := eval simpl in (MutatorMethods A) in
    let ObserverMethods' := eval simpl in (ObserverMethods A) in
  assert (forall idx idx' : MutatorIndex', {idx = idx'} + {idx <> idx'})
    as mutIdx_eq' by (decide equality);
  eapply SharpenStep;
    [ eapply refinesReplaceAddCache
      with (cacheSpec := cSpec)
             (adt := A)
             (cachedIndex := ())
             (ObserverIndex_eq := mutIdx_eq'); simpl
    | idtac]; cbv beta in *; simpl in *.
