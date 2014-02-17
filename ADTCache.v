Require Import Common Computation ADT Ensembles ADTRefinement.

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
       We first running the old mutators
       to obtain the original mutated representation [or], then we add
       Pick implementation of the [cacheSpec] specification to the result. *)

  Definition AddCacheEntry
             {MutatorIndex}
             (MutatorMethods : MutatorIndex -> mutatorMethodType rep)
             (cacheSpec : rep -> cacheTyp -> Prop)
             idx r n :=
    or <- MutatorMethods idx (origRep r) n;
    cv <- Pick (cacheSpec or);
    ret {| origRep := or;
           cachedVal := cv |}.

  Variable repInv : Ensemble rep.

  (* A representation augmented with a cache should satisfy the
     original invariant [repInv], and the cache should satisfy [cacheSpec].*)
  Definition ValidCacheInv
             (cacheSpec : rep -> cacheTyp -> Prop)
             (r : cachedRep) :=
    repInv (origRep r) /\ cacheSpec (origRep r) (cachedVal r).

  (* Mutators updated with [AddCacheEntry] preserve the [ValidCacheInv] invariant. *)
  Lemma AddCacheEntryInv {MutatorIndex}:
    forall
      (MutatorMethods : MutatorIndex -> mutatorMethodType rep)
      (MutatorMethodsInv :
         forall (idx : MutatorIndex) (r : rep) (n : nat),
           repInv r -> computational_inv repInv (MutatorMethods idx r n))
      (cacheSpec : rep -> cacheTyp -> Prop),
      mutatorInv
        (fun r => ValidCacheInv cacheSpec r)
        (AddCacheEntry MutatorMethods cacheSpec).
  Proof.
    unfold AddCacheEntry, ValidCacheInv; simpl; intros.
    inversion_by computes_to_inv; subst; eauto.
  Qed.

End addCache.

Definition addCachedValue {cacheTyp} adt (cacheSpec : Rep adt -> cacheTyp -> Prop)
: ADT :=
  {| Rep := cachedRep (Rep adt) cacheTyp;
     RepInv r := ValidCacheInv (RepInv adt) cacheSpec r; (* *)
     ObserverIndex := ObserverIndex adt;
     MutatorIndex := MutatorIndex adt;
     ObserverMethods idx r := ObserverMethods adt idx (origRep r);
     MutatorMethods := AddCacheEntry (MutatorMethods adt) cacheSpec;
     MutatorMethodsInv := AddCacheEntryInv (MutatorMethodsInv adt) (cacheSpec := cacheSpec) |}.

Theorem refinesAddCachedValue
        {cacheTyp}
        adt
        (cacheSpec : Rep adt -> cacheTyp -> Prop)
: refineADT adt (addCachedValue adt cacheSpec).
Proof.
  unfold addCachedValue, ValidCacheInv; destruct adt.
  econstructor 1 with
  (abs := fun r : cachedRep Rep cacheTyp =>  ret (origRep r))
    (mutatorMap := @id MutatorIndex) (* Have to specify MutatorIndex in order to
                                        unify- 8.5 might fix this? *)
    (observerMap := @id ObserverIndex); simpl; unfold id; unfold AddCacheEntry;
  intros; autorewrite with refine_monad.
  - unfold refine; intros; inversion_by computes_to_inv; subst; eauto.
  - reflexivity.
  - inversion_by computes_to_inv; subst; eauto.
Qed.

Definition replaceObserverCache adt
           (ObserverIndex_eq : forall idx idx' : ObserverIndex adt, {idx = idx'} + {idx <> idx'})
           (f : Rep adt -> nat -> Comp nat)
           (cachedIndex : ObserverIndex adt)
: ADT :=
  {| Rep := Rep adt;
     RepInv := RepInv adt;
     ObserverIndex := ObserverIndex adt;
     MutatorIndex := MutatorIndex adt;
     ObserverMethods idx :=
       if (ObserverIndex_eq idx cachedIndex) then
         f
       else
         ObserverMethods adt idx;
     MutatorMethods := MutatorMethods adt;
     MutatorMethodsInv := MutatorMethodsInv adt |}.

(* Currently think it's good practice to expand ADT building blocks. *)
Arguments replaceObserverCache / .
Arguments addCachedValue / .
Arguments ValidCacheInv / .
Arguments AddCacheEntry / .

Lemma refinesReplaceObserverCache
      adt
      (ObserverIndex_eq : forall idx idx' : ObserverIndex adt, {idx = idx'} + {idx <> idx'})
      (f : Rep adt -> nat -> Comp nat)
      (cachedIndex : ObserverIndex adt)
      (refines_f : forall r n, RepInv adt r -> refine (ObserverMethods adt cachedIndex r n) (f r n))
: refineADT adt (replaceObserverCache adt ObserverIndex_eq f cachedIndex).
Proof.
  unfold replaceObserverCache; destruct adt; simpl.
  econstructor 1 with (abs := fun r : Rep => ret r)
                        (mutatorMap := @id MutatorIndex) (* Have to specify MutatorIndex in order to
                                        unify- 8.5 might fix this? *)
                        (observerMap := @id ObserverIndex); simpl in *|-*; unfold id; intros;
                                                                    autorewrite with refine_monad.
  - reflexivity.
  - find_if_inside; subst; [eauto | reflexivity].
  - inversion_by computes_to_inv; subst; eauto.
Qed.

(* Combining the above two refinements to replace an observer with a cached value. *)
Lemma refinesReplaceAddCache
      adt
      (ObserverIndex_eq : forall idx idx' : ObserverIndex adt, {idx = idx'} + {idx <> idx'})
      (cacheSpec : Rep adt -> nat -> Prop)
      (cachedIndex : ObserverIndex adt)
      (refines_f : forall r n v, cacheSpec r v ->
                                 refine (ObserverMethods adt cachedIndex r n) (ret v))
: refineADT adt
            (replaceObserverCache (addCachedValue adt cacheSpec)
                                  ObserverIndex_eq (fun r _ => ret (cachedVal r)) cachedIndex).
Proof.
  etransitivity. (* Example of where we can't rewrite? *)
  eapply refinesAddCachedValue.
  eapply refinesReplaceObserverCache.
  unfold addCachedValue, ValidCacheInv; simpl; intuition.
Qed.

(* Honing tactic for replacing an observer with a cached value. *)
Tactic Notation "cache" "observer" "using" "spec" constr(cSpec) :=
  let A := match goal with |- Sharpened ?A => constr:(A) end in
  let mutIdx_eq' := fresh in
  assert (forall idx idx' : MutatorIndex A, {idx = idx'} + {idx <> idx'})
    as mutIdx_eq' by (decide equality);
  eapply SharpenStep;
    [ eapply refinesReplaceAddCache
      with (cacheSpec := cSpec)
             (adt :=  A)
             (cachedIndex := ())
             (ObserverIndex_eq := mutIdx_eq'); simpl
    | idtac]; simpl.
