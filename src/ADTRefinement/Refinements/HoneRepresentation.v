Require Import Common Computation
        ADT.ADTSig ADT.Core
        ADTRefinement.Core ADTRefinement.SetoidMorphisms
        ADTRefinement.GeneralRefinements.

(* A generic refinement and honing tactic for switching the
    representation of an ADT. *)

Section HoneRepresentation.

  Variable oldRep : Type. (* The old representation type. *)
  Variable newRep : Type. (* The new representation type. *)

  (* The abstraction relation between old and new representations. *)
  Variable AbsR : oldRep -> newRep -> Prop.
  Local Infix "≃" := (AbsR) (at level 70).

  (* When switching representations, we can always build a default
     implementation (computation?) for the methods of an ADT by
     using the old methods. *)

  Definition absMethod
        (Dom Cod : Type)
        (oldMethod : methodType oldRep Dom Cod) nr n
  : Comp (newRep * Cod) :=
    {nr' | forall or,
             or ≃ nr ->
             exists or',
               (oldMethod or n) ↝ or' /\
               fst or' ≃ fst nr' /\ snd or' = snd nr'}%comp.

  Lemma refine_absMethod
        (Dom Cod : Type)
        (oldMethod : methodType oldRep Dom Cod)
  : @refineMethod oldRep newRep AbsR _ _
                   oldMethod
                   (absMethod oldMethod).
  Proof.
    unfold refineMethod, absMethod, refine; intros.
    inversion_by computes_to_inv.
    destruct (H0 _ H) as [or' [Comp_or [AbsR_or'' eq_or''] ] ].
    repeat econstructor; eauto.
    destruct v; simpl in *; subst; econstructor.
  Qed.

  Hint Resolve refine_absMethod.

  (* A similar approach works for constructors. *)
  Definition absConstructor
             (Dom : Type)
             (oldConstr : constructorType oldRep Dom)
             n
  : Comp newRep :=
    {nr | exists or', oldConstr n ↝ or' /\
                      or' ≃ nr }%comp.

  Lemma refine_absConstructor
        (Dom : Type)
        (oldConstr : constructorType oldRep Dom)
  : @refineConstructor oldRep newRep AbsR _ oldConstr
                    (absConstructor oldConstr).
  Proof.
    unfold refineConstructor, absConstructor, refine; intros.
    inversion_by computes_to_inv; eauto.
  Qed.

  Hint Resolve refine_absConstructor.

  (* We can refine an ADT using the default mutator and observer
     implementations provided by [absMutatorMethod] and [absObserverMethod]. *)
  Lemma refineADT_Build_ADT_Rep_default
        Sig
        oldConstrs oldMeths :
    refineADT
      (@Build_ADT Sig oldRep oldConstrs oldMeths)
      (@Build_ADT Sig newRep
                  (fun idx => absConstructor (oldConstrs idx))
                  (fun idx => absMethod (oldMeths idx))).
  Proof.
    eapply refineADT_Build_ADT_Rep; eauto.
  Qed.

End HoneRepresentation.

(* Always unfold absMutatorMethods and absObserverMethods. *)
Global Arguments absMethod oldRep newRep AbsR Dom Cod oldMethod / nr n.
Global Arguments absConstructor oldRep newRep AbsR Dom oldConstr / n .

(* Honing tactic for refining the ADT representation which provides
   default observer and mutator implementations. *)
Tactic Notation "hone" "representation" "using" constr(AbsR') :=
    eapply SharpenStep;
    [eapply refineADT_Build_ADT_Rep_default with (AbsR := AbsR') | ].
