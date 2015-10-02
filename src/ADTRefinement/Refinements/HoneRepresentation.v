Require Import Fiat.Common
        Fiat.Computation
        Fiat.ADT.ADTSig
        Fiat.ADT.Core
        Fiat.ADTRefinement.Core Fiat.ADTRefinement.SetoidMorphisms
        Fiat.ADTRefinement.GeneralRefinements.

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

  Fixpoint absMethod'
             (dom : list Type)
             (cod : Type)
    : (oldRep -> methodType' oldRep cod dom)
      -> newRep -> (methodType' newRep cod dom) :=
    match dom return
          (oldRep -> methodType' oldRep cod dom)
          -> newRep -> (methodType' newRep cod dom)
    with
    | nil =>
      fun oldMethod nr =>
        {nr' | forall or,
            or ≃ nr ->
            exists or',
              (oldMethod or) ↝ or' /\
              fst or' ≃ fst nr' /\ snd or' = snd nr'}%comp
    | cons d dom' =>
      fun oldMethod nr t =>
        absMethod' dom' cod (fun or => oldMethod or t) nr
    end.

  Definition absMethod
             (dom : list Type)
             (cod : Type)
             (oldMethod : methodType oldRep dom cod)
    : methodType newRep dom cod :=
    absMethod' dom cod oldMethod.

  Lemma refine_absMethod
        (dom : list Type)
        (cod : Type)
        (oldMethod : methodType oldRep dom cod)
  : @refineMethod oldRep newRep AbsR _ _
                   oldMethod
                   (absMethod oldMethod).
  Proof.
    induction dom.
    - simpl in *; unfold refineMethod, refineMethod',
                  absMethod, absMethod', refine; intros; computes_to_inv.
      destruct (H0 _ H) as [or' [Comp_or [AbsR_or'' eq_or''] ] ].
      repeat computes_to_econstructor; eauto.
      destruct v; simpl in *; subst; econstructor.
    - intro; simpl; intros.
      eapply (IHdom (fun or => oldMethod or d)); eauto.
  Qed.

  Hint Resolve refine_absMethod.

  (* A similar approach works for constructors. *)
  Fixpoint absConstructor
             {dom : list Type}
    : constructorType oldRep dom ->
      constructorType newRep dom :=
    match dom return
          constructorType oldRep dom ->
          constructorType newRep dom
    with
    | nil =>
      fun oldConstr =>
      {nr | exists or', oldConstr ↝ or' /\
                        or' ≃ nr }%comp
    | cons d dom' =>
      fun oldConstr t =>
        @absConstructor dom' (oldConstr t)
    end.

  Lemma refine_absConstructor
        (dom : list Type)
        (oldConstr : constructorType oldRep dom)
  : @refineConstructor oldRep newRep AbsR _ oldConstr
                    (absConstructor oldConstr).
  Proof.
    induction dom; simpl in *.
    - unfold refineConstructor, absConstructor, refine; intros.
      computes_to_inv; eauto.
    - intros; eapply IHdom.
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

(* Always unfold absMutatorMethods and absObserverMethods.
Global Arguments absMethod oldRep newRep AbsR Dom Cod oldMethod / nr n.
Global Arguments absConstructor oldRep newRep AbsR Dom oldConstr / n . *)

(* Honing tactic for refining the ADT representation which provides
   default observer and mutator implementations. *)
Tactic Notation "hone" "representation" "using" constr(AbsR') :=
    eapply SharpenStep;
    [eapply refineADT_Build_ADT_Rep_default with (AbsR := AbsR') | ].
