Require Import Fiat.Common
        Fiat.Computation
        Fiat.ADT.ADTSig
        Fiat.ADT.Core
        Fiat.ADT.ComputationalADT
        Fiat.ADTRefinement.Core
        Fiat.ADTRefinement.SetoidMorphisms
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

  Fixpoint unCurry_Dom
           (fDom : list Type)
    : Type :=
    match fDom with
    | nil => unit
    | cons T fDom' => prod T (unCurry_Dom fDom')
    end.

  Fixpoint unCurry_methodType'
           (rep : Type)
           (dom : list Type)
           {cod : option Type}
           (f : methodType' rep dom cod)
           {struct dom}
    : methodType' rep (cons (unCurry_Dom dom) nil) cod :=
    match dom return
          methodType' rep dom cod
          -> methodType' rep (cons (unCurry_Dom dom) nil) cod
    with
    | nil => fun f _ => f
    | cons T dom' => fun f t => unCurry_methodType' rep dom' (f (fst t)) (snd t)
    end f.

  Definition unCurried_methodType
           (arity : nat)
           (rep : Type)
           (dom : list Type)
           (cod : option Type)
    : Type := Vector.t rep arity -> methodType' rep (cons (unCurry_Dom dom) nil) cod.

  Fixpoint unCurry_methodType
           (arity : nat)
           {rep : Type}
           {dom : list Type}
           {cod : option Type}
           (f : methodType arity rep dom cod)
    : unCurried_methodType arity rep dom cod :=
    match arity return
          methodType arity rep dom cod
          -> unCurried_methodType arity rep dom cod with
    | 0 => fun meth v => unCurry_methodType' _ _ meth
    | S n' => fun meth v => unCurry_methodType (arity := n') (meth (Vector.hd v)) (Vector.tl v)
    end f.

  Fixpoint Curry_methodType'
           (rep : Type)
           (dom : list Type)
           {cod : option Type}
           (f : methodType' rep (cons (unCurry_Dom dom) nil) cod)
           {struct dom}
    : methodType' rep dom cod :=
    match dom return
          methodType' rep (cons (unCurry_Dom dom) nil) cod
          -> methodType' rep dom cod
    with
    | nil => fun f => f tt
    | cons T dom' => fun f t => Curry_methodType' _ (fun t' => f (t, t'))
    end f.

  Fixpoint Curry_methodType
           (arity : nat)
           (rep : Type)
           (dom : list Type)
           {cod : option Type}
           (f : unCurried_methodType arity rep dom cod)
           {struct arity}
    : methodType arity rep dom cod :=
    match arity return
          unCurried_methodType arity rep dom cod
          -> methodType arity rep dom cod
    with
    | 0 => fun f => Curry_methodType' _ (f (Vector.nil _))
    | S n' => fun f t => Curry_methodType (fun t' => f (Vector.cons _ t _ t'))
    end f.

  Lemma refineFunEquiv_unCurry
        (arity : nat)
        (rep : Type)
        (dom : list Type)
        {cod : option Type}
    : forall (f : methodType arity rep dom cod),
      refineMethod eq _ f (Curry_methodType (unCurry_methodType f)).
  Proof.
    induction arity; simpl.
    - induction dom; simpl.
      + destruct cod; simpl.
        * intros f [v v'] Comp_v; repeat (computes_to_econstructor; eauto).
        * intros f v Comp_v; repeat (computes_to_econstructor; eauto).
      + simpl; intros; eapply IHdom.
    - simpl; intros; subst; eauto.
  Qed.

  Lemma refineMethod_Curry_Some
        {arity : nat}
        {rep : Type}
        {dom : list Type}
        {cod : Type}
    : forall (f f' : unCurried_methodType arity rep dom (Some cod)),
      (forall r_ns ds, refine (f r_ns ds) (f' r_ns ds))
      -> refineMethod_eq rep arity (Curry_methodType f) (Curry_methodType f').
  Proof.
    induction arity; simpl; intros.
    - induction dom; unfold unCurried_methodType in *; intros; simpl in *.
      + eapply H.
      + intros; eapply (IHdom (fun r_ns' t' => f r_ns' (d, t')) (fun r_ns' t' => f' r_ns' (d, t') ));
          eauto.
    - intros; simpl in *; eauto.
  Qed.
  
  Lemma refineMethod_Curry_None
        {arity : nat}
        {rep : Type}
        {dom : list Type}
    : forall (f f' : unCurried_methodType arity rep dom None),
      (forall r_ns ds, refine (f r_ns ds) (f' r_ns ds))
      -> refineMethod_eq rep arity (Curry_methodType f) (Curry_methodType f').
  Proof.
    induction arity; simpl; intros.
    - induction dom; unfold unCurried_methodType in *; intros; simpl in *.
      + eapply H.
      + intros; eapply (IHdom (fun r_ns' t' => f r_ns' (d, t')) (fun r_ns' t' => f' r_ns' (d, t') ));
          eauto.
    - intros; simpl in *; eauto.
  Qed.

  Fixpoint absMethod'
           (dom : list Type)
           (cod : option Type)
           (oldMeth : methodType' oldRep dom cod)
           {struct dom}
    : methodType' newRep (cons (unCurry_Dom dom) nil) cod :=
    match dom return
          methodType' oldRep dom cod ->
          methodType' newRep (cons (unCurry_Dom dom) nil) cod
    with
    | nil =>
      match cod return
            methodType' oldRep [] cod
            -> methodType' newRep (cons (unCurry_Dom []) nil) cod
      with
      | Some cod' =>
        fun oldMeth _ =>
          {nr' | exists or',
                 oldMeth ↝ or' /\ fst or' ≃ fst nr' /\ snd or' = snd nr'}%comp
      | None =>
        fun oldMeth _ =>
          {nr' | exists or',
                 oldMeth ↝ or' /\ or' ≃ nr'}%comp
         end
    | cons d dom' =>
      fun oldMeth dom'' => absMethod' dom' cod (oldMeth (fst dom'')) (snd dom'')
    end oldMeth.

  Fixpoint absMethod_Some
           (arity : nat)
           (dom : list Type)
           (cod : Type)
           (oldMeth : methodType arity oldRep dom (Some cod))
           {struct arity}
    : unCurried_methodType arity newRep dom (Some cod) :=
    match arity return
          methodType arity oldRep dom (Some cod) ->
          unCurried_methodType arity newRep dom (Some cod)
    with
    | 0 => fun oldMeth _ => absMethod' dom (Some cod) oldMeth
    | S n' => fun oldMeth reps args v =>
                forall r_o,
                  r_o ≃ Vector.hd reps
                  -> absMethod_Some dom (oldMeth r_o) (Vector.tl reps) args v
    end oldMeth.

    Fixpoint absMethod_None
           (arity : nat)
           (dom : list Type)
           (oldMeth : methodType arity oldRep dom None)
           {struct arity}
    : unCurried_methodType arity newRep dom None :=
    match arity return
          methodType arity oldRep dom None ->
          unCurried_methodType arity newRep dom None
    with
    | 0 => fun oldMeth _ => absMethod' dom None oldMeth
    | S n' => fun oldMeth reps args v =>
                forall r_o,
                  r_o ≃ Vector.hd reps
                  -> absMethod_None dom (oldMeth r_o) (Vector.tl reps) args v
    end oldMeth.

    Definition absMethod
               {arity : nat}
               {dom : list Type}
               {cod : option Type}
               (oldMeth : methodType arity oldRep dom cod)
      : methodType arity newRep dom cod :=
      Curry_methodType (match cod return
                              methodType arity oldRep dom cod
                              -> unCurried_methodType arity newRep dom cod with
                        | Some cod => absMethod_Some _ (cod := cod)
                        | None => absMethod_None _
                        end oldMeth).

    Local Transparent computes_to.
    Lemma refine_absMethod
          arity
          (dom : list Type)
          (cod : option Type)
          (oldMethod : methodType arity oldRep dom cod)
      : @refineMethod oldRep newRep AbsR arity _ _
                      oldMethod
                      (absMethod oldMethod).
    Proof.
      induction arity.
      - simpl in *; induction dom; simpl in *.
        + destruct cod.
          * unfold absMethod; simpl; intros [r_n' v] Comp_v;
              computes_to_inv; subst; destruct_ex; intuition subst;
                simpl in *; subst.
            computes_to_econstructor; eauto.
          * unfold absMethod; simpl; intros r_n' Comp_v;
              computes_to_inv; subst; destruct_ex; intuition subst;
                simpl in *; subst.
            computes_to_econstructor; eauto.
        + intros; unfold absMethod in *; simpl in *.
          destruct cod;
            eapply (IHdom (oldMethod d)).
      - unfold absMethod in *; simpl; intros.
        pose proof (IHarity (oldMethod r_o)); clear IHarity.
        destruct cod; simpl in *.
        + eapply refineMethod_eq_trans; eauto.
          eapply refineMethod_Curry_Some; simpl; intros.
          intros v Comp_v.
          unfold computes_to in Comp_v; apply Comp_v in H; eauto.
        + eapply refineMethod_eq_trans; eauto.
          eapply refineMethod_Curry_None; simpl; intros.
          intros v Comp_v.
          unfold computes_to in Comp_v; apply Comp_v in H; eauto.
    Qed.

    Opaque computes_to.

  Hint Resolve refine_absMethod.

  (* We can refine an ADT using the default mutator and observer
     implementations provided by [absMutatorMethod] and [absObserverMethod]. *)
  Lemma refineADT_Build_ADT_Rep_default
        Sig
        oldMeths :
    refineADT
      (@Build_ADT Sig oldRep oldMeths)
      (@Build_ADT Sig newRep
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
