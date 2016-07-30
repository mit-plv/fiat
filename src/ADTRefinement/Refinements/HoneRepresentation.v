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
           (cod : option Type)
    : methodType' oldRep dom cod
      -> methodType' newRep dom cod :=
    match dom return
          methodType' oldRep dom cod
          -> methodType' newRep dom cod
    with
    | nil =>
      match cod return
            methodType' oldRep [] cod
            -> methodType' newRep [] cod
      with
      | Some cod' =>
        fun oldMethod =>
          {nr' | exists or',
                 oldMethod ↝ or' /\
                 fst or' ≃ fst nr' /\ snd or' = snd nr'}%comp
      | None =>
        fun oldMethod =>
          {nr' | exists or',
                 oldMethod ↝ or' /\ or' ≃ nr'}%comp
      end
    | cons d dom' =>
      fun oldMethod t =>
        absMethod' dom' cod (oldMethod t)
    end.

  Fixpoint absMethod
           arity
           {dom cod}
           {struct arity}
    : methodType arity oldRep dom cod
      -> methodType arity newRep dom cod.
  Admitted.
  (*refine (match arity return
                  methodType arity oldRep dom cod
                  -> methodType arity newRep dom cod
            with
            | 0 => absMethod' dom cod
            | S arity' => _
            end).
    simpl; intros.
    admit.
  Defined. *)

  Lemma refine_absMethod
        arity
        (dom : list Type)
        (cod : option Type)
        (oldMethod : methodType arity oldRep dom cod)
  : @refineMethod oldRep newRep AbsR arity _ _
                   oldMethod
                   (absMethod arity oldMethod).
  Proof.
    induction dom.
  Admitted.
  (*- simpl in *; unfold refineMethod, refineMethod',
                  absMethod, absMethod', refine; intros;
      destruct cod; intros; computes_to_inv.
      + destruct (H0 _ H) as [or' [Comp_or [AbsR_or'' eq_or''] ] ].
        repeat computes_to_econstructor; eauto.
        destruct v; simpl in *; subst; econstructor.
      + destruct (H0 _ H) as [or' [Comp_or AbsR_or'' ] ].
        repeat computes_to_econstructor; eauto.
    - intro; simpl; intros.
      eapply (IHdom (fun or => oldMethod or d)); eauto.
  Qed. *)

  Hint Resolve refine_absMethod.

  (* We can refine an ADT using the default mutator and observer
     implementations provided by [absMutatorMethod] and [absObserverMethod]. *)
  Lemma refineADT_Build_ADT_Rep_default
        Sig
        oldMeths :
    refineADT
      (@Build_ADT Sig oldRep oldMeths)
      (@Build_ADT Sig newRep
                  (fun idx => absMethod _ (oldMeths idx))).
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
