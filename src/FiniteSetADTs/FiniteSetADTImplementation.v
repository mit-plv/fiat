(* Definition of the finite set spec *)
Require Export Fiat.FiniteSetADTs.FiniteSetADT.
Require Import Coq.Strings.String Coq.Sets.Ensembles
  Coq.Sets.Finite_sets Coq.Lists.List
  Coq.Sorting.Permutation Coq.MSets.MSetInterface
  Coq.MSets.MSetAVL Coq.MSets.MSetList Coq.MSets.MSetRBT
  Fiat.ADT
  Fiat.ADT.ComputationalADT
  Fiat.ADTRefinement.Core
  Fiat.ADTNotation
  Fiat.ADTRefinement.GeneralRefinements
  Fiat.Common.IterateBoundedIndex
  Fiat.Common.Ensembles.EnsembleListEquivalence.

Set Implicit Arguments.

Local Open Scope string_scope.

Module BedrockWordAsOrderedType <: OrderedType.
  Definition t : Type := W.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.
  Definition lt : t -> t -> Prop := fun x y => wlt x y = true.
  Definition lt_strorder : StrictOrder lt.
  Proof.
    constructor; repeat intro; unfold lt in *.
    { rewrite ?wlt_irrefl in *; congruence. }
    { eapply wlt_trans; eassumption. }
  Qed.
  Definition lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    repeat intro; subst; unfold eq in *; subst; reflexivity.
  Qed.
  Definition compare : t -> t -> comparison
    := fun x y => if wlt x y
                  then Datatypes.Lt
                  else if wlt y x
                       then Datatypes.Gt
                       else Datatypes.Eq.
  Definition compare_spec :
    forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    unfold lt, eq, t, compare; intros x y.
    case_eq (wlt x y); case_eq (wlt y x); intros;
    constructor; trivial.
    eapply wle_antisym; eassumption.
  Qed.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    refine (fun x y
            => (if weq x y as weqxy return weq x y = weqxy -> _
                then fun H => left (proj2 (weq_iff x y) H)
                else fun H => right _)
                 eq_refl).
    abstract (unfold eq; intros; subst;
              pose proof (proj1 (weq_iff y y) eq_refl);
              congruence).
  Defined.
End BedrockWordAsOrderedType.

Module FiniteSetADTMSet (FSMSet : SetsOn BedrockWordAsOrderedType).


  Definition FiniteSetCImpl : cADT FiniteSetSig :=
    cADTRep FSMSet.t {
      Def Constructor sEmpty (_ : unit) : rep :=
         FSMSet.empty,

      Def Method sAdd (fs : rep , w : W) : unit :=
        (FSMSet.add w fs, tt),

      Def Method sRemove (fs : rep , w : W) : unit :=
        (FSMSet.remove w fs, tt),

      Def Method sIn (fs : rep , w : W) : bool :=
        (fs, FSMSet.mem w fs),

      Def Method sSize (fs : rep , _ : unit) : W :=
        (fs, from_nat (FSMSet.cardinal fs))
    }.

  Local Ltac handle_computes_to_step_t :=
    idtac;
    match goal with
      | _ => intro
      | _ => progress simpl in *
      | _ => progress destruct_head_hnf prod
      | _ => progress destruct_head_hnf unit
      | [ |- computes_to (Bind _ _) _ ] => refine (BindComputes _ _ _)
      | [ |- computes_to (Return _) _ ] => constructor
      | [ |- computes_to (Pick _) _ ] => constructor
    end.

  Local Ltac t_step :=
    idtac;
    match goal with
      | _ => progress repeat handle_computes_to_step_t
      | _ => progress destruct_head_hnf Empty_set
      | _ => progress destruct_head_hnf or
      | _ => progress destruct_head_hnf Union
      | _ => progress destruct_head_hnf Singleton
      | _ => progress destruct_head_hnf prod
      | _ => progress destruct_head_hnf unit
      | _ => progress destruct_head_hnf False
      | _ => progress inversion_by computes_to_inv
      | _ => progress subst
      | _ => progress unfold Ensembles.In, Same_set, Included, Subtract, Setminus in *
      | _ => progress simplify_hyps
      | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
      | [ |- Empty_set _ _ ] => exfalso
      | [ |- Singleton _ _ _ ] => constructor
      | [ H : FSMSet.In _ FSMSet.empty |- _ ] => apply FSMSet.empty_spec in H
      | [ |- FSMSet.In _ (FSMSet.add _ _) ] => apply FSMSet.add_spec
      | [ H : FSMSet.In _ (FSMSet.add _ _) |- _ ] => apply FSMSet.add_spec in H
      | [ |- FSMSet.In _ (FSMSet.remove _ _) ] => apply FSMSet.remove_spec
      | [ H : FSMSet.In _ (FSMSet.remove _ _) |- _ ] => apply FSMSet.remove_spec in H
      | _ => rewrite FSMSet.cardinal_spec
      | [ |- Cardinal.cardinal _ _ _ ] => eexists
      | [ |- Datatypes.length _ = Datatypes.length _ ] => reflexivity
      | [ |- EnsembleListEquivalence _ _ ] => split
      | [ |- NoDup (FSMSet.elements _) ] => eapply NoDupA_NoDup; [ | apply FSMSet.elements_spec2w ]; try exact _
      | [ |- List.In _ (FSMSet.elements _) ] => apply InA_In_eq
      | [ |- InA _ _ (FSMSet.elements _) ] => apply FSMSet.elements_spec1
      | [ H : List.In _ (FSMSet.elements _) |- _ ] => apply InA_In_eq in H
      | [ H : InA _ _ (FSMSet.elements _) |- _ ] => apply FSMSet.elements_spec1 in H
      | [ |- FSMSet.mem _ _ = true ] => apply FSMSet.mem_spec
      | [ H : FSMSet.mem _ _ = true |- _ ] => apply FSMSet.mem_spec in H
      | [ H : ~Singleton _ ?x ?x |- _ ] => exfalso; apply H; clear
      | [ |- _ /\ _ ] => split
      | [ |- _ <-> _ ] => split
      | [ |- ?G ] => not has_evar G; solve [ eauto with nocore ]
      | [ |- ?G ] => not has_evar G; left; reflexivity
      | [ |- ?G ] => not has_evar G; right; reflexivity
      | [ |- ?G ] => not has_evar G; right; solve [ hnf; eauto with nocore ]
      | [ |- ?G ] => not has_evar G; left; solve [ hnf; eauto with nocore ]
    end.

  Local Ltac t := repeat repeat repeat t_step.

  Local Arguments cConstructors _ _ _ _ / .
  Local Arguments cMethods _ _ _ _ _ / .

  Definition FiniteSetImpl : FullySharpened FiniteSetSpec.
  Proof.
    exists FiniteSetCImpl.
    exists (fun S0 fs => Same_set _ S0 (fun w => FSMSet.In w fs));
      eapply Iterate_Dep_Type_BoundedIndex_equiv_1; simpl;
      unfold FiniteSetADT.cardinal;
      repeat split; t.
  Defined.

End FiniteSetADTMSet.

Module MSetAVL_BedrockWord := MSetAVL.Make BedrockWordAsOrderedType.
Module Export FiniteSetADTMSetAVL := FiniteSetADTMSet MSetAVL_BedrockWord.
Module MSetList_BedrockWord := MSetList.Make BedrockWordAsOrderedType.
Module Export FiniteSetADTMSetList := FiniteSetADTMSet MSetList_BedrockWord.
Module MSetRBT_BedrockWord := MSetRBT.Make BedrockWordAsOrderedType.
Module Export FiniteSetADTMSetRBT := FiniteSetADTMSet MSetRBT_BedrockWord.
