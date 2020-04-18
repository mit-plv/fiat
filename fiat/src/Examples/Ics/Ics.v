Require Import Fiat.ADTNotation.BuildADT Fiat.ADTNotation.BuildComputationalADT Fiat.ADTNotation.BuildADTSig.
Require Import Fiat.ADTRefinement.GeneralRefinements Fiat.Common.ilist.
Require Import Fiat.ADTRefinement.BuildADTRefinements.HoneRepresentation.
Require Import Fiat.ADT.ComputationalADT.
(*What was this importing?*)
(*Require Import Core.*)
Require Import Fiat.ADTRefinement.GeneralBuildADTRefinements.
Require Import Fiat.ADT.ComputationalADT Fiat.ADTRefinement.GeneralBuildADTRefinements.

Require Import Coq.Bool.Bool Coq.ZArith.ZArith.

Export ADTNotation.BuildADT ADTNotation.BuildComputationalADT ADTNotation.BuildADTSig.
Export ADTRefinement.GeneralRefinements ADT.ComputationalADT Core.
Export ADTRefinement.BuildADTRefinements.HoneRepresentation ADTRefinement.GeneralBuildADTRefinements.
Export Bool ZArith String List.

Global Open Scope Z_scope.
Global Open Scope ADT_scope.
Global Open Scope string_scope.
Global Open Scope list_scope.
Global Open Scope ADTSig_scope.

Ltac implement1 := intros;
  repeat match goal with
         | [ |- context[if ?b then _ else _] ] => case_eq b; intros
         | [ H : _ && _ = true |- _ ] => apply andb_true_iff in H; destruct H
         | [ H : _ && _ = false |- _ ] => apply andb_false_iff in H; destruct H
         | [ H : (?x <? ?y) = _ |- _ ] => let Hcases := fresh in generalize (Zlt_cases x y); intro Hcases;
                                            rewrite H in Hcases; clear H
         | [ H : (?x >? ?y) = _ |- _ ] => let Hcases := fresh in generalize (Zgt_cases x y); intro Hcases;
                                            rewrite H in Hcases; clear H
         | [ H : (?x >=? ?y) = _ |- _ ] => let Hcases := fresh in generalize (Zge_cases x y); intro Hcases;
                                             rewrite H in Hcases; clear H
         | [ H : _ = Lt |- _ ] => apply (proj1 (Z.compare_lt_iff _ _)) in H
         | [ H : _ = Gt |- _ ] => apply Z.compare_gt_iff in H
         | [ H : context[Z.abs ?N] |- _ ] =>
           generalize (Zabs_spec N); generalize dependent (Z.abs N); intuition
         end.

Ltac implement2 := simpl in *; intuition; try congruence;
  repeat match goal with
         | [ |- context[(?x - ?x)%Z] ] => rewrite <- (Zminus_diag_reverse x); simpl
         | [ H : _ = Lt |- _ ] => apply (proj1 (Z.compare_lt_iff _ _)) in H
         | [ H : _ = Gt |- _ ] => apply Z.compare_gt_iff in H
         | [ H : context[Z.abs ?N] |- _ ] =>
           generalize (Zabs_spec N); generalize dependent (Z.abs N); intuition
         end.

Ltac implement := implement1; try apply refine_pick_val; implement2; Tactics.t_refine; implement2; auto.

Lemma refine_trivial_pick : forall A (x : A),
  refine {y | x = y} (ret x).
Proof.
  implement.
Qed.

Lemma repair : forall A B (x : A * B), (fst x, snd x) = x.
Proof.
  destruct x; auto.
Qed.

Ltac simplify :=
  repeat rewrite refine_if_If;
  repeat (match goal with
          | [ |- context[(fst ?X, snd ?X)] ] => rewrite (repair X)
          | _ => rewrite refine_If_Then_Else_Bind
          | _ => rewrite refineEquiv_bind_unit
          | _ => rewrite refine_trivial_pick
          end; simpl);
  repeat rewrite <- refineEquiv_if_ret;
  unfold If_Then_Else; simpl.

Ltac ilist_of_evar' B As k :=
  match As with
  | [] => k (inil B)
  | ?a :: ?As' =>
    makeEvar (B a)
             ltac:(fun b =>
                     ilist_of_evar' B As'
                                    ltac:(fun Bs' => k (icons a b Bs')))
  end.

Ltac finished' :=
  match goal with
  | [ |- refine (ret ?E) (ret ?F) ] =>
      unify E F
  | [ |- refine (ret ?E) (ret (?F ?X)) ] =>
    let E' := eval pattern X in E in
      match E' with
      | ?F' _ => unify F F'
      end
  | [ |- refine (ret ?E) (ret (?F ?X ?Y)) ] =>
    let E' := eval pattern X, Y in E in
      match E' with
      | ?F' _ _ => unify F F'
      end
  end; reflexivity.

Ltac finished :=
  let delegateSpecs := constr:(inil (fun nadt : NamedDelegatee => ADT (delegateeSig nadt))) in
  match goal with
  | |- Sharpened (@BuildADT ?Rep ?consSigs ?methSigs ?consDefs ?methDefs) =>
    ilist_of_evar' (fun Sig =>
                      cMethodType Rep (BuildADTSig.methDom Sig) (BuildADTSig.methCod Sig))
                   methSigs
                   ltac:(fun cMeths =>
                           ilist_of_evar' (fun Sig => cConstructorType Rep (BuildADTSig.consDom Sig))
                                          consSigs
                                          ltac:(fun cCons =>
                                                  eapply Notation_Friendly_SharpenFully with
                                                  (DelegateIDs' := nil)
                                                    (DelegateSigs' := nil)
                                                    (DelegateReps' := nil)
                                                    (DelegateSpecs' := delegateSpecs)
                                                    (cMethods := fun _ _ => cMeths)
                                                    (cAbsR := fun _ _ _ => eq)
                                                    (cConstructors := fun _ _ => cCons)));
      simpl; intros; repeat match goal with
                            | [ |- unit ] => constructor
                            | [ |- ((forall x, _) * _)%type ] => constructor
                            end; intros; subst; unfold StringBound.ith_Bounded; simpl;
      simplify; finished'
  end.

Lemma StringBound_contra : @StringBound.BoundedString nil -> False.
Proof.
  destruct 1 as [ ? [ [ ] ] ]; simpl in *; discriminate.
Qed.

Ltac extract impl :=
  let Impl := eval simpl in (Sharpened_Implementation (projT1 impl)
                                                      (fun _ => unit)
                                                      (fun idx => match StringBound_contra idx with end)) in
    exact Impl.

Ltac extractConstructor impl name :=
  let new := eval simpl in (CallConstructor impl name) in
  let new := eval unfold cConstructors in new in
  let new := eval simpl in new in
    exact new.

Ltac extractMethod impl name :=
  let new := eval simpl in (CallMethod impl name) in
  let new := eval unfold cMethods in new in
  let new := eval simpl in new in
    exact new.
