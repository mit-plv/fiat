Require Export Bedrock.Platform.Cito.StringMap Bedrock.Platform.Cito.StringMapFacts.
Require Export Bedrock.Platform.Cito.SyntaxExpr Bedrock.Platform.Facade.DFacade.
Require Import Bedrock.Platform.Facade.DFacadeFacts2.
Require Import Coq.Setoids.Setoid.

Add Parametric Morphism {av} : (@eval av)
    with signature (StringMap.Equal ==> eq ==> eq)
      as eval_Morphism.
Proof.
  eauto using DFacadeFacts2.eval_Morphism.
Qed.

Lemma IL_weqb_refl : forall x,
    IL.weqb x x = true.
Proof.
  unfold IL.weqb.
  intros; rewrite Word.weqb_true_iff; reflexivity.
Qed.

Lemma IL_weqb_sound : forall x y,
    IL.weqb x y = true -> x = y.
Proof.
  eauto using Word.weqb_sound.
Qed.

Add Parametric Morphism {av} {env} {prog} : (@Safe av env prog)
    with signature (StringMap.Equal ==> iff)
      as Safe_Morphism.
Proof.
  eauto using DFacadeFacts2.Safe_Morphism.
Qed.

Add Parametric Morphism {av} {env} {prog} : (@RunsTo av env prog)
    with signature (StringMap.Equal ==> StringMap.Equal ==> iff)
      as RunsTo_Morphism.
Proof.
  eauto using DFacadeFacts2.RunsTo_Morphism.
Qed.

Require Import GLabelMap GLabelMapFacts.
Require Import Program.Basics.

Add Parametric Morphism av
  : (@RunsTo av)
    with signature
    (GLabelMap.Equal ==> eq ==> StringMap.Equal ==> StringMap.Equal ==> impl)
      as Proper_RunsTo.
Proof.
  unfold impl; intros.
  revert y y1 y2 H0 H1 H.
  induction H2; intros.
  - econstructor; rewrite <- H0, <- H1; eauto.
  - econstructor 2; eauto.
    eapply IHRunsTo1; eauto.
    reflexivity.
    eapply IHRunsTo2; eauto.
    reflexivity.
  - econstructor 3; eauto.
    unfold is_true, eval_bool.
    setoid_rewrite <- H0; apply H.
  - econstructor 4; eauto.
    unfold is_false, eval_bool.
    setoid_rewrite <- H0; apply H.
  - econstructor 5; eauto.
    unfold is_true, eval_bool.
    setoid_rewrite <- H0; apply H.
    eapply IHRunsTo1; eauto.
    reflexivity.
    eapply IHRunsTo2; eauto.
    reflexivity.
  - econstructor 6; eauto.
    unfold is_false, eval_bool.
    setoid_rewrite <- H1; apply H.
    rewrite <- H1, <- H2; eauto.
  - econstructor 7;
    rewrite <- H2; eauto.
    rewrite <- H1; symmetry; eauto.
  - econstructor 8; eauto.
    rewrite <- H8; eauto.
    rewrite <- H6; eauto.
    rewrite <- H6; eauto.
    rewrite <- H7.
    subst st'; subst st'0; rewrite <- H6; eauto.
  - econstructor 9; eauto.
    rewrite <- H9; eauto.
    rewrite <- H7; eauto.
    rewrite <- H7; eauto.
    eapply IHRunsTo; eauto.
    reflexivity.
    reflexivity.
    subst st'; subst st'0; subst output; rewrite <- H8.
    rewrite <- H7; eauto.
Qed.

Add Parametric Morphism av
  : (@Safe av)
    with signature
    (GLabelMap.Equal ==> eq ==> StringMap.Equal ==> impl)
      as Proper_Safe.
Proof.
  unfold impl; intros.
  rewrite <- H0.
  apply Safe_coind with (R := fun st ext => Safe x st ext); eauto.
  - intros; inversion H2; subst; intuition.
    eapply H4.
    setoid_rewrite H; eauto.
  - intros; inversion H2; subst; intuition.
  - intros; inversion H2; try subst; intuition.
    left; intuition eauto.
    subst loop; subst loop1; subst loop2.
    rewrite <- H4.
    eapply H8.
    rewrite H; eauto.
  - intros; inversion H2; try subst; intuition.
    eauto.
  - intros; inversion H2; try subst; intuition.
    + eexists; intuition eauto.
      left; eexists; intuition eauto.
      rewrite <- H; eauto.
    + eexists; intuition eauto.
      right; eexists; intuition eauto.
      rewrite <- H; eauto.
      eapply H12; eauto.
      rewrite H; eauto.
      eapply H12.
      rewrite H; eauto.
Qed.

Add Parametric Morphism elt
  : (@GLabelMapFacts.UWFacts.WFacts.P.update elt)
    with signature
    (GLabelMap.Equal ==> GLabelMap.Equal ==> GLabelMap.Equal)
      as GLabelMapFacts_UWFacts_WFacts_P_update_morphism.
Proof.
  apply GLabelMapFacts.UWFacts.WFacts.P.update_m.
Qed.

Ltac isDeterministicStmtConstructor stmt :=
  match stmt with
  | Skip => idtac
  | Seq _ _ => idtac
  | Assign _ _ => idtac
  | _ => fail 1 "This statement has multiple RunsTo and Safe constructors"
  end.

Ltac isSafelyInvertibleStmtConstructor stmt :=
  match stmt with
  | Skip => idtac
  | Seq _ _ => idtac
  | If _ _ _ => idtac
  | Call _ _ _ => idtac
  | Assign _ _ => idtac
  | _ => fail 1 "Not a safely invertible constructor"
  end.
