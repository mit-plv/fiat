Require Import Bedrock.PropX Bedrock.PropXTac.
Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms.

Section machine.
  Variable pc st : Type.

  Definition PropX_imply cs (l r : PropX pc st) : Prop :=
    interp cs (Imply l r).

  Definition PropX_eq cs (l r : PropX pc st) : Prop :=
    PropX_imply cs l r /\ PropX_imply cs r l.

  Theorem PropX_imply_refl cs : Reflexive (PropX_imply cs).
  Proof.
    unfold Reflexive, PropX_imply. intros.
      eapply Imply_I. econstructor. left; auto.
  Qed.

  Theorem PropX_imply_trans cs : Transitive (PropX_imply cs).
  Proof.
    unfold Transitive, PropX_imply. intros.
      eapply Imply_I. eapply Imply_E.
      eapply valid_weaken. eassumption. compute; intros; auto.
      eapply Imply_E. eapply valid_weaken. eassumption. compute; intros; auto.
      propxFo.
  Qed.

  Theorem PropX_eq_refl cs : Reflexive (PropX_eq cs).
  Proof.
    unfold Reflexive, PropX_eq. generalize (PropX_imply_refl cs). intuition eauto.
  Qed.

  Theorem PropX_eq_sym cs : Symmetric (PropX_eq cs).
  Proof.
    unfold Symmetric, PropX_eq. intuition.
  Qed.

  Theorem PropX_eq_trans cs : Transitive (PropX_eq cs).
  Proof.
    unfold Transitive, PropX_eq. generalize PropX_imply_trans.
      intuition;  eapply H; eauto.
  Qed.

  Add Parametric Relation cs : (@PropX pc st) (@PropX_imply cs)
    reflexivity proved by (PropX_imply_refl cs)
    transitivity proved by (PropX_imply_trans cs)
  as imply_rel.

  Add Parametric Relation cs : (@PropX pc st) (@PropX_eq cs)
    reflexivity proved by (PropX_eq_refl cs)
    symmetry proved by (PropX_eq_sym cs)
    transitivity proved by (PropX_eq_trans cs)
  as eq_rel.

  Global Add Parametric Morphism cs : (interp cs) with
    signature (PropX_imply cs ==> Basics.impl)
  as interp_imply.
    intros. intro. eapply Imply_E; eauto.
  Qed.

  Global Add Parametric Morphism cs : (interp cs) with
    signature (PropX_eq cs ==> iff)
  as interp_eq.
    unfold PropX_eq.
    intros. generalize (interp_imply cs). unfold Basics.impl. intuition;
    eapply H0; eauto.
  Qed.
End machine.

Require Import Coq.Lists.List.

(* I'm sure this is duplication of work *)
Section tactic.
  Variable pcType : Type.
  Variable stateType : Type.

  Variable cs : codeSpec pcType stateType.

  Lemma valid_extend : forall Ps Q R,
    valid cs Ps Q ->
    valid cs (Q :: Ps) R ->
    valid cs Ps R.
  Proof.
    intros.
    eapply Imply_I in H0.
    eapply Imply_E. eassumption.
    eauto.
  Qed.

  Lemma valid_and_split : forall P Ps Q R,
    valid cs ((P /\ Q) :: Ps)%PropX R <->
    valid cs (P :: Q :: Ps)%PropX R.
  Proof.
    split; intros.
    eapply Imply_I in H. eapply Imply_E. eapply valid_weaken. eassumption.
    firstorder.
    eapply And_I; econstructor; firstorder.

    eapply valid_extend. eapply And_E1. econstructor; firstorder.
    eapply valid_extend. eapply And_E2. econstructor; firstorder.
    eapply valid_weaken; eauto. firstorder.
  Qed.

  Lemma valid_perm : forall A B C,
    valid cs (A :: B) C <->
    valid cs (B ++ A :: nil) C.
  Proof.
    split; intros.
    eapply valid_weaken; eauto. intuition.
    eapply valid_weaken; eauto. intuition.
    eapply incl_app; intuition. firstorder.
  Qed.

  Lemma valid_inj :  forall (A : Prop) B C,
    (A -> valid cs B C) ->
    valid cs ([| A |] :: B)%PropX C.
  Proof.
    intros. eapply Inj_E. econstructor; firstorder. intro.
    eapply H in H0.
    eapply valid_weaken; eauto. intuition.
  Qed.

  Lemma valid_ex_clear : forall T (F : T -> PropX pcType stateType) Ps R ,
    (forall x, valid cs (F x :: Ps)%PropX R) ->
    valid cs ((PropX.Exists F) :: Ps)%PropX R.
  Proof.
    intros. eapply Exists_E. econstructor. firstorder.
    intros. eapply valid_weaken. eauto.
    instantiate (1 := B). firstorder.
  Qed.
End tactic.

Ltac propxIntuition :=
  repeat (instantiate; match goal with
                         | [ |- valid _ ((Ex x : _ , _) :: _)%PropX _ ] =>
                           eapply valid_ex_clear; intros
                         | [ |- valid _ ((_ /\ _) :: _)%PropX _ ] =>
                           eapply valid_and_split
                         | [ |- valid _ _ (_ ---> _) ] =>
                           eapply Imply_I
                         | [ |- valid _ ([| _ |] :: _)%PropX _ ] =>
                           eapply valid_inj; intros
                         | [ |- valid _ (_ :: ?X) _ ] =>
                           match X with
                             | context [ (_ /\ _)%PropX ] =>
                               eapply valid_perm; simpl
                             | context [ (Ex x : _ , _)%PropX ] =>
                               eapply valid_perm; simpl
                             | context [ ([| _ |])%PropX ] =>
                               eapply valid_perm; simpl
                           end
                         | [ |- valid _ _ (_ /\ _)%PropX ] =>
                           eapply And_I
                         | [ |- valid _ _ (Ex x : _ , _)%PropX ] =>
                           eapply Exists_I
                         | [ |- valid _ _ (?X _ _) ] =>
                           match X with
                             | @Inj _ _ => fail 1
                             | _ =>
                               solve [ econstructor; firstorder ]
                           end
                         | [ |- valid _ _ ([| _ |])%PropX ] =>
                           eapply Inj_I
                       end).

Section more.
  Variables pc st : Type.

  Global Add Parametric Morphism cs : (@And pc st nil) with
    signature (PropX_eq pc st cs ==> PropX_eq pc st cs ==> PropX_eq pc st cs)
  as And_mor.
    unfold PropX_eq, PropX_imply;
    intuition; unfold interp in *; propxIntuition;
    (eapply Imply_E; [ eapply valid_weaken; eauto; firstorder | econstructor; firstorder ]).
  Qed.
End more.
