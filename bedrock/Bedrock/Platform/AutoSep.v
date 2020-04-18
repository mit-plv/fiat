Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.PreAutoSep Bedrock.Platform.Util Bedrock.Platform.Sys.
Export PreAutoSep Util Sys.

Set Implicit Arguments.


Ltac enterFunction :=
  match goal with
    | [ |- context[localsInvariant _ _ false _ ?ns _ _] ] =>
      match goal with
        | [ |- context[localsInvariant _ _ true _ ?ns'' _ _] ] =>
          let ns' := peelPrefix ns ns'' in
            intros;
              repeat match goal with
                       | [ H : interp _ _ |- _ ] =>
                         eapply localsInvariant_inEx; [ | apply H ];
                           clear H; simpl; intros
                     end;
              eapply (@localsInvariant_in ns'); [
                eassumption
                | simpl; omega
                | reflexivity
                | reflexivity
                | repeat constructor; simpl; intuition congruence
                | intros ? ? Hrew; repeat rewrite Hrew by (simpl; tauto); reflexivity
                | intros ? ? Hrew; repeat rewrite Hrew by (simpl; tauto); reflexivity ]
      end
  end.

Ltac sep hints := enterFunction || PreAutoSep.sep hints.

Ltac sep_auto := sep auto_ext.


(** * Help with higher-order VCs *)

Lemma tuple_predicate : forall A B pc state
  (P : A -> B -> PropX pc state) P' specs x y,
  interp specs (P x y)
  -> P' = (fun p => P (fst p) (snd p))
  -> interp specs (P' (x, y)).
  intros; subst; auto.
Qed.

Hint Extern 1 (interp _ _) =>
  eapply tuple_predicate; [ eassumption | reflexivity ].

(* avoid name conflict with Conditional.v *)
Definition And := PropX.And.
Definition Or := PropX.Or.

Fixpoint eatEasy pc state G (P : propX pc state G)
  : list (propX pc state G) * list (propX pc state G) :=
  match P in propX _ _ G return list (propX _ _ G) * list (propX _ _ G) with
    | Inj _ p => (Inj p :: nil, nil)
    | Cptr _ pc f => (Cptr pc f :: nil, nil)
    | And _ Q R => let (easy1, hard1) := eatEasy Q in
      let (easy2, hard2) := eatEasy R in
        (easy1 ++ easy2, hard1 ++ hard2)
    | Or _ Q R => (nil, Or Q R :: nil)
    | Imply _ Q R => (nil, Imply Q R :: nil)
    | Forall _ _ Q => (nil, Forall Q :: nil)
    | Exists _ _ Q => (nil, Exists Q :: nil)
    | Var0 _ _ v => (nil, Var0 v :: nil)
    | Lift _ _ Q => (nil, Lift Q :: nil)
    | ForallX _ _ Q => (nil, ForallX Q :: nil)
    | ExistsX _ _ Q => (nil, ExistsX Q :: nil)
  end.

Definition andify' pc state G (Ps : list (propX pc state G)) :=
  fold_left (@And _ _ _) Ps.

Definition andify pc state G (Ps : list (propX pc state G)) :=
  andify' Ps (Inj True).

Lemma eatEasy_right1 : forall pc state (P : PropX pc state) specs,
  interp specs ([|True|] /\ P ---> [|True|] ---> P)%PropX.
  intros.
  repeat apply Imply_I.
  eapply And_E2; apply Env; simpl; eauto.
Qed.

Lemma eatEasy_right2 : forall pc state (P : PropX pc state) specs,
  interp specs (andify nil ---> andify (P :: nil) ---> P)%PropX.
  unfold andify, andify'; simpl; intros.
  do 2 apply Imply_I.
  eapply And_E2; apply Env; simpl; eauto.
Qed.

Lemma andify1'' : forall pc state (Ps : list (PropX pc state)) R' R specs,
  interp specs (R' ---> R)
  -> interp specs (andify' Ps R' ---> R).
  unfold andify'; induction Ps; simpl; intuition.
  apply IHPs.
  apply Imply_I; eapply Imply_E; [ apply interp_weaken; apply H | ].
  eapply And_E1; apply Env; simpl; eauto.
Qed.

Lemma andify1' : forall pc state (Qs Ps : list (PropX pc state)) R specs,
  interp specs (andify' (Ps ++ Qs) R ---> andify' Ps R).
  unfold andify'; induction Ps; simpl; intuition.
  apply andify1''; apply Imply_refl.
Qed.

Lemma andify1 : forall pc state (Qs Ps : list (PropX pc state)) specs,
  interp specs (andify (Ps ++ Qs) ---> andify Ps).
  intros; apply andify1'.
Qed.

Lemma andify2''' : forall pc state (Ps : list (PropX pc state)) R' R specs,
  interp specs ((R' ---> R) ---> andify' Ps R' ---> andify' Ps R)%PropX.
  unfold andify'; induction Ps; simpl; intuition.
  apply Imply_refl.
  apply Imply_I.
  eapply Imply_E.
  apply interp_weaken; apply IHPs.
  apply Imply_I; apply And_I.
  eapply Imply_E.
  apply Env; simpl; eauto.
  eapply And_E1; apply Env; simpl; eauto.
  eapply And_E2; apply Env; simpl; eauto.
Qed.

Lemma andify2'' : forall pc state (Ps : list (PropX pc state)) R' R specs,
  interp specs (R' ---> R)
  -> interp specs (andify' Ps R' ---> andify' Ps R).
  intros; eapply Imply_E.
  apply andify2'''.
  auto.
Qed.

Lemma andify2' : forall pc state (Qs Ps : list (PropX pc state)) R specs,
  interp specs (andify' (Ps ++ Qs) R ---> andify' Qs R).
  unfold andify'; induction Ps; simpl; intuition.
  apply Imply_refl.
  eapply Imply_trans; try apply IHPs.
  apply andify2''.
  eapply Imply_I; eapply And_E1; apply Env; simpl; eauto.
Qed.

Lemma andify2 : forall pc state (Qs Ps : list (PropX pc state)) specs,
  interp specs (andify (Ps ++ Qs) ---> andify Qs).
  intros; apply andify2'.
Qed.

Lemma eatEasy_right' : forall pc state G (P : propX pc state G),
  match G return propX pc state G -> Prop with
    | nil => fun P => forall specs,
      let (easy, hard) := eatEasy P in
        interp specs (andify easy ---> andify hard ---> P)%PropX
    | _ => fun _ => True
  end P.
  induction P; destruct G; simpl; intuition;
    try (apply eatEasy_right1 || apply eatEasy_right2; eauto).

  intros.
  destruct (eatEasy P1).
  destruct (eatEasy P2).
  repeat apply Imply_I.
  apply And_I.
  eapply Imply_E; [ eapply Imply_E | ].
  apply interp_weaken; apply IHP1.
  eapply Imply_E; [ apply interp_weaken; apply andify1 | ].
  eapply Env; simpl; eauto.
  eapply Imply_E; [ apply interp_weaken; apply andify1 | ].
  eapply Env; simpl; eauto.
  eapply Imply_E.
  eapply Imply_E.
  apply interp_weaken; apply IHP2.
  eapply Imply_E; [ apply interp_weaken; apply andify2 | ].
  apply Env; simpl; eauto.
  eapply Imply_E; [ apply interp_weaken; apply andify2 | ].
  apply Env; simpl; eauto.
Qed.

Lemma eatEasy_left1 : forall pc state (P : PropX pc state) specs,
  interp specs (P ---> andify (P :: nil))%PropX.
  unfold andify, andify'; simpl; intros.
  apply Imply_I.
  apply And_I.
  apply Inj_I; auto.
  apply Env; simpl; eauto.
Qed.

Lemma eatEasy_left2 : forall pc state (P : PropX pc state) specs,
  interp specs (P ---> andify nil).
  intros; apply Imply_I; apply Inj_I; auto.
Qed.

Lemma andify_app' : forall pc state (Qs Ps : list (PropX pc state)) R specs,
  interp specs (andify' Ps R ---> andify Qs ---> andify' (Ps ++ Qs) R)%PropX.
  unfold andify, andify'; induction Ps; simpl; intuition.
  apply Imply_I.
  eapply Imply_E.
  apply interp_weaken; apply andify2'''.
  apply Imply_I; apply Env; simpl; eauto.
Qed.

Lemma andify_app : forall pc state (Qs Ps : list (PropX pc state)) specs,
  interp specs (andify Ps ---> andify Qs ---> andify (Ps ++ Qs))%PropX.
  unfold andify, andify'; induction Ps; simpl; intuition.
  apply Imply_I; apply interp_weaken; apply Imply_refl.
  apply andify_app'.
Qed.

Lemma eatEasy_left1' : forall pc state G (P : propX pc state G),
  match G return propX pc state G -> Prop with
    | nil => fun P => forall specs,
      let (easy, hard) := eatEasy P in
        interp specs (P ---> andify easy)%PropX
    | _ => fun _ => True
  end P.
  induction P; destruct G; simpl; intuition;
    try (apply eatEasy_left1 || apply eatEasy_left2).

  destruct (eatEasy P1); destruct (eatEasy P2).
  apply andL; do 2 apply Imply_I.
  eapply Imply_E.
  eapply Imply_E.
  apply interp_weaken; apply andify_app.
  eapply Imply_E.
  apply interp_weaken; apply IHP1; apply Env; simpl; auto.
  apply Env; simpl; auto.
  eapply Imply_E.
  apply interp_weaken; apply IHP2; apply Env; simpl; auto.
  apply Env; simpl; auto.
Qed.

Lemma eatEasy_left2' : forall pc state G (P : propX pc state G),
  match G return propX pc state G -> Prop with
    | nil => fun P => forall specs,
      let (easy, hard) := eatEasy P in
        interp specs (P ---> andify hard)%PropX
    | _ => fun _ => True
  end P.
  induction P; destruct G; simpl; intuition;
    try (apply eatEasy_left1 || apply eatEasy_left2).

  destruct (eatEasy P1); destruct (eatEasy P2).
  apply andL; do 2 apply Imply_I.
  eapply Imply_E.
  eapply Imply_E.
  apply interp_weaken; apply andify_app.
  eapply Imply_E.
  apply interp_weaken; apply IHP1; apply Env; simpl; auto.
  apply Env; simpl; auto.
  eapply Imply_E.
  apply interp_weaken; apply IHP2; apply Env; simpl; auto.
  apply Env; simpl; auto.
Qed.

Theorem eatEasy_simpl : forall pc state (P Q : PropX pc state) specs,
  (let (easy1, hard1) := eatEasy P in
    let (easy2, hard2) := eatEasy Q in
    interp specs (andify easy1 ---> andify hard1 ---> andify easy2 /\ andify hard2)%PropX)
  -> interp specs (P ---> Q)%PropX.
  intros.
  specialize (eatEasy_left1' P); specialize (eatEasy_left2' P); destruct (eatEasy P); intros.
  specialize (eatEasy_right' Q); destruct (eatEasy Q); intros.
  apply Imply_trans with (andify l0 /\ andify l)%PropX.
  apply andR; auto.
  eapply Imply_trans; try apply H2.
  apply andL; apply swap; eauto.
  apply andL; auto.
Qed.

Ltac big_imp := ((eapply Imply_sound; [ match goal with
                                          | [ H : _ |- _ ] => apply H
                                        end | ])
|| (eapply Imply_trans; [ | match goal with
                              | [ H : _ |- _ ] => apply H
                            end ])); cbv beta; simpl.

Ltac cptr := post; rewrite sepFormula_eq;
  repeat match goal with
           | [ H : interp _ (![_] _) |- _ ] => rewrite sepFormula_eq in H
         end; propxFo; descend; eauto;
  try big_imp.

Lemma jiggle : forall pc state (P Q R S : PropX pc state) specs,
  interp specs (P ---> (Q /\ S) /\ R)%PropX
  -> interp specs (P ---> (Q /\ R) /\ S)%PropX.
  intros.
  eapply Imply_trans; try apply H.
  intros; apply Imply_I.
  repeat apply And_I.
  eapply And_E1; eapply And_E1; apply Env; simpl; eauto.
  eapply And_E2; apply Env; simpl; eauto.
  eapply And_E2; eapply And_E1; apply Env; simpl; eauto.
Qed.

Ltac refl := try rewrite sepFormula_eq;
  apply Imply_refl || (apply jiggle; apply Imply_refl).

Ltac imp := rewrite sepFormula_eq; apply eatEasy_simpl;
  unfold andify, andify'; simpl;
    repeat (apply andL; apply swap; ((apply injL || apply cptrL); intro));
      apply injL; intro; apply andR; [
        apply Imply_I; apply interp_weaken
        | try refl ].

Lemma curry_predicate : forall A B pc state
  (P : A * B -> PropX pc state) P' specs x y,
  interp specs (P (x, y))
  -> P' = (fun x y => P (x, y))
  -> interp specs (P' x y).
  intros; subst; auto.
Qed.

Hint Extern 1 (simplify _ _ _) =>
  apply simplify_fwd; eapply curry_predicate; [ eassumption | reflexivity ].

Lemma substH_in2 : forall a b (P : hpropB (a :: b :: nil)) q1 q2,
  (fun stn sm => subst (G := a :: nil) (subst (P stn sm) q1) q2) = substH (substH P q1) q2.
reflexivity.
Qed.

Hint Rewrite substH_in2 : sepFormula.
Opaque mult.
Require Import Coq.Arith.Arith.

Lemma create_stack : forall ns ss sp,
  NoDup ns
  -> sp =?> (length ns + ss) ===> Ex vs, locals ns vs ss sp.
  intros; eapply Himp_trans; [ apply allocated_split | ].
  instantiate (1 := length ns); omega.
  eapply Himp_trans.
  eapply Himp_star_frame.
  apply behold_the_array; auto.
  apply Himp_refl.
  unfold locals, array.
  Opaque mult.
  sepLemma.
  apply allocated_shift_base.
  unfold natToW; rewrite mult_comm; words.
  omega.
Qed.

Transparent mult.

Notation Abort := (Goto "sys"!"abort")%SP.
