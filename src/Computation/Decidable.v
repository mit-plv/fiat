Require Import Coq.Arith.Compare_dec.

Generalizable All Variables.

Class Decidable (P : Prop) := {
  Decidable_witness : bool;
  Decidable_spec : Decidable_witness = true <-> P
}.
Arguments Decidable_witness {P _} /.
Arguments Decidable_spec {P _} /.

Lemma Decidable_sound : forall P (H : Decidable P),
  Decidable_witness = true -> P.
Proof. intros; apply Decidable_spec; trivial. Qed.

Lemma Decidable_complete : forall P (H : Decidable P),
  P -> Decidable_witness = true.
Proof. intros; apply Decidable_spec; trivial. Qed.

Lemma Decidable_sound_alt : forall P (H : Decidable P),
  ~ P -> Decidable_witness = false.
Proof.
  intros.
  destruct Decidable_witness eqn:Heqe; trivial.
  apply Decidable_spec in Heqe.
  contradiction.
Qed.

Lemma Decidable_complete_alt : forall P (H : Decidable P),
  Decidable_witness = false -> ~ P.
Proof.
  intros.
  unfold not; intros.
  apply Decidable_spec in H1.
  congruence.
Qed.

Definition decide P {H : Decidable P} := Decidable_witness (Decidable:=H).

Ltac _decide_ P H :=
  let b := fresh "b" in
  set (b := decide P) in *;
  assert (H : decide P = b) by reflexivity;
  clearbody b;
  destruct b; [apply Decidable_sound in H|apply Decidable_complete_alt in H].

Tactic Notation "decide" constr(P) "as" ident(H) :=
  _decide_ P H.

Tactic Notation "decide" constr(P) :=
  let H := fresh "H" in _decide_ P H.

Hint Extern 2 =>
  match goal with
    [ H : @Decidable ?P |- _ ] =>
    let Heqe := fresh "Heqe" in
    destruct (@Decidable_witness P H) eqn:Heqe
  end : decidability.

Hint Extern 3 =>
  match goal with
    [ W : @Decidable_witness ?P ?H = true |- ?P ] =>
    exact (Decidable_sound P H W)
  end : decidability.

Hint Extern 3 =>
  match goal with
    [ W : @Decidable_witness ?P ?H = false |- ~ ?P ] =>
    exact (Decidable_complete_alt P H W)
  end : decidability.

Lemma Decidable_witness_dec `{Decidable P} : P \/ ~ P.
Proof. decide P; firstorder. Qed.
Arguments Decidable_witness_dec {P _} /.

Lemma Decidable_witness_decides `{Decidable P} :
  if Decidable_witness then P else ~ P.
Proof. auto with decidability. Qed.
Arguments Decidable_witness_decides {P _} /.

Local Ltac t :=
  intros;
  repeat
    match goal with
      [ H : Decidable ?P |- _ ] =>
      let Heqe := fresh "Heqe" in
      destruct (@Decidable_witness P H) eqn:Heqe;
      [ apply (@Decidable_sound P H) in Heqe
      | apply (@Decidable_complete_alt P H) in Heqe ];
      clear H
    end;
  simpl; split; intros;
  try discriminate;
  try contradiction;
  try reflexivity;
  intuition.

Section DecidableLogic.

Local Obligation Tactic := t.

Global Program Instance not_Decidable {P : Prop} `{Decidable P} :
  Decidable (~ P) := {
  Decidable_witness := negb Decidable_witness
}.

Global Program Instance and_Decidable {P Q : Prop}
  `{Decidable P} `{Decidable Q} : Decidable (P /\ Q) := {
  Decidable_witness := andb (Decidable_witness (P:=P))
                            (Decidable_witness (P:=Q))
}.

Global Program Instance or_Decidable {P Q : Prop}
  `{Decidable P} `{Decidable Q} : Decidable (P \/ Q) := {
  Decidable_witness := orb (Decidable_witness (P:=P))
                           (Decidable_witness (P:=Q))
}.

Global Program Instance impl_Decidable {P Q : Prop}
  `{Decidable P} `{Decidable Q} : Decidable (P -> Q) := {
  Decidable_witness := if Decidable_witness (P:=P)
                       then Decidable_witness (P:=Q)
                       else true
}.

End DecidableLogic.

Local Ltac t' tac := t; apply tac; assumption.

Require Import Coq.Bool.Bool.

Global Program Instance bool_eq_Decidable {n m : bool} : Decidable (n = m) := {
  Decidable_witness := eqb n m
}.
Obligation 1. t' eqb_true_iff. Qed.

Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Sumbool.

Global Program Instance ascii_eq_Decidable {n m : Ascii.ascii} :
  Decidable (n = m) := {
  Decidable_witness := bool_of_sumbool (Ascii.ascii_dec n m)
}.
Obligation 1. t; destruct (Ascii.ascii_dec n m); auto; discriminate. Qed.

Require Import Coq.Arith.Arith.

Global Program Instance nat_eq_Decidable {n m : nat} : Decidable (n = m) := {
  Decidable_witness := beq_nat n m
}.
Obligation 1. t' beq_nat_true_iff. Qed.

Global Program Instance le_Decidable {n m} : Decidable (le n m) := {
  Decidable_witness := Compare_dec.leb n m
}.
Obligation 1. t' leb_iff. Qed.

Global Instance lt_Decidable {n m} : Decidable (lt n m) := le_Decidable.

Require Import Coq.NArith.NArith.

Global Program Instance N_eq_Decidable {n m : N} : Decidable (n = m) := {
  Decidable_witness := N.eqb n m
}.
Obligation 1. t' N.eqb_eq. Qed.

Global Program Instance Nle_Decidable {n m} : Decidable (Nle n m) := {
  Decidable_witness := N.leb n m
}.
Obligation 1. t' N.leb_le. Qed.

Global Program Instance Nlt_Decidable {n m} : Decidable (Nlt n m) := {
  Decidable_witness := N.ltb n m
}.
Obligation 1. t' N.ltb_lt. Qed.

Require Import Coq.ZArith.ZArith.

Global Program Instance Z_eq_Decidable {n m : Z} : Decidable (n = m) := {
  Decidable_witness := Z.eqb n m
}.
Obligation 1. t' Z.eqb_eq. Qed.

Global Program Instance Zle_Decidable {n m} : Decidable (Zle n m) := {
  Decidable_witness := Z.leb n m
}.
Obligation 1. t' Z.leb_le. Qed.

Global Program Instance Zlt_Decidable {n m} : Decidable (Zlt n m) := {
  Decidable_witness := Z.ltb n m
}.
Obligation 1. t' Z.ltb_lt. Qed.

Require Import Coq.QArith.QArith.

Global Program Instance Q_eq_Decidable {n m : Q} : Decidable (n == m) := {
  Decidable_witness := Qeq_bool n m
}.
Obligation 1. t' Qeq_bool_iff. Qed.

Global Program Instance Qle_Decidable {n m} : Decidable (Qle n m) := {
  Decidable_witness := Qle_bool n m
}.
Obligation 1. t' Qle_bool_iff. Qed.

Global Program Instance Qlt_Decidable {n m} : Decidable (Qlt n m) := {
  Decidable_witness := bool_of_sumbool (Qlt_le_dec n m)
}.
Obligation 1.
  t; destruct (Qlt_le_dec n m); simpl in H; auto.
    discriminate.
  apply Qle_not_lt in H; auto.
Qed.

Section ListDec.
  Variable A : Type.
  Variable eq_dec : forall x y : A, {x = y} + {x <> y}.

  Global Program Instance list_eq_Decidable {xs ys : list A} :
    Decidable (xs = ys) := {
    Decidable_witness := bool_of_sumbool (List.list_eq_dec eq_dec xs ys)
  }.
  Obligation 1.
    t; destruct (List.list_eq_dec eq_dec xs ys);
    simpl in H; auto; discriminate.
  Qed.

  Global Program Instance list_in_Decidable {xs : list A} {x : A} :
    Decidable (List.In x xs) := {
    Decidable_witness := List.existsb (fun y => bool_of_sumbool (eq_dec x y)) xs
  }.
  Obligation 1.
    remember (fun _ => proj1_sig _) as F; t;
    destruct (List.existsb_exists F xs);
    destruct (List.existsb F xs);
    auto; try discriminate.
      destruct (H0 H).
      destruct H2.
      rewrite HeqF in H3.
      destruct (eq_dec x x0);
      subst; auto; discriminate.
    apply H1.
    exists x; split; auto.
    rewrite HeqF.
    destruct (eq_dec x x); auto.
  Qed.
End ListDec.

Definition IfDec_Then_Else {A} (P : Prop) `{Decidable P} (t e : A) :=
  if Decidable_witness then t else e.
Arguments IfDec_Then_Else {A} P {_} t e : simpl never.

Notation "'IfDec' P 'Then' t 'Else' e" :=
  (IfDec_Then_Else P t e) (at level 70) : comp_scope.

Require Import Fiat.Common.
Require Import Fiat.Computation.Core.

Local Ltac t2 p := intros; destruct p; intuition.

Lemma refine_IfDec_true : forall `{Decidable P} ResultT (t e : Comp ResultT),
  P -> refine (IfDec P Then t Else e) t.
Proof.
  intros.
  apply Decidable_spec in H0.
  unfold IfDec_Then_Else.
  rewrite H0; simpl.
  apply refine_PreOrder.
Qed.

Lemma refine_IfDec_false : forall `{Decidable P} ResultT (t e : Comp ResultT),
  ~ P -> refine (IfDec P Then t Else e) e.
Proof.
  intros.
  eapply Decidable_sound_alt in H0.
  unfold IfDec_Then_Else.
  rewrite H0; simpl.
  apply refine_PreOrder.
Qed.

Require Import Fiat.Computation.Monad.
Require Import Fiat.Computation.Refinements.General.

Lemma refine_IfDec_decides :
  forall `{Decidable P} ResultT (t e : Comp ResultT),
    refineEquiv (IfDec P Then t Else e)
                (b <- {b : bool | decides b P};
                 If b Then t Else e).
Proof.
  split.
    apply refine_pick_decides.
      exact (refine_IfDec_true _ _).
    exact (refine_IfDec_false _ _).
  refine pick val Decidable_witness.
    rewrite refine_bind_unit.
    apply refine_PreOrder.
  exact Decidable_witness_decides.
Qed.

Lemma refine_IfDec_Then_Else :
  forall (A : Type) `{Decidable P} (x y : Comp A),
    refine x y
      -> forall x0 y0 : Comp A, refine x0 y0
      -> refine (IfDec P Then x Else x0)
                (IfDec P Then y Else y0).
Proof.
  intros.
  unfold IfDec_Then_Else.
  rewrite refine_if_If.
  rewrite H0, H1.
  apply refine_PreOrder.
Qed.

Lemma refine_IfDec_Then_Else_ret :
  forall `{Decidable P} ResultT (t e : ResultT),
    refine (IfDec P Then ret t Else ret e)
           (ret (IfDec P Then t Else e)%comp).
Proof.
  intros.
  unfold IfDec_Then_Else.
  apply refine_If_Then_Else_ret; trivial.
Qed.

Lemma refine_sumbool_match :
  forall `(P : {A} + {~A}) B
         (f f' : A -> Comp B) (g g' : ~A -> Comp B),
       pointwise_relation A    refine f f'
    -> pointwise_relation (~A) refine g g'
    -> refine (match P with
               | left  H => f H
               | right H => g H
               end)
              (match P with
               | left  H => f' H
               | right H => g' H
               end).
Proof. t2 P. Qed.

Lemma refine_sumbool_ret :
  forall `(P : {A} + {~A}) `(f : A -> B) (g : ~A -> B),
    refine (match P with
            | left  H => ret (f H)
            | right H => ret (g H)
            end)
           (ret (match P with
                 | left  H => f H
                 | right H => g H
                 end)).
Proof. t2 P. Qed.

Lemma refine_sumbool_bind :
  forall `(P : {A} + {~A})
         `(f : A -> Comp B) (g : ~A -> Comp B)
         `(h : B -> Comp C),
    refine (x <- match P with
                 | left  H => f H
                 | right H => g H
                 end;
            h x)
           (match P with
            | left  H => x <- f H; h x
            | right H => x <- g H; h x
            end).
Proof. t2 P. Qed.

Lemma refine_bind_sumbool :
  forall `(P : {A} + {~A})
         `(f : C -> A -> Comp B) (g : C -> ~A -> Comp B)
         `(c : Comp C),
    refine (x <- c;
            match P with
            | left  H => f x H
            | right H => g x H
            end)
           (match P with
            | left  H => x <- c; f x H
            | right H => x <- c; g x H
            end).
Proof. t2 P. Qed.
