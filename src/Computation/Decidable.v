Require Import
  Fiat.ADT
  Coq.Arith.Compare_dec
  Coq.ZArith.ZArith
  Coq.QArith.QArith
  Coq.QArith.Qabs.

Generalizable All Variables.

Class Decidable (P : Prop) := {
  decision : bool;
  decision_correct : BoolSpec P (~P) decision
}.
Arguments decision P {_} /.
Arguments decision_correct P {_} /.

Lemma decision_dec `{Decidable P} : P \/ ~ P.
  destruct (decision_correct P); auto.
Qed.
Arguments decision_dec P {_} /.

Lemma decision_decides `{Decidable P} : if decision P then P else ~ P.
  destruct (decision_correct P); trivial.
Qed.
Arguments decision_decides P {_} /.

Local Ltac t :=
  repeat
    match goal with
      [ H : Decidable ?P |- _ ] =>
      destruct H;
      repeat
        match goal with
          [ decision_correct0 : BoolSpec ?P ?Q ?B |- _ ] =>
          destruct decision_correct0
        end
    end;
  simpl in *;
  try constructor;
  intuition.

Global Program Instance not_Decidable {P : Prop} `{Decidable P} :
  Decidable (~ P) := {
  decision := negb (decision P)
}.
Obligation 1. t. Qed.

Global Program Instance and_Decidable {P Q : Prop}
  `{Decidable P} `{Decidable Q} : Decidable (P /\ Q) := {
  decision := andb (decision P) (decision Q)
}.
Obligation 1. t. Qed.

Global Program Instance or_Decidable {P Q : Prop}
  `{Decidable P} `{Decidable Q} : Decidable (P \/ Q) := {
  decision := orb (decision P) (decision Q)
}.
Obligation 1. t. Qed.

Global Program Instance impl_Decidable {P Q : Prop}
  `{Decidable P} `{Decidable Q} : Decidable (P -> Q) := {
  decision := if decision P then decision Q else true
}.
Obligation 1. t. Qed.

Global Program Instance bool_eq_Decidable {n m : bool} : Decidable (n = m) := {
  decision := eqb n m
}.
Obligation 1.
  destruct (eqb n m) eqn:Heqe;
  constructor.
    apply eqb_true_iff; assumption.
  apply eqb_false_iff; assumption.
Qed.

Global Program Instance ascii_eq_Decidable {n m : Ascii.ascii} :
  Decidable (n = m) := {
  decision := bool_of_sumbool (Ascii.ascii_dec n m)
}.
Obligation 1.
  destruct (Ascii.ascii_dec n m); constructor; assumption.
Qed.

Global Program Instance nat_eq_Decidable {n m : nat} : Decidable (n = m) := {
  decision := beq_nat n m
}.
Obligation 1.
  destruct (beq_nat n m) eqn:Heqe;
  constructor.
    apply beq_nat_true_iff; assumption.
  apply beq_nat_false_iff; assumption.
Qed.

Global Program Instance le_Decidable {n m} : Decidable (le n m) := {
  decision := Compare_dec.leb n m
}.
Obligation 1.
  destruct (Compare_dec.leb n m) eqn:Heqe;
  constructor.
    apply leb_iff; assumption.
  apply gt_not_le.
  apply leb_iff_conv; assumption.
Qed.

Global Instance lt_Decidable {n m} : Decidable (lt n m) := le_Decidable.

Global Program Instance N_eq_Decidable {n m : N} : Decidable (n = m) := {
  decision := N.eqb n m
}.
Obligation 1.
  destruct (N.eqb n m) eqn:Heqe.
    apply N.eqb_eq in Heqe.
    constructor; assumption.
  apply N.eqb_neq in Heqe.
  constructor; assumption.
Qed.

Global Program Instance Nle_Decidable {n m} : Decidable (Nle n m) := {
  decision := N.leb n m
}.
Obligation 1.
  destruct (N.leb n m) eqn:Heqe.
    apply N.leb_le in Heqe.
    constructor; assumption.
  apply N.leb_nle in Heqe.
  constructor; assumption.
Qed.

Global Program Instance Nlt_Decidable {n m} : Decidable (Nlt n m) := {
  decision := N.ltb n m
}.
Obligation 1.
  destruct (N.ltb n m) eqn:Heqe.
    apply N.ltb_lt in Heqe.
    constructor; assumption.
  apply N.ltb_nlt in Heqe.
  constructor; assumption.
Qed.

Global Program Instance Z_eq_Decidable {n m : Z} : Decidable (n = m) := {
  decision := Z.eqb n m
}.
Obligation 1.
  destruct (Z.eqb n m) eqn:Heqe.
    apply Z.eqb_eq in Heqe.
    constructor; assumption.
  apply Z.eqb_neq in Heqe.
  constructor; assumption.
Qed.

Global Program Instance Zle_Decidable {n m} : Decidable (Zle n m) := {
  decision := Z.leb n m
}.
Obligation 1.
  destruct (Z.leb n m) eqn:Heqe.
    apply Z.leb_le in Heqe.
    constructor; assumption.
  apply Z.leb_nle in Heqe.
  constructor; assumption.
Qed.

Global Program Instance Zlt_Decidable {n m} : Decidable (Zlt n m) := {
  decision := Z.ltb n m
}.
Obligation 1.
  destruct (Z.ltb n m) eqn:Heqe.
    apply Z.ltb_lt in Heqe.
    constructor; assumption.
  apply Z.ltb_nlt in Heqe.
  constructor; assumption.
Qed.

Global Program Instance Q_eq_Decidable {n m : Q} : Decidable (n == m) := {
  decision := Qeq_bool n m
}.
Obligation 1.
  destruct (Qeq_bool n m) eqn:Heqe.
    apply Qeq_bool_eq in Heqe.
    constructor; assumption.
  apply Qeq_bool_neq in Heqe.
  constructor; assumption.
Qed.

Global Program Instance Qle_Decidable {n m} : Decidable (Qle n m) := {
  decision := Qle_bool n m
}.
Obligation 1.
  destruct (Qle_bool n m) eqn:Heqe.
    apply Qle_bool_iff in Heqe.
    constructor; assumption.
  constructor.
  apply Z.leb_nle in Heqe.
  assumption.
Qed.

Global Program Instance Qlt_Decidable {n m} : Decidable (Qlt n m) := {
  decision := bool_of_sumbool (Qlt_le_dec n m)
}.
Obligation 1.
  destruct (Qlt_le_dec n m).
    constructor; assumption.
  constructor.
  apply Qle_not_lt.
  assumption.
Qed.

Section ListDec.
  Variable A : Type.
  Variable eq_dec : forall x y : A, {x = y} + {x <> y}.

  Global Program Instance list_eq_Decidable {xs ys : list A} :
    Decidable (xs = ys) := {
    decision := bool_of_sumbool (List.list_eq_dec eq_dec xs ys)
  }.
  Obligation 1.
    destruct (List.list_eq_dec eq_dec xs ys); auto.
  Qed.

  Global Program Instance list_in_Decidable {xs : list A} {x : A} :
    Decidable (List.In x xs) := {
    decision := List.existsb (eq_dec x) xs
  }.
  Obligation 1.
    destruct (List.existsb_exists (eq_dec x) xs).
    destruct (List.existsb (fun y : A => eq_dec x y) xs);
    intuition;
    constructor.
      destruct H1.
      destruct H0.
      destruct (eq_dec x x0); subst; auto.
      discriminate.
    intros.
    assert (exists x0 : A, (List.In x0 xs) /\
                           (bool_of_sumbool (eq_dec x x0) = true)).
      exists x; split.
        assumption.
      destruct (eq_dec x x); auto.
    apply H0 in H2.
    discriminate.
  Qed.
End ListDec.

Definition IfDec_Then_Else {A} (P : Prop) `{Decidable P} (t e : A) :=
  If decision P Then t Else e.
Arguments IfDec_Then_Else {A} P {_} t e : simpl never.

Notation "'IfDec' P 'Then' t 'Else' e" :=
  (IfDec_Then_Else P t e) (at level 70) : comp_scope.

Local Ltac t' p := intros; destruct p; intuition.

Corollary refine_IfDec_decides :
  forall `{Decidable P} ResultT (t e : Comp ResultT),
    refineEquiv (IfDec P Then t Else e)
                (b <- {b : bool | decides b P};
                 If b Then t Else e).
Proof.
  intros.
  unfold IfDec_Then_Else, decides, If_Then_Else.
  split.
    apply refine_pick_decides; intros.
      destruct (decision_correct P); simpl.
        reflexivity.
      contradiction.
    destruct (decision_correct P); simpl.
      contradiction.
    reflexivity.
  refine pick val (decision P).
    simplify with monad laws.
    reflexivity.
  apply decision_decides.
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
  apply refine_If_Then_Else; trivial.
Qed.

Lemma refine_IfDec_Then_Else_ret :
  forall `{Decidable P} ResultT (t e : ResultT),
    refine (IfDec P Then ret t Else ret e)
           (ret (IfDec P Then t Else e)).
Proof.
  intros.
  unfold IfDec_Then_Else.
  apply refine_If_Then_Else_ret; trivial.
Qed.

Ltac decidability :=
  repeat
    match goal with
    | [ |- refine (ret ?Z) ?H ] => higher_order_reflexivity
    | [ |- refine (x <- ret ?Z; ?V) ?H ] => simplify with monad laws; simpl
    | [ |- refine (x <- y <- ?Z; ?W; ?V) ?H ] => simplify with monad laws; simpl
    | [ |- refine (IfDec ?P Then ?T Else ?E) ?H ] =>
      etransitivity;
        [ apply refine_IfDec_Then_Else;
            [ decidability | decidability ]
        | try rewrite refine_IfDec_Then_Else_ret;
          decidability ]
    end.

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
Proof. t' P. Qed.

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
Proof. t' P. Qed.

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
Proof. t' P. Qed.

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
Proof. t' P. Qed.
