Require Import
  Fiat.ADT
  Coq.Arith.Compare_dec
  Coq.ZArith.ZArith
  Coq.QArith.QArith
  Coq.QArith.Qabs.

Generalizable All Variables.

Class Decidable (P : Prop) := {
  decision : {P} + {~ P}
}.
Arguments decision P {_} /.

Global Program Instance not_Decidable {P : Prop} `{Decidable P} :
  Decidable (~ P) := {
  decision := match decision P with
              | in_left => in_right
              | in_right => in_left
              end
}.

Global Program Instance and_Decidable {P Q : Prop}
  `{Decidable P} `{Decidable Q} : Decidable (P /\ Q) := {
  decision := match decision P with
              | left HP =>
                match decision Q with
                | left HQ => left (conj HP HQ)
                | in_right => in_right
                end
              | in_right => in_right
              end
}.
Obligation 1. intuition. Qed.
Obligation 2. intuition. Qed.

Global Program Instance or_Decidable {P Q : Prop}
  `{Decidable P} `{Decidable Q} : Decidable (P \/ Q) := {
  decision := match decision P with
              | left HP => left (or_introl HP)
              | in_right =>
                match decision Q with
                | left HQ => left (or_intror HQ)
                | in_right => in_right
                end
              end
}.
Obligation 1. intuition. Qed.

Global Program Instance impl_Decidable {P Q : Prop}
  `{Decidable P} `{Decidable Q} : Decidable (P -> Q) := {
  decision := match decision P with
              | left HP =>
                match decision Q with
                | left HQ => left (fun _ => HQ)
                | in_right => in_right
                end
              | in_right => in_left
              end
}.
Obligation 2. contradiction. Qed.

Global Program Instance bool_eq_Decidable {n m : bool} : Decidable (n = m) := {
  decision := bool_dec n m
}.

Global Program Instance ascii_eq_Decidable {n m : Ascii.ascii} :
  Decidable (n = m) := {
  decision := Ascii.ascii_dec n m
}.

Global Program Instance nat_eq_Decidable {n m : nat} : Decidable (n = m) := {
  decision := eq_nat_dec n m
}.

Global Program Instance le_Decidable {n m} : Decidable (le n m) := {
  decision := Compare_dec.le_dec n m
}.

Global Instance lt_Decidable {n m} : Decidable (lt n m) := le_Decidable.

Global Program Instance N_eq_Decidable {n m : N} : Decidable (n = m) := {
  decision := N.eq_dec n m
}.

Global Program Instance Nle_Decidable {n m} : Decidable (Nle n m) := {
  decision := match N.leb_spec0 n m with
              | ReflectT _ => in_left
              | ReflectF _ => in_right
              end
}.

Global Program Instance Nlt_Decidable {n m} : Decidable (Nlt n m) := {
  decision := match N.ltb_spec0 n m with
              | ReflectT _ => in_left
              | ReflectF _ => in_right
              end
}.

Global Program Instance Z_eq_Decidable {n m : Z} : Decidable (n = m) := {
  decision := Z.eq_dec n m
}.

Global Program Instance Zle_Decidable {n m} : Decidable (Zle n m) := {
  decision := match Z.leb_spec0 n m with
              | ReflectT _ => in_left
              | ReflectF _ => in_right
              end
}.

Global Program Instance Zlt_Decidable {n m} : Decidable (Zlt n m) := {
  decision := match Z.ltb_spec0 n m with
              | ReflectT _ => in_left
              | ReflectF _ => in_right
              end
}.

Global Program Instance Q_eq_Decidable {n m : Q} : Decidable (n == m) := {
  decision := Qeq_dec n m
}.

Global Program Instance Qle_Decidable {n m} : Decidable (Qle n m) := {
  decision := match Q_dec n m with
              | inleft in_left  => in_left
              | inleft in_right => in_right
              | inright _       => in_left
              end
}.
Obligation 1. apply Qlt_le_weak; assumption. Qed.
Obligation 2. apply Qlt_not_le; assumption. Qed.
Obligation 3. apply Qle_lteq; right; assumption. Qed.

Global Program Instance Qlt_Decidable {n m} : Decidable (Qlt n m) := {
  decision := match Qlt_le_dec n m with
              | in_left  => in_left
              | in_right => in_right
              end
}.
Obligation 2. apply Qle_not_lt; assumption. Qed.

Section ListDec.
  Variable A : Type.
  Variable eq_dec : forall x y : A, {x = y} + {x <> y}.

  Global Program Instance list_eq_Decidable {xs ys : list A} :
    Decidable (xs = ys) := {
    decision := List.list_eq_dec eq_dec xs ys
  }.

  Global Program Instance list_in_Decidable {xs : list A} {x : A} :
    Decidable (List.In x xs) := {
    decision := List.in_dec eq_dec x xs
  }.
End ListDec.

Definition IfDec_Then_Else {A} (P : Prop) `{Decidable P} (t e : A) :=
  If decision P Then t Else e.
Arguments IfDec_Then_Else {A} P {_} t e : simpl never.

Notation "'IfDec' P 'Then' t 'Else' e" :=
  (IfDec_Then_Else P t e) (at level 70) : comp_scope.

Local Ltac t p := intros; destruct p; intuition.

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
      destruct (decision P); simpl.
        reflexivity.
      contradiction.
    destruct (decision P); simpl.
      contradiction.
    reflexivity.
  refine pick val (bool_of_sumbool (decision P)).
    simplify with monad laws.
    reflexivity.
  destruct (decision P); trivial.
Qed.

Lemma refine_IfDec_Then_Else :
  forall (A : Type) `{Decidable P} (x y : Comp A),
    refine x y
      -> forall x0 y0 : Comp A, refine x0 y0
      -> refine (IfDec P Then x Else x0) (IfDec P Then y Else y0).
Proof.
  intros.
  unfold IfDec_Then_Else.
  apply refine_If_Then_Else; trivial.
Qed.

Lemma refine_IfDec_Then_Else_ret :
  forall `{Decidable P} ResultT (t e : ResultT),
    refine (IfDec P Then ret t Else ret e) (ret (IfDec P Then t Else e)).
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
Proof. t P. Qed.

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
Proof. t P. Qed.

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
Proof. t P. Qed.

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
Proof. t P. Qed.
