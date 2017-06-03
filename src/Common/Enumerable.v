Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.StringFacts.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.

Set Implicit Arguments.

Class Enumerable A
  := { enumerate : list A;
       enumerate_correct : forall x, List.In x enumerate }.

Global Arguments enumerate A {_}.

Section enum.
  Context {A B : Type} (beq : B -> B -> bool).

  Definition enumerate_fun_beq (enumerate : list A) (f g : A -> B)
  : bool
    := EqNat.beq_nat (List.length (List.filter (fun x => negb (beq (f x) (g x))) enumerate)) 0.

  Definition enumerate_fun_bl_in
             (bl : forall x y, beq x y = true -> x = y)
             (enumerate : list A) (f g : A -> B)
  : enumerate_fun_beq enumerate f g = true -> forall x, List.In x enumerate -> f x = g x.
  Proof.
    unfold enumerate_fun_beq.
    intros H x H'.
    apply EqNat.beq_nat_true in H.
    apply bl.
    destruct (beq (f x) (g x)) eqn:Heq; [ reflexivity | exfalso ].
    apply Bool.negb_true_iff in Heq.
    match type of H with
      | context[List.filter ?f ?ls]
        => pose proof (proj2 (@List.filter_In _ f x ls) (conj H' Heq)) as H'';
          destruct (List.filter f ls)
    end.
    { simpl in *.
      destruct H''. }
    { simpl in *; omega. }
  Qed.

  Definition enumerate_fun_bl
             (bl : forall x y, beq x y = true -> x = y)
             (enumerate : list A)
             (enumerate_bl : forall x, List.In x enumerate)
             (f g : A -> B)
  : enumerate_fun_beq enumerate f g = true -> forall x, f x = g x.
  Proof.
    intros; eapply enumerate_fun_bl_in; try eassumption; trivial.
  Qed.

  Definition enumerate_fun_false_lb_in
             (lb : forall x y, x = y -> beq x y = true)
             (enumerate : list A) (f g : A -> B)
  : enumerate_fun_beq enumerate f g = false -> { x | List.In x enumerate /\ f x <> g x }.
  Proof.
    induction enumerate as [|y ys IHys];
    unfold enumerate_fun_beq in *; simpl in *;
    intros H.
    { exfalso; clear -H; abstract discriminate. }
    { destruct (beq (f y) (g y)) eqn:Heq; simpl in *.
      { specialize (IHys H).
        exists (proj1_sig IHys); split; [ right | ];
        apply (proj2_sig IHys). }
      { exists y.
        split; [ left; reflexivity | ].
        intro H'.
        apply lb in H'.
        clear -H' Heq.
        generalize dependent (beq (f y) (g y)); clear; intros.
        abstract congruence. } }
  Defined.

  Definition enumerate_fun_false_lb
             (lb : forall x y, x = y -> beq x y = true)
             (enumerate : list A)
             (f g : A -> B)
  : enumerate_fun_beq enumerate f g = false -> { x | f x <> g x }.
  Proof.
    intro H.
    eexists (proj1_sig (enumerate_fun_false_lb_in lb enumerate f g H)).
    apply (proj2_sig (enumerate_fun_false_lb_in lb enumerate f g H)).
  Defined.

  Definition enumerate_fun_lb
             (lb : forall x y, x = y -> beq x y = true)
             (enumerate : list A)
             (f g : A -> B)
  : (forall x, f x = g x) -> enumerate_fun_beq enumerate f g = true.
  Proof.
    destruct (enumerate_fun_beq enumerate f g) eqn:Heq; [ reflexivity | ].
    intro H; exfalso.
    apply enumerate_fun_false_lb in Heq; [ | assumption.. ].
    destruct Heq; eauto with nocore.
  Qed.
End enum.

Section enumerable.
  Context {A} {H : Enumerable A} {B} (beq : B -> B -> bool).

  Definition enumerable_fun_beq : (A -> B) -> (A -> B) -> bool
    := enumerate_fun_beq beq (enumerate A).
  Definition enumerable_fun_bl
             (bl : forall x y, beq x y = true -> x = y)
             (f g : A -> B)
  : enumerable_fun_beq f g = true -> forall x, f x = g x
    := enumerate_fun_bl beq bl (enumerate A) enumerate_correct f g.
  Definition enumerable_fun_false_lb
             (lb : forall x y, x = y -> beq x y = true)
             (f g : A -> B)
  : enumerable_fun_beq f g = false -> { x | f x <> g x }
    := enumerate_fun_false_lb beq lb (enumerate A) f g.
  Definition enumerable_fun_lb
             (lb : forall x y, x = y -> beq x y = true)
             (f g : A -> B)
  : (forall x, f x = g x) -> enumerable_fun_beq f g = true
    := enumerate_fun_lb beq lb (enumerate A) f g.
End enumerable.

Scheme Equality for unit.
Definition unit_bl := internal_unit_dec_bl.
Definition unit_lb := internal_unit_dec_lb.

Local Ltac t bl :=
  abstract (
      let x := fresh in
      intro x; apply (list_in_bl bl); revert x;
      repeat intros []; simpl; try reflexivity
    ).

Global Instance enumerable_unit : Enumerable unit
  := { enumerate := tt::nil }.
Proof. t unit_bl. Defined.

Global Instance enumerable_Empty_set : Enumerable Empty_set
  := { enumerate := nil }.
Proof. intros []. Defined.

Global Instance enumerable_True : Enumerable True
  := { enumerate := I::nil }.
Proof. intros []; left; reflexivity. Defined.

Global Instance enumerable_False : Enumerable False
  := { enumerate := nil }.
Proof. intros []. Defined.

Global Instance enumerable_bool : Enumerable bool
  := { enumerate := true::false::nil }.
Proof. t (@bool_bl). Defined.

Global Instance enumerable_sum `{Enumerable A, Enumerable B} : Enumerable (A + B)
  := { enumerate := List.map inl (enumerate A) ++ List.map inr (enumerate B) }.
Proof.
  intros [x|x]; apply in_or_app; [ left | right ];
  apply in_map;
  apply enumerate_correct.
Defined.

Global Instance enumerable_prod `{Enumerable A, Enumerable B} : Enumerable (A * B)
  := { enumerate := List.flat_map (fun a => List.map (pair a) (enumerate B)) (enumerate A) }.
Proof.
  intros [a b].
  apply List.in_flat_map.
  exists a; split.
  { apply enumerate_correct. }
  { apply in_map;
    apply enumerate_correct. }
Defined.

Definition enumerate_ascii : list Ascii.ascii
  := Eval compute in List.map Ascii.ascii_of_nat (up_to 256).

Global Instance enumerable_ascii : Enumerable Ascii.ascii
  := { enumerate := enumerate_ascii }.
Proof.
  intro x.
  abstract (
      rewrite <- (Ascii.ascii_nat_embedding x);
      change enumerate_ascii with (List.map Ascii.ascii_of_nat (up_to 256));
      apply List.in_map, in_up_to, nat_of_ascii_small
    ).
Defined.

Lemma filter_enumerate {A} {HE : Enumerable A} P a (H : List.filter P (enumerate A) = a::nil)
  : (forall a', is_true (P a') <-> a = a').
Proof.
  intro a'; split; intros;
  assert (H' : In a' (filter P (enumerate A)) <-> In a' (a::nil))
    by (rewrite H; reflexivity);
  clear H; subst; simpl in *;
  rewrite filter_In in H';
  split_iff; split_and;
  repeat match goal with
         | [ H : _ \/ False -> _ |- _ ] => specialize (fun k => H (or_introl k))
         | [ H : _ /\ _ -> _ |- _ ] => specialize (fun a b => H (conj a b))
         | _ => progress specialize_by (apply enumerate_correct)
         | _ => progress specialize_by assumption
         | _ => progress specialize_by (exact eq_refl)
         | _ => progress destruct_head or
         | _ => progress destruct_head False
         | _ => assumption
         end.
Qed.
