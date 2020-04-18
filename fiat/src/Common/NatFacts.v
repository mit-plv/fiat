Require Import Coq.Classes.Morphisms.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.

Lemma min_def {x y} : min x y = x - (x - y).
Proof. apply Min.min_case_strong; omega. Qed.
Lemma max_def {x y} : max x y = x + (y - x).
Proof. apply Max.max_case_strong; omega. Qed.
Ltac coq_omega := omega.
Ltac handle_min_max_for_omega :=
  repeat match goal with
         | [ H : context[min _ _] |- _ ] => rewrite !min_def in H
         | [ H : context[max _ _] |- _ ] => rewrite !max_def in H
         | [ |- context[min _ _] ] => rewrite !min_def
         | [ |- context[max _ _] ] => rewrite !max_def
         end.
Ltac handle_min_max_for_omega_case :=
  repeat match goal with
         | [ H : context[min _ _] |- _ ] => revert H
         | [ H : context[max _ _] |- _ ] => revert H
         | [ |- context[min _ _] ] => apply Min.min_case_strong
         | [ |- context[max _ _] ] => apply Max.max_case_strong
         end;
  intros.
Ltac omega_with_min_max :=
  handle_min_max_for_omega;
  omega.
Ltac omega_with_min_max_case :=
  handle_min_max_for_omega_case;
  omega.
Tactic Notation "omega" := coq_omega.
Tactic Notation "omega" "*" := omega_with_min_max_case.
Tactic Notation "omega" "**" := omega_with_min_max.

Section NatFacts.
  Lemma le_r_le_max :
    forall x y z,
      x <= z -> x <= max y z.
  Proof. intros; omega *. Qed.

  Lemma le_l_le_max :
    forall x y z,
      x <= y -> x <= max y z.
  Proof. intros; omega *. Qed.

  Lemma le_neq_impl :
    forall m n, m < n -> m <> n.
  Proof. intros; omega. Qed.

  Lemma gt_neq_impl :
    forall m n, m > n -> m <> n.
  Proof. intros; omega. Qed.

  Lemma lt_refl_False :
    forall x,
      lt x x -> False.
  Proof. intros; omega. Qed.

  Lemma beq_nat_eq_nat_dec :
    forall x y,
      beq_nat x y = if eq_nat_dec x y then true else false.
  Proof.
    intros; destruct (eq_nat_dec _ _); [ apply beq_nat_true_iff | apply beq_nat_false_iff ]; assumption.
  Qed.

  Lemma min_minus_l x y
  : min (x - y) x = x - y.
  Proof. omega *. Qed.
  Lemma min_minus_r x y
  : min x (x - y) = x - y.
  Proof. omega *. Qed.

  Lemma sub_twice x y : x - (x - y) = min x y.
  Proof. omega *. Qed.

  Lemma minus_ge {x y : nat} (H : x - y >= x) : {x = 0} + {y = 0}.
  Proof. destruct x; [ left | right]; omega. Qed.
End NatFacts.

Fixpoint minusr (n m : nat) {struct m} : nat
  := match m with
       | 0 => n
       | S l => minusr (pred n) l
     end.

Lemma minusr_minus n m
: minusr n m = minus n m.
Proof.
  revert m; induction n; simpl;
  induction m; simpl; auto.
Qed.

Delimit Scope natr_scope with natr.
Infix "-" := minusr : natr_scope.

Module minusr_notation.
  Infix "-" := minusr : nat_scope.
End minusr_notation.

Section dec_prod.
  Local Notation dec T := (T + (T -> False))%type (only parsing).
  Context (P : nat -> Type).
  Fixpoint dec_stabalize'
             (max : nat)
             (Hstable : forall n, n >= max -> P n -> P (S n))
             (Hdec : forall n, n <= max -> dec (P n))
             {struct max}
  : dec (forall n, P n).
  Proof.
    destruct max as [|max];
    [ clear dec_stabalize' | specialize (dec_stabalize' max) ].
    { destruct (Hdec 0 (le_refl _)) as [Hd|Hd]; [ left | right ].
      { intro n.
        induction n as [|n IHn].
        { assumption. }
        { apply Hstable; [ auto with arith | assumption ]. } }
      { intro Pn; apply Hd, Pn. } }
    { destruct (Hdec (S max)) as [Hdecmax|Hdecmax];
      [ reflexivity | | right; solve [ auto with nocore ] ].
      apply dec_stabalize'.
      { intros n Hn; specialize (Hstable n).
        unfold ge in *.
        destruct (le_lt_eq_dec _ _ Hn) as [pf|npf].
        { auto with nocore. }
        { intro; subst; assumption. } }
      { intros n pf.
        apply le_S in pf.
        auto with nocore. } }
  Defined.

  Local Notation iffT A B := ((A -> B) * (B -> A))%type (only parsing).

  Fixpoint dec_stabalize
             (max : nat)
             (Hstable : forall n, n >= max -> iffT (P n) (P (S n)))
             (Hdec : forall n, n <= max -> dec (P n))
             {struct max}
  : ({ n : nat & (n <= max) * P n }%type + (forall n, P n -> False))%type.
  Proof.
    destruct max as [|max];
    [ clear dec_stabalize | specialize (dec_stabalize max) ].
    { destruct (Hdec 0 (le_refl _)) as [Hd|Hd]; [ left | right ].
      { exists 0; split; [ reflexivity | assumption ]. }
      { intros n Pn. apply Hd.
        clear -Pn Hstable.
        specialize (fun n => Hstable n (le_0_n _)).
        induction n; [ assumption  | apply IHn ].
        apply Hstable; assumption. } }
    { destruct (Hdec (S max)) as [HdecSmax|HdecSmax];
      [ reflexivity | | ].
      { left; eexists; split; [ reflexivity | eassumption ]. }
      { destruct (Hdec max) as [Hdecmax|Hdecmax];
        [ solve [ auto with arith ] | | ].
        { left; eexists; split; [ | eassumption ]; auto with arith. }
        { destruct dec_stabalize as [[n [??]]|];
          [
          |
          | left; exists n; split; [ solve [ auto with arith ] | assumption ]
          | right; assumption ].
          { intros n Hn.
            destruct (le_lt_eq_dec _ _ Hn) as [pf|npf].
            pose proof (Hstable n).
            unfold ge in *.
            { auto with nocore. }
            { split; intro; subst;
              exfalso; eauto with nocore. } }
          { intros n pf.
            apply le_S in pf.
            auto with nocore. } } } }
  Defined.
End dec_prod.

Lemma nat_rect3_ext
       {A B C D}
       (P := fun n => forall (a : A n) (b : B n a), C n a b -> D)
       (z z' : P 0)
       (Hz : forall a b c, z a b c = z' a b c)
       (s s' : forall n, P n -> P (S n))
       (Hs : forall n f g (pf : forall a b c, f a b c = g a b c) a b c,
               s n f a b c = s' n g a b c)
       n a b c
: nat_rect P z s n a b c = nat_rect P z' s' n a b c.
Proof.
  revert a b c; induction n as [|n IHn]; simpl; intros.
  { apply Hz. }
  { apply Hs; intros.
    apply IHn. }
Qed.

Lemma minus_plus_min x y
: x - y + min y x = x.
Proof. omega *. Qed.

Lemma min_case_strong_r n m (P : nat -> Type)
: (n <= m -> P n) -> (m < n -> P m) -> P (min n m).
Proof.
  destruct (Compare_dec.le_lt_dec n m);
  first [ rewrite Min.min_r by omega
        | rewrite Min.min_l by omega ];
  auto.
Qed.

Lemma min_case_strong_l n m (P : nat -> Type)
: (n < m -> P n) -> (m <= n -> P m) -> P (min n m).
Proof.
  destruct (Compare_dec.le_lt_dec m n);
  first [ rewrite Min.min_r by omega
        | rewrite Min.min_l by omega ];
  auto.
Qed.

Lemma beq_0_1_leb x
: (EqNat.beq_nat x 1 || EqNat.beq_nat x 0)%bool = Compare_dec.leb x 1.
Proof.
  destruct x as [|[|]]; simpl; reflexivity.
Qed.

Lemma beq_S_leb x n
: (EqNat.beq_nat x (S n) || Compare_dec.leb x n)%bool = Compare_dec.leb x (S n).
Proof.
  revert x; induction n as [|n IHn]; simpl.
  { intros [|[|]]; reflexivity. }
  { intros [|x]; [ reflexivity | apply IHn ]. }
Qed.

Lemma min_max_sub {a x f}
  : min a (x - f) = x - (max (x - a) f).
Proof. omega *. Qed.

Lemma if_to_min {x y}
  : (if x <? y then x else y) = min x y.
Proof.
  apply min_case_strong_l; intro.
  { rewrite (proj2 (Nat.ltb_lt _ _)) by assumption.
    reflexivity. }
  { destruct (x <? y) eqn:H'; [ | reflexivity ].
    apply Nat.ltb_lt in H'.
    omega. }
Qed.

Lemma min_sub_same {x y} : min x y - x = 0.
Proof. omega *. Qed.

Lemma min_subr_same {x y} : (min x y - x)%natr = 0.
Proof. clear; rewrite minusr_minus; omega *. Qed.

Lemma beq_nat_min_0 {x y}
  : EqNat.beq_nat (min x y) 0 = orb (EqNat.beq_nat x 0) (EqNat.beq_nat y 0).
Proof. destruct x, y; simpl; reflexivity. Qed.

Lemma max_min_n {x y} : max (min x y) y = y.
Proof. omega *. Qed.

Global Instance S_Proper_le : Proper (le ==> le) S.
Proof. repeat intro; omega. Qed.

Global Instance nat_rect_Proper_nondep {A}
  : Proper
      (eq
         ==> pointwise_relation _ (pointwise_relation _ eq)
         ==> forall_relation (fun _ => eq))
      (nat_rect (fun _ => A)).
Proof.
  intros ??? ?? H; repeat intro; subst.
  pose proof (@Nat.recursion_wd A eq) as H'.
  unfold Nat.recursion in H'.
  apply H'; try reflexivity.
  repeat intro; subst; apply H.
Qed.

Global Instance nat_rect_Proper_nondep_respectful {A}
  : Proper
      (eq
         ==> pointwise_relation _ (pointwise_relation _ eq)
         ==> eq ==> eq)
      (nat_rect (fun _ => A)).
Proof.
  repeat intro; subst; apply nat_rect_Proper_nondep; try assumption; reflexivity.
Qed.
