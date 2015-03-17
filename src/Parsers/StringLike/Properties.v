(** * Theorems about string-like types *)
Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.Lt.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import Parsers.StringLike.Core Common.Le Common.UIP.
Require Import Common.Equality.

Set Implicit Arguments.

Definition stringlike_dec {CharType} {String : string_like CharType} (s1 s2 : String)
: { s1 = s2 } + { s1 <> s2 }.
Proof.
  case_eq (bool_eq s1 s2); intro H; [ left | right ].
  { apply bool_eq_correct; exact H. }
  { intro H'; apply bool_eq_correct in H'.
    generalize dependent (s1 =s s2)%string_like; clear; intros.
    abstract congruence. }
Defined.

Lemma stringlike_uip {CharType} {String : string_like CharType} {s1 s2 : String}
      (p q : s1 = s2)
: p = q.
Proof.
  apply dec_eq_uip.
  apply stringlike_dec.
Qed.

Global Instance str_le_refl {CharType String} : Reflexive (@str_le CharType String).
Proof.
  repeat intro; right; reflexivity.
Qed.

Global Instance str_le_antisym {CharType String} : Antisymmetric _ eq (@str_le CharType String).
Proof.
  intros ? ? [H0|H0]; repeat subst; intros [H1|H1]; repeat subst; try reflexivity.
  exfalso; eapply lt_irrefl;
  etransitivity; eassumption.
Qed.

Global Instance str_le_trans {CharType String} : Transitive (@str_le CharType String).
Proof.
  intros ? ? ? [H0|H0]; repeat subst; intros [H1|H1]; repeat subst;
  first [ reflexivity
        | left; assumption
        | left; etransitivity; eassumption ].
Qed.

Add Parametric Relation {CharType String} : _ (@str_le CharType String)
    reflexivity proved by reflexivity
    transitivity proved by transitivity
      as str_le_rel.

Local Open Scope string_like_scope.

Local Ltac str_le_append_t :=
  repeat match goal with
           | _ => intro
           | _ => progress subst
           | [ H : (_ =s _) = true |- _ ] => apply bool_eq_correct in H
           | _ => progress rewrite ?LeftId, ?RightId
           | _ => right; reflexivity
           | [ H : Length _ = 0 |- _ ] => apply Empty_Length in H
           | [ H : Length ?s <> 0 |- _ ] => destruct (Length s)
           | [ H : ?n <> ?n |- _ ] => destruct (H eq_refl)
           | [ |- ?x < ?x + S _ \/ _ ] => left; omega
           | [ |- ?x < S _ + ?x \/ _ ] => left; omega
         end.

Lemma str_le1_append CharType (String : string_like CharType) (s1 s2 : String)
: s1 ≤s s1 ++ s2.
Proof.
  hnf.
  rewrite <- Length_correct.
  case_eq (s2 =s (Empty _));
  destruct (NPeano.Nat.eq_dec (Length s2) 0);
  str_le_append_t.
Qed.

Lemma str_le2_append CharType (String : string_like CharType) (s1 s2 : String)
: s2 ≤s s1 ++ s2.
Proof.
  hnf.
  rewrite <- Length_correct.
  case_eq (s1 =s Empty _);
  destruct (NPeano.Nat.eq_dec (Length s1) 0);
  str_le_append_t.
Qed.

Lemma length_le_trans {CharType} {String : string_like CharType}
      {a b c : String} (H : Length a < Length b) (H' : b ≤s c)
: Length a < Length c.
Proof.
  destruct H'; subst.
  { etransitivity; eassumption. }
  { assumption. }
Qed.

Lemma strle_to_sumbool {CharType} {String : string_like CharType}
      (s1 s2 : String) (f : String -> nat)
      (H : f s1 < f s2 \/ s1 = s2)
: {f s1 < f s2} + {s1 = s2}.
Proof.
  case_eq (s1 =s s2).
  { intro H'; right.
    abstract (apply bool_eq_correct in H'; exact H'). }
  { intro H'; left.
    abstract (
        destruct H; trivial;
        apply bool_eq_correct in H;
        generalize dependent (s1 =s s2)%string_like; intros; subst;
        discriminate
      ). }
Defined.

Section strle_choose.
  Context {CharType} {String : string_like CharType}
          (s1 s2 : String) (f : String -> nat)
          (H : f s1 < f s2 \/ s1 = s2).

  Definition strle_left (H' : f s1 < f s2)
  : H = or_introl H'.
  Proof.
    destruct H as [H''|H'']; subst; [ apply f_equal | exfalso ].
    { apply le_proof_irrelevance. }
    { eapply lt_irrefl; eassumption. }
  Qed.

  Definition strle_right (H' : s1 = s2)
  : H = or_intror H'.
  Proof.
    destruct H as [H''|H'']; [ subst; exfalso | apply f_equal ].
    { eapply lt_irrefl; eassumption. }
    { apply dec_eq_uip.
      clear.
      intro y.
      destruct (Bool.bool_dec (bool_eq s1 y) true) as [H|H].
      { left.
        apply bool_eq_correct; assumption. }
      { right; intro H'.
        apply bool_eq_correct in H'.
        auto. } }
  Qed.
End strle_choose.


Lemma NonEmpty_Length {CharType} {String : string_like CharType}
      (a : String)
      (H : a <> Empty _)
: Length a > 0.
Proof.
  case_eq (Length a); intro H'; try omega.
  apply Empty_Length in H'; subst.
  destruct (H eq_refl).
Qed.

Local Ltac lt_nonempty_t :=
  repeat match goal with
           | [ H : _ ≤s _ |- _ ] => destruct H
           | [ H : _ |- _ ] => progress rewrite ?plus_O_n, <- ?Length_correct in H
           | _ => progress rewrite ?plus_O_n, <- ?Length_correct
           | _ => assumption
           | _ => intro
           | _ => progress subst
           | _ => omega
           | [ H : _ <> Empty _ |- _ ] => apply NonEmpty_Length in H
         end.

Lemma strle_to_lt_nonempty_r {CharType} {String : string_like CharType}
      {a b c : String}
      (H : a <> Empty _)
      (H' : a ++ b ≤s c)
: Length b < Length c.
Proof. lt_nonempty_t. Qed.

Lemma strle_to_lt_nonempty_l {CharType} {String : string_like CharType}
      {a b c : String}
      (H : b <> Empty _)
      (H' : a ++ b ≤s c)
: Length a < Length c.
Proof. lt_nonempty_t. Qed.

Lemma str_seq_lt_false {CharType} {String : string_like CharType}
      {a b : String}
      (H : Length a < Length b)
      (H' : (a =s b) = true)
: False.
Proof.
  apply bool_eq_correct in H'; subst.
  apply lt_irrefl in H; assumption.
Qed.

Lemma neq_some_none_state_val {CharType} {String : string_like CharType} {P}
      {s1 s2 : StringWithSplitState String (fun x => option (P x))}
      (H : s1 = s2)
: match state_val s1, state_val s2 with
    | None, Some _ => False
    | Some _, None => False
    | _, _ => True
  end.
Proof.
  destruct H.
  destruct (state_val s1); exact I.
Qed.

Definition string_val_path {CharType String A}
      {s0 s1 : @StringWithSplitState CharType String A}
      (H : s0 = s1)
: string_val s0 = string_val s1
  := f_equal (@string_val _ _ _) H.

Definition state_val_path {CharType String A}
      {s0 s1 : @StringWithSplitState CharType String A}
      (H : s0 = s1)
: eq_rect _ _ (state_val s0) _ (string_val_path H) = state_val s1.
Proof.
  destruct H; reflexivity.
Defined.

(** This proof would be so much easier to read if we were using HoTT conventions, tactics, and lemmas. *)
Lemma lift_StringWithSplitState_injective {CharType String A B}
           (s0 s1 : @StringWithSplitState CharType String A)
           (lift : forall s, A s -> B s)
           (lift_injective : forall s a1 a2, lift s a1 = lift s a2 -> a1 = a2)
           (H : lift_StringWithSplitState s0 (lift _) = lift_StringWithSplitState s1 (lift _))
: s0 = s1.
Proof.
  pose proof (state_val_path H) as H'.
  generalize dependent (string_val_path H); clear H.
  destruct s0, s1; simpl in *.
  intro H'.
  destruct H'; simpl.
  intro H'.
  apply lift_injective in H'.
  destruct H'.
  reflexivity.
Qed.

Lemma lift_StringWithSplitState_pair_injective {CharType String A A' B B'}
           (s0 s1 : @StringWithSplitState CharType String A * @StringWithSplitState CharType String A')
           (lift : forall s, A s -> B s)
           (lift' : forall s, A' s -> B' s)
           (lift_injective : forall s a1 a2, lift s a1 = lift s a2 -> a1 = a2)
           (lift'_injective : forall s a1 a2, lift' s a1 = lift' s a2 -> a1 = a2)
           (H : (lift_StringWithSplitState (fst s0) (lift _),
                 lift_StringWithSplitState (snd s0) (lift' _))
                =
                (lift_StringWithSplitState (fst s1) (lift _),
                 lift_StringWithSplitState (snd s1) (lift' _)))
: s0 = s1.
Proof.
  pose proof (f_equal (@fst _ _) H) as H0.
  pose proof (f_equal (@snd _ _) H) as H1.
  clear H; simpl in *.
  apply lift_StringWithSplitState_injective in H0; [ | assumption.. ].
  apply lift_StringWithSplitState_injective in H1; [ | assumption.. ].
  apply injective_projections; assumption.
Qed.

Lemma in_lift_pair_StringWithSplitState_iff_injective {CharType String A A' B B'}
      {s0s1 : @StringWithSplitState CharType String A * @StringWithSplitState CharType String A'}
      {lift : forall s, A s -> B s}
      {lift' : forall s, A' s -> B' s}
      {lift_injective : forall s a1 a2, lift s a1 = lift s a2 -> a1 = a2}
      {lift'_injective : forall s a1 a2, lift' s a1 = lift' s a2 -> a1 = a2}
      {ls : list (StringWithSplitState String A * StringWithSplitState String A')}
      (H : List.In (lift_StringWithSplitState (fst s0s1) (lift _),
                    lift_StringWithSplitState (snd s0s1) (lift' _))
                   (List.map (fun s0s1 =>
                                (lift_StringWithSplitState (fst s0s1) (lift _),
                                 lift_StringWithSplitState (snd s0s1) (lift' _)))
                             ls))
: List.In s0s1 ls.
Proof.
  eapply in_map_iff_injective; [ | exact H ].
  simpl; intro.
  apply lift_StringWithSplitState_pair_injective; assumption.
Qed.
