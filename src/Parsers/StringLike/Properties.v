(** * Theorems about string-like types *)
Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.Lt.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import Parsers.StringLike.Core Common.Le Common.UIP.

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
