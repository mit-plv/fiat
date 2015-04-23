(** * Theorems about string-like types *)
Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Program.Basics.
Require Import Coq.Arith.Lt.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.StringLike.Core Fiat.Common.Le Fiat.Common.UIP.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.
Require Import Fiat.Common.Le.

Set Implicit Arguments.

Section String.
  Context {Char} `{StringLikeProperties Char}.

  Definition bool_eq_refl {x : String} : x =s x.
  Proof.
    reflexivity.
  Defined.

  Definition bool_eq_sym {x y : String} : ((x =s y) = (y =s x) :> bool)%string_like.
  Proof.
    case_eq (y =s x)%string_like; intro H';
    [
    | case_eq (x =s y)%string_like; intro H'' ].
    { apply (symmetry (R := (fun x y => x =s y))) in H'; assumption. }
    { apply (symmetry (R := (fun x y => x =s y))) in H''; hnf in H''.
      etransitivity; [ exact (eq_sym H'') | exact H' ]. }
    { reflexivity. }
  Defined.

  Definition bool_eq_trans {x y z : String} : (x =s y) -> (y =s z) -> (x =s z).
  Proof.
    apply (transitivity (R := (fun x y => x =s y))).
  Defined.

  Global Instance str_le_Proper_iff : Proper (beq ==> beq ==> iff) str_le | 1000.
  Proof.
    repeat match goal with
             | _ => intro
             | _ => split
             | [ H : _ ≤s _ |- _ ] => destruct H
             | _ => left; assumption
             | _ => right; assumption
             | _ => right; symmetry; assumption
             | [ H : ?x =s _ |- _ ] => rewrite H in *; clear x H
             | [ H : _ =s ?x |- _ ] => rewrite <- H in *; clear x H
           end.
  Qed.

  Global Instance str_le_Proper : Proper (beq ==> beq ==> impl) str_le.
  Proof.
    intros x y H' x' y' H'' H'''.
    apply (@str_le_Proper_iff x y H' x' y' H''); assumption.
  Qed.

  Global Instance str_le_Proper' : Proper (beq ==> beq ==> Basics.flip impl) str_le.
  Proof.
    intros x y H' x' y' H'' H'''.
    apply (@str_le_Proper_iff _ _ H' _ _ H''); assumption.
  Qed.

  Global Instance str_le_refl : Reflexive str_le.
  Proof.
    repeat intro; right; reflexivity.
  Qed.

  Global Instance str_le_antisym : @Antisymmetric _ beq _ str_le.
  Proof.
    intros ? ? [H'|H']; repeat subst; intros [H1|H1]; repeat subst; try reflexivity;
    solve [ reflexivity
          | exfalso; omega
          | assumption
          | symmetry; assumption ].
  Qed.

  Global Instance str_le_trans : Transitive str_le.
  Proof.
    intros ? ? ? [H'|H']; repeat subst; intros [H1|H1]; repeat subst;
    try (rewrite H1 in *; clear H1);
    try (rewrite H' in *; clear H');
    first [ reflexivity
          | left; assumption
          | left; etransitivity; eassumption ].
  Qed.

  Local Open Scope string_like_scope.

  Global Instance str_le_length_le_Proper : Proper (str_le ==> le) length.
  Proof.
    intros x y [H'|H']; auto with arith.
    rewrite H'; reflexivity.
  Qed.

  Global Instance str_le_length_le_Proper' : Proper (Basics.flip str_le ==> Basics.flip le) length.
  Proof.
    intros x y [H'|H']; unfold Basics.flip in *; auto with arith.
    rewrite H'; reflexivity.
  Qed.

  Lemma str_le_take {str n}
  : take n str ≤s str.
  Proof.
    destruct (le_gt_dec (length str) n).
    { right; apply take_long; assumption. }
    { left; rewrite take_short_length; omega. }
  Qed.

  Lemma str_le_drop {str n}
  : drop n str ≤s str.
  Proof.
    destruct n.
    { rewrite drop_0; reflexivity. }
    { hnf; rewrite drop_length.
      case_eq (length str); intro H'.
      { right; apply bool_eq_empty.
        { rewrite drop_length, H'; reflexivity. }
        { assumption. } }
      { intro; left; omega. } }
  Qed.

  Lemma take_length {str n}
  : length (take n str) = min n (length str).
  Proof.
    destruct (le_ge_dec (length str) n).
    { rewrite take_long by assumption.
      rewrite Min.min_r by assumption.
      reflexivity. }
    { rewrite take_short_length by assumption.
      rewrite Min.min_l by assumption.
      reflexivity. }
  Qed.

  Lemma length_le_trans
        {a b c : String} (H0' : length a < length b) (H1' : b ≤s c)
  : length a < length c.
  Proof.
    destruct H1'; setoid_subst.
    { etransitivity; eassumption. }
    { assumption. }
  Qed.

  Lemma strle_to_sumbool
        (s1 s2 : String) (f : String -> nat)
        (H' : f s1 < f s2 \/ s1 =s s2)
  : {f s1 < f s2} + {s1 =s s2}.
  Proof.
    unfold beq in *.
    case_eq (s1 =s s2).
    { intro H''; right; reflexivity. }
    { intro H''; left.
      destruct H' as [H' | H']; trivial.
      hnf in *.
      abstract congruence. }
  Defined.

  Section strle_choose.
    Context (s1 s2 : String) (f : String -> nat)
            (f_Proper : Proper (beq ==> eq) f)
            (H0' : f s1 < f s2 \/ s1 =s s2).

    Definition strle_left (H' : f s1 < f s2)
    : H0' = or_introl H'.
    Proof.
      destruct H0' as [H''|H'']; try clear H0'; [ apply f_equal | exfalso ].
      { apply le_proof_irrelevance. }
      { setoid_subst s1.
        eapply lt_irrefl; eassumption. }
    Qed.

    Definition strle_right (H' : s1 =s s2)
    : H0' = or_intror H'.
    Proof.
      destruct H0' as [H''|H'']; try clear H0'; [ exfalso | apply f_equal ].
      { setoid_subst s1; eapply lt_irrefl; eassumption. }
      { apply dec_eq_uip.
        decide equality. }
    Qed.
  End strle_choose.

  Lemma str_seq_lt_false
        {a b : String}
        (H0' : length a < length b)
        (H' : a =s b)
  : False.
  Proof.
    rewrite H' in H0'.
    eapply lt_irrefl; eassumption.
  Qed.

  Lemma singleton_exists_unique : forall s, length s = 1 -> exists !ch, s ~= [ ch ].
  Proof.
    intros s H'.
    destruct (singleton_exists s H') as [ch H''].
    exists ch.
    split; [ apply H'' | ].
    intro; apply singleton_unique; assumption.
  Qed.

  Lemma singleton_take {str ch} (H' : str ~= [ ch ]) n
  : take (S n) str =s str.
  Proof.
    eapply bool_eq_char; try eassumption.
    rewrite take_long; try assumption.
    apply length_singleton in H'; omega.
  Qed.
End String.
