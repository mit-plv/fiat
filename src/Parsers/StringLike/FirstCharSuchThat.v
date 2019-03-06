(** * Mapping predicates over [StringLike] things *)

Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.StringLike.ForallChars.
Require Import Fiat.Parsers.StringLike.FirstChar.
Require Import Fiat.Common.
Require Import Fiat.Common.NatFacts.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section is_first_char_such_that.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Definition is_first_char_such_that
             (might_be_empty : Prop)
             (str : String)
             (n : nat)
             P
    := forall_chars (take n str) (fun ch => ~P ch)
       /\ ((for_first_char (drop n str) P /\ n < length str)
           \/ (might_be_empty /\ length str <= n)).

  Lemma first_char_such_that_past_end
        (might_be_empty : Prop)
        (str : String)
        (n : nat)
        P
        (H : length str <= n)
        (H' : is_first_char_such_that might_be_empty str n P)
  : might_be_empty.
  Proof.
    destruct_head_hnf and.
    destruct_head_hnf or;
      destruct_head_hnf and; trivial.
    exfalso; omega.
  Qed.

  Lemma first_char_such_that_0
        {might_be_empty : Prop}
        {str : String}
        {P}
  : is_first_char_such_that might_be_empty str 0 P
    <-> (for_first_char str P /\ (might_be_empty \/ length str > 0)).
  Proof.
    unfold is_first_char_such_that.
    rewrite drop_0.
    split; intro;
    destruct_head_hnf and;
    destruct_head_hnf or;
      destruct_head_hnf and; repeat split; trivial;
    try solve [ left; assumption
              | right; omega
              | apply for_first_char_nil; omega
              | apply forall_chars_nil; rewrite ?take_length; try apply Min.min_case_strong; intros; omega
              | destruct (length str);
                try solve [ left; repeat split; eauto; omega
                          | right; repeat split; eauto; omega ] ].
  Qed.

  Lemma is_first_char_such_that_drop
        (might_be_empty : Prop)
        (str : String)
        (n : nat)
        P
  : is_first_char_such_that might_be_empty str (S n) P
    <-> (is_first_char_such_that might_be_empty (drop 1 str) n P /\ for_first_char str (fun ch => ~P ch)).
  Proof.
    generalize dependent str; induction n; intros;
    unfold is_first_char_such_that in *;
    [
    | specialize (IHn (drop 1 str));
      rewrite (forall_chars__split _ _ 1) ];
    repeat match goal with
             | _ => assumption
             | _ => intro
             | _ => progress destruct_head and
             | _ => progress destruct_head iff
             | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
             | _ => progress simpl in *
             | [ H : _ |- _ ] => apply forall_chars__impl__for_first_char, for_first_char__take in H; assumption
             | [ H : for_first_char (take (S _) _) _ |- _ ] => apply for_first_char__take in H
             | [ H : for_first_char ?str ?P, H' : for_first_char ?str ?P' |- _ ]
               => destruct (fun H0 => for_first_char_combine (T := False) H0 H H'); cbv beta; [ tauto | clear H H' | tauto ]
             | [ H : ?x = 0 |- context[?x] ] => rewrite H
             | _ => apply forall_chars_nil; [ (rewrite ?take_length, ?drop_length; reflexivity).. ]
             | _ => omega
             | [ H : ?A /\ ?B -> ?C |- _ ] => specialize (fun x y => H (conj x y))
             | [ H : _ -> ?A /\ ?B -> ?C |- _ ] => specialize (fun a x y => H a (conj x y))
             | [ H : _ |- _ ] => progress rewrite ?drop_0, ?drop_drop, ?take_take, ?drop_length, ?take_length, ?drop_take, ?Nat.add_1_r, ?Nat.le_sub_le_add_r, <- ?(Plus.plus_comm 2), <- ?Nat.lt_add_lt_sub_r in H
             | _ => progress rewrite ?drop_0, ?drop_drop, ?take_take, ?drop_length, ?take_length, ?drop_take, ?Nat.add_1_r, ?Nat.le_sub_le_add_r, <- ?(Plus.plus_comm 2), <- ?Nat.lt_add_lt_sub_r
             | _ => progress destruct_head or
             | [ |- _ /\ _ ] => split
             | [ |- _ <-> _ ] => split
             | _ => left; repeat split; trivial; omega
             | _ => right; repeat split; trivial; omega
             | _ => apply for_first_char__for_first_char__iff_short;
                   [ rewrite take_length; destruct (length str); simpl in *; omega
                   | apply -> (for_first_char__take 0); assumption ]
           end.
  Qed.

  Global Instance is_first_char_such_that_Proper
  : Proper (impl ==> beq ==> eq ==> pointwise_relation _ iff ==> impl) is_first_char_such_that.
  Proof.
    repeat intro; subst.
    unfold is_first_char_such_that in *.
    setoid_subst_rel beq.
    setoid_subst_rel impl.
    setoid_subst_rel (pointwise_relation Char iff).
    assumption.
  Qed.

  Global Instance is_first_char_such_that_Proper_flip
  : Proper (flip impl ==> beq ==> eq ==> pointwise_relation _ iff ==> flip impl) is_first_char_such_that.
  Proof.
    repeat intro; subst.
    unfold is_first_char_such_that in *.
    setoid_subst_rel beq.
    setoid_subst_rel (pointwise_relation Char iff).
    unfold flip in *.
    setoid_subst_rel impl.
    assumption.
  Qed.

  Global Instance is_first_char_such_that_Proper_iff
  : Proper (iff ==> beq ==> eq ==> pointwise_relation _ iff ==> iff) is_first_char_such_that.
  Proof.
    repeat intro; subst.
    unfold is_first_char_such_that in *.
    setoid_subst_rel beq.
    setoid_subst_rel iff.
    setoid_subst_rel (pointwise_relation Char iff).
    reflexivity.
  Qed.

  Lemma is_first_char_such_that_eq_nat_iff
        (might_be_empty : Prop)
        (str : String)
        (n n' : nat)
        P
        (H0 : is_first_char_such_that might_be_empty str n P)
        (H1 : is_first_char_such_that might_be_empty str n' P)
  : n = n' \/ (n >= length str /\ n' >= length str /\ might_be_empty).
  Proof.
    generalize dependent n'; generalize dependent str; induction n; intros.
    { destruct n'; intros.
      { left; reflexivity. }
      { right.
        unfold is_first_char_such_that in *.
        repeat match goal with
                 | _ => assumption
                 | [ H : and _ _ |- _ ] => destruct H
                 | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
                 | [ H : _ |- _ ] => rewrite drop_0 in H
                 | [ H : _ |- _ ] => apply forall_chars__impl__for_first_char in H
                 | [ H : for_first_char (take (S _) _) _ |- _ ] => apply for_first_char__take in H
                 | [ H : for_first_char ?str ?P, H' : for_first_char ?str ?P' |- _ ]
                   => destruct (fun H0 => for_first_char_combine (T := False) H0 H H'); cbv beta; [ tauto | clear H H' | tauto ]
                 | [ H : ?x = 0 |- context[?x] ] => rewrite H
                 | _ => omega
                 | _ => progress destruct_head and
                 | _ => progress destruct_head or
                 | [ |- _ /\ _ ] => split
               end. } }
    { specialize (IHn (drop 1 str)).
      destruct n'; [ right; case_eq (length str) | ];
      repeat match goal with
               | [ H : is_first_char_such_that _ _ (S _) _ |- _ ] => apply is_first_char_such_that_drop in H
               | _ => progress destruct_head and
               | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
               | _ => intro
               | [ H : _ |- _ ] => progress rewrite ?drop_length, ?Nat.le_sub_le_add_r in H
               | [ H : ?x = 0, H' : context[?x] |- _ ] => rewrite H in H'
               | _ => progress simpl in *
               | [ |- _ /\ _ ] => split; try omega; []
               | _ => eapply first_char_such_that_past_end; [ | eassumption ]; omega
               | [ H : _ |- _ ] => unique pose proof (proj1 (proj1 first_char_such_that_0 H))
               | [ H : for_first_char ?str ?P, H' : for_first_char ?str ?P' |- _ ]
                 => destruct (fun H_new => for_first_char_combine (T := False) H_new H H'); cbv beta; [ tauto | clear H H' | tauto ]
               | _ => omega
               | _ => progress unfold ge in *
               | [ H : forall n', is_first_char_such_that ?P ?str n' ?P' -> _, H' : is_first_char_such_that ?P ?str _ ?P' |- _ ]
                 => specialize (H _ H')
               | _ => progress subst
               | _ => left; reflexivity
               | _ => right; repeat split; trivial; omega
               | _ => progress destruct_head or
             end. }
  Qed.
End is_first_char_such_that.

Global Opaque is_first_char_such_that.

Definition find_first_char_such_that' {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char}
           (P : Char -> bool)
           (len : nat)
           (str : String)
: nat
  := nat_rect
       (fun _ => nat)
       0
       (fun len' find_first_char_such_that'
        => let otherwise := S find_first_char_such_that' in
           match get (length str - S len') str with
             | Some ch => if P ch
                          then 0
                          else otherwise
             | None => otherwise
           end)
       len.

Lemma find_first_char_such_that'_S {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char}
      (P : Char -> bool)
      (len : nat)
      (str : String)
: find_first_char_such_that' P (S len) str
  = let otherwise := S (find_first_char_such_that' P len str) in
    match get (length str - S len) str with
      | Some ch => if P ch
                   then 0
                   else otherwise
      | None => otherwise
    end.
Proof.
  reflexivity.
Qed.

Definition find_first_char_such_that {Char} {HSLM} {HSL} str P
  := @find_first_char_such_that' Char HSLM HSL P (length str) str.

Global Instance find_first_char_such_that'_Proper
       {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char}
       {HSLP : StringLikeProperties Char}
  : Proper (pointwise_relation _ eq ==> eq ==> beq ==> eq)
           find_first_char_such_that'.
Proof.
  intros ?? Hfg n n' ? s s' H; subst n'.
  unfold find_first_char_such_that'.
  apply nat_rect_Proper_nondep; [ reflexivity | repeat intro ].
  setoid_subst_rel beq.
  edestruct get; try reflexivity.
  rewrite Hfg; reflexivity.
Qed.

Global Instance find_first_char_such_that_Proper
       {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char}
       {HSLP : StringLikeProperties Char}
  : Proper (beq ==> pointwise_relation _ eq ==> eq)
           find_first_char_such_that.
Proof.
  repeat intro; unfold find_first_char_such_that.
  setoid_subst_rel beq.
  setoid_subst_rel (pointwise_relation Char (@eq bool)).
  reflexivity.
Qed.
