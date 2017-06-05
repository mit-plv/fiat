(** * Mapping predicates over [StringLike] things *)
Require Import Coq.omega.Omega.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.StringLike.ForallChars.
Require Import Fiat.Parsers.StringLike.LastChar.
Require Import Fiat.Common.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Local Arguments min !_ !_.
Local Arguments minus !_ !_.

Section is_after_last_char_such_that.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Definition is_after_last_char_such_that
             (*(might_be_empty : Prop)*)
             (str : String)
             (n : nat)
             P
    := forall_chars (drop n str) (fun ch => ~P ch)
       /\ for_last_char (take n str) P (*/\ 0 < min n (length str))
           \/ (might_be_empty /\ min n (length str) = 0))*).

  Lemma unfold_is_after_last_char_such_that str n P
  : is_after_last_char_such_that str n P
    <-> (forall_chars (drop n str) (fun ch => ~P ch)
         /\ for_last_char (take n str) P).
  Proof.
    reflexivity.
  Qed.

  Lemma after_last_char_such_that_nil
        (str : String)
        (n : nat)
        P
        (Hlen : length str = 0)
  : is_after_last_char_such_that str n P.
  Proof.
    unfold is_after_last_char_such_that.
    split; [ apply forall_chars_nil | apply for_last_char_nil ];
    rewrite ?take_length, ?drop_length;
    try apply Min.min_case_strong; omega.
  Qed.

  Lemma after_last_char_such_that_0
        (*might_be_empty : Prop*)
        (str : String)
        P
  : is_after_last_char_such_that (*might_be_empty*) str 0 P
    <-> forall_chars str (fun ch => ~P ch).
  Proof.
    unfold is_after_last_char_such_that.
    rewrite drop_0.
    split.
    { intros; destruct_head and.
      assumption. }
    { split; [ assumption | ].
      apply for_last_char_nil.
      rewrite take_length; reflexivity. }
  Qed.

  Lemma after_last_char_such_that_after_end
        (*{might_be_empty : Prop}*)
        {str : String}
        {P}
        {n}
        (Hle : length str <= n)
  : is_after_last_char_such_that (*might_be_empty*) str n P
    <-> for_last_char str P(* /\ (might_be_empty \/ 0 < length str))*).
  Proof.
    unfold is_after_last_char_such_that.
    rewrite take_long by omega.
    split; intro;
    destruct_head_hnf and;
    destruct_head_hnf or;
    destruct_head_hnf and; repeat split; trivial;
      try rewrite Min.min_idempotent in *;
      try solve [ left; assumption
                | right; omega
                | apply for_last_char_nil; omega
                | apply forall_chars_nil; rewrite ?drop_length, ?take_length; try apply Min.min_case_strong; intros; omega
                | destruct (length str);
                  try solve [ left; repeat split; eauto; omega
                            | right; repeat split; eauto; omega ] ].
  Qed.

  Lemma after_last_char_such_that_end
        (*{might_be_empty : Prop}*)
        {str : String}
        {P}
  : is_after_last_char_such_that (*might_be_empty*) str (length str) P
    <-> for_last_char str P(* /\ (might_be_empty \/ 0 < length str))*).
  Proof.
    apply after_last_char_such_that_after_end; reflexivity.
  Qed.

  Lemma is_after_last_char_such_that_drop
        (*(might_be_empty : Prop)*)
        (str : String)
        (n : nat)
        P
  : is_after_last_char_such_that (*might_be_empty*) str (S n) P
    -> is_after_last_char_such_that (*might_be_empty*) (drop 1 str) n P(* \/ ((*might_be_empty /\*) length str <= 1))*).
  Proof.
    revert dependent str; induction n as [|n IHn]; intros;
      unfold is_after_last_char_such_that in *;
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
             | [ H : ?x < ?y |- _ \/ (_ /\ ?y <= ?x) ] => left

             | [ H : ?x = 0 |- context[?x] ] => rewrite H
             | _ => apply forall_chars_nil; rewrite ?take_length, ?drop_length; reflexivity
             | _ => omega
             | [ H : ?A /\ ?B -> ?C |- _ ] => specialize (fun x y => H (conj x y))
             | [ H : _ -> ?A /\ ?B -> ?C |- _ ] => specialize (fun a x y => H a (conj x y))
             | [ H : _ |- _ ] => progress rewrite ?drop_0, ?drop_drop, ?take_take, ?drop_length, ?take_length, ?take_drop, ?Nat.add_1_r, ?Nat.le_sub_le_add_r, <- ?(Plus.plus_comm 2), <- ?Nat.lt_add_lt_sub_r in H
             | _ => progress rewrite ?drop_0, ?drop_drop, ?take_take, ?drop_length, ?take_length, ?take_drop, ?Nat.add_1_r, ?Nat.le_sub_le_add_r, <- ?(Plus.plus_comm 2), <- ?Nat.lt_add_lt_sub_r
             | _ => progress destruct_head or
             | [ |- _ /\ _ ] => split
             | [ |- _ <-> _ ] => split
             | _ => left; repeat split; trivial; omega
             | _ => right; repeat split; trivial; omega

             | [ H : for_last_char ?str ?P |- for_last_char (drop ?n ?str) ?P ]
               => eapply for_last_char__add_drop; eexact H

             | [ H : for_last_char (drop _ _) _ |- _ ]
               => rewrite <- for_last_char__drop in H by (rewrite ?take_length; apply Min.min_case_strong; omega)
             | [ |- forall_chars (drop _ (take _ _)) _ ]
               => rewrite drop_take, <- minus_Sn_m, minus_diag by omega; simpl;
                    apply (proj1 (forall_chars_take _ _))
             | [ H : forall_chars (drop ?n ?str) ?P |- forall_chars (drop (S ?n) ?str) ?P ]
               => rewrite <- (drop_drop str 1 n); apply (proj1 (forall_chars_drop _ _)); assumption
             end.
  Qed.

  Global Instance is_after_last_char_such_that_Proper
  : Proper ((*impl ==> *)beq ==> eq ==> pointwise_relation _ iff ==> impl) is_after_last_char_such_that.
  Proof.
    repeat intro; subst.
    unfold is_after_last_char_such_that in *.
    setoid_subst_rel beq.
    setoid_subst_rel impl.
    setoid_subst_rel (pointwise_relation Char iff).
    assumption.
  Qed.

  Global Instance is_after_last_char_such_that_Proper_flip
  : Proper ((*flip impl ==> *)beq ==> eq ==> pointwise_relation _ iff ==> flip impl) is_after_last_char_such_that.
  Proof.
    repeat intro; subst.
    unfold is_after_last_char_such_that in *.
    setoid_subst_rel beq.
    setoid_subst_rel (pointwise_relation Char iff).
    unfold flip in *.
    setoid_subst_rel impl.
    assumption.
  Qed.

  Global Instance is_after_last_char_such_that_Proper_iff
  : Proper ((*iff ==> *)beq ==> eq ==> pointwise_relation _ iff ==> iff) is_after_last_char_such_that.
  Proof.
    repeat intro; subst.
    unfold is_after_last_char_such_that in *.
    setoid_subst_rel beq.
    setoid_subst_rel iff.
    setoid_subst_rel (pointwise_relation Char iff).
    reflexivity.
  Qed.

  Lemma is_after_last_char_such_that_eq_nat_iff
        (*(might_be_empty : Prop)*)
        (str : String)
        (n n' : nat)
        P
        (H0 : is_after_last_char_such_that (*might_be_empty*) str n P)
        (H1 : is_after_last_char_such_that (*might_be_empty*) str n' P)
  : n = n' \/ (n >= length str /\ n' >= length str).
  Proof.
    revert dependent n'; revert dependent str; induction n; intros;
      [ destruct n'; intros;
        [ left; reflexivity
        | ]
      | destruct n'; intros;
        [ right; intros
        | ] ];
      [ unfold is_after_last_char_such_that in *;
        repeat match goal with
               | _ => assumption
               | [ H : and _ _ |- _ ] => destruct H
               | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
               | [ H : _ |- _ ] => rewrite drop_0 in H
               | [ H : forall_chars _ _, H' : for_last_char _ _ |- ?T ]
                 => apply (forall_chars_for_last_char_overlap (R := T) H H'); solve [ omega | tauto | exfalso; tauto ]
               | [ H : ?x = 0 |- context[?x] ] => rewrite H
               | _ => omega
               | _ => progress destruct_head and
               | [ H : context[_ - 0] |- _ ] => rewrite Nat.sub_0_r in H
               | _ => progress destruct_head or
               | [ |- _ /\ _ ] => split
               | [ |- 0 = S _ \/ _ ] => right
               | [ H : for_last_char (take 0 _) _ |- _ ] => clear H
               | [ H : forall_chars ?str ?P, H' : forall_chars (drop _ ?str) ?P |- _ ] => clear H'
               | [ H : forall_chars ?str ?P, H' : forall_chars (take _ ?str) ?P |- _ ] => clear H'
               | _ => right; repeat split; solve [ assumption | omega ]
               | [ H : forall_chars ?str ?P, H' : for_last_char (take (S ?n) ?str) ?P' |- ?R ]
                 => rewrite forall_chars_take in H; specialize (H n); apply forall_chars__impl__for_last_char in H
               | [ H : for_last_char ?s ?P, H' : for_last_char ?s ?P' |- ?T' ]
                 => destruct (fun pf => for_last_char_combine (T := T') pf H H'); [ cbv beta; tauto | | ];
                    clear H H'
               | [ H : length (take _ _) = 0 |- _ ] => rewrite take_length in H
               | [ H : min ?x ?y = 0 |- _ ] => revert H; apply (Min.min_case_strong x y)
               | _ => intro
               end..
      | let H := fresh in
        edestruct IHn as [H|H];
        [ solve [ eauto using is_after_last_char_such_that_drop ]..
        | left; omega
        | right; rewrite drop_length in H; destruct_head and; omega ] ].
  Qed.
End is_after_last_char_such_that.

Global Opaque is_after_last_char_such_that.

Definition find_after_last_char_such_that' {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char}
           (P : Char -> bool)
           (len : nat)
           (str : String)
  : nat
  := nat_rect
       (fun _ => nat)
       0
       (fun len' otherwise
        => match get len' str with
             | Some ch => if P ch
                          then S len'
                          else otherwise
             | None => otherwise
           end)
       len.

Lemma find_after_last_char_such_that'_S {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}
      (P : Char -> bool)
      (len : nat)
      (str : String)
  : find_after_last_char_such_that' P (S len) str
    = let v := S (find_after_last_char_such_that' P len (drop 1 str)) in
      match get 0 str with
        | Some ch => match find_after_last_char_such_that' P len (drop 1 str) with
                       | 0 => if P ch then 1 else 0
                       | _ => v
                     end
        | None => 0
      end.
Proof.
  cbv zeta.
  revert str; induction len as [|len IHlen]; intros.
  { reflexivity. }
  { simpl in *.
    rewrite IHlen; clear IHlen.
    repeat match goal with
             | [ |- context[get ?n'] ]
               => not constr_eq n' 0; rewrite (get_drop (n := n'))
             | [ H : context[get ?n'] |- _ ]
               => not constr_eq n' 0; setoid_rewrite (get_drop (n := n')) in H
           end.
    replace (get 0 (drop len (drop 1 str))) with (get 0 (drop (S len) str))
      by (rewrite drop_drop; do 2 f_equal; omega).
    destruct (get 0 str) eqn:Hg0.
    { destruct (get 0 (drop (S len) str)) eqn:Hg1; [ | reflexivity ].
      edestruct P; reflexivity. }
    { apply no_first_char_empty in Hg0.
      rewrite has_first_char_nonempty
        by (rewrite drop_length, Hg0; reflexivity).
      reflexivity. } }
Qed.

Definition find_after_last_char_such_that {Char} {HSLM} {HSL} str P
  := @find_after_last_char_such_that' Char HSLM HSL P (length str) str.

Lemma find_after_last_char_such_that_drop {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}
      (str : String)
      (P : Char -> bool)
  : find_after_last_char_such_that str P
    = let v := S (find_after_last_char_such_that (drop 1 str) P) in
      match get 0 str with
        | Some ch => match find_after_last_char_such_that (drop 1 str) P with
                       | 0 => if P ch then 1 else 0
                       | _ => v
                     end
        | None => 0
      end.
Proof.
  unfold find_after_last_char_such_that.
  destruct (length str) eqn:Hlen.
  { rewrite has_first_char_nonempty by assumption; simpl; reflexivity. }
  { rewrite find_after_last_char_such_that'_S; simpl.
    rewrite drop_length, Hlen; simpl.
    rewrite Nat.sub_0_r.
    reflexivity. }
Qed.

Lemma is_after_last_char_such_that__find_after_last_char_such_that {Char} {HSLM HSL} {HSLP : @StringLikeProperties Char HSLM HSL} str P
      (*might_be_empty*)
      (H : exists n, is_after_last_char_such_that (*might_be_empty*) str n (fun ch => is_true (P ch)))
: is_after_last_char_such_that (*might_be_empty*) str (@find_after_last_char_such_that Char HSLM HSL str P) (fun ch => is_true (P ch)).
Proof.
  destruct H as [n H].
  rewrite unfold_is_after_last_char_such_that in H |- *.
  destruct H as [H0 H1].
  generalize dependent str.
  induction n as [|n IHn]; intros.
  { cut (find_after_last_char_such_that str P = 0);
    [ intro Heq; rewrite Heq; split; assumption
    | ].
    rewrite drop_0 in H0.
    unfold find_after_last_char_such_that, find_after_last_char_such_that'.
    induction (length str) as [|len IHlen]; simpl;
    [ reflexivity | rewrite IHlen; clear IHlen ].
    rewrite forall_chars_get in H0.
    specialize (H0 len).
    edestruct get; [ | reflexivity ].
    specialize (H0 _ eq_refl).
    edestruct P; simpl in *; intuition. }
  { specialize (IHn (drop 1 str)).
    rewrite !drop_drop, !take_drop, !Nat.add_1_r in IHn.
    specialize_by assumption.
    specialize_by (apply for_last_char__add_drop; assumption).
    rewrite find_after_last_char_such_that_drop; simpl.
    destruct (get 0 str) eqn:Hg0.
    { destruct (find_after_last_char_such_that (drop 1 str) P) eqn:Hf.
      { destruct_head and.
        destruct (P c) eqn:Hp.
        { split; try assumption; [].
          rewrite <- for_last_char_singleton; [ | apply get_0 ]; eassumption. }
        { rewrite drop_0.
          split; [ | apply for_last_char_nil; rewrite take_length; reflexivity ].
          apply (forall_chars__split _ _ 1); split; try assumption; [].
          rewrite <- forall_chars_singleton; [ | apply get_0; eassumption ].
          congruence. } }
      { destruct_head and; split; try assumption; [].
        rewrite for_last_char__drop; [ eassumption | ].
        rewrite take_length; simpl.
        destruct (length str) as [|[|]] eqn:Hlen;
          [ exfalso
          | exfalso
          | ].
        { rewrite has_first_char_nonempty in Hg0 by assumption; congruence. }
        { move Hf at bottom.
          unfold find_after_last_char_such_that in Hf.
          rewrite drop_length, Hlen in Hf.
          simpl in Hf.
          congruence. }
        { simpl; omega. } } }
    { rewrite drop_0.
      apply no_first_char_empty in Hg0.
      split; [ apply forall_chars_nil | apply for_last_char_nil ];
      rewrite ?take_length, Hg0; reflexivity. } }
Qed.
