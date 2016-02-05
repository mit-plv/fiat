(** * Mapping predicates over [StringLike] things *)
Require Import Coq.Classes.Morphisms Coq.Classes.RelationClasses Coq.Program.Basics.
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

  (*Lemma after_last_char_such_that_0
        (might_be_empty : Prop)
        (str : String)
        (n : nat)
        P
        (H' : is_after_last_char_such_that might_be_empty str 0 P)
  : might_be_empty.
  Proof.
    destruct_head_hnf and.
    destruct_head_hnf or;
      destruct_head_hnf and; trivial.
    destruct (length str);
      simpl in *;
      exfalso; omega.
  Qed.*)

  Lemma after_last_char_such_that_end
        (*{might_be_empty : Prop}*)
        {str : String}
        {P}
  : is_after_last_char_such_that (*might_be_empty*) str (length str) P
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
                 => destruct (fun pf => for_last_char_combine (T := T') pf H H'); [ tauto | | ];
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
  := length str
     - nat_rect
         (fun _ => nat)
         0
         (fun len' find_after_last_char_such_that'
          => let otherwise := S find_after_last_char_such_that' in
             match get len' str with
             | Some ch => if P ch
                          then 0
                          else otherwise
             | None => otherwise
             end)
         len.

(*Lemma find_after_last_char_such_that'_S {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char}
      (P : Char -> bool)
      (len : nat)
      (str : String)
  : find_after_last_char_such_that' P (S len) str
    = length str
      - let otherwise := S (length str - find_after_last_char_such_that' P len str) in
        match get len str with
        | Some ch => if P ch
                     then 0
                     else otherwise
        | None => otherwise
        end.
Proof.
  unfold find_after_last_char_such_that'.
  match goal with
  | [ |- appcontext[@nat_rect ?P ?Z ?Sc (S ?n)] ]
    => change (nat_rect P Z Sc (S n)) with (Sc n (@nat_rect P Z Sc n))
  end.
  cbv beta zeta.
  apply f_equal.
  edestruct get.
  SearchAbout (?x - (?y - _)).
unfold nat_rect; fold nat_rect.

  cbv beta.
  simpl.
  reflexivity.
Qed.*)

Definition find_after_last_char_such_that {Char} {HSLM} {HSL} str P
  := @find_after_last_char_such_that' Char HSLM HSL P (length str) str.
