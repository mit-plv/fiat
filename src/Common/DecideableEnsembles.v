Require Import Fiat.Common Coq.Arith.Arith Coq.Bool.Bool Coq.Sets.Ensembles.

Class DecideableEnsemble {A} (P : Ensemble A) :=
  { dec : A -> bool;
    dec_decides_P : forall a, dec a = true <-> P a}.

Lemma Decides_false {A} :
  forall (P : Ensemble A)
         (P_dec : DecideableEnsemble P) a,
    dec a = false <-> ~ (P a).
Proof.
  split; unfold not; intros.
  + apply dec_decides_P in H0; congruence.
  + case_eq (dec a); intros; eauto.
    apply dec_decides_P in H0; intuition.
Qed.

Instance DecideableEnsemble_gt {A} (f f' : A -> nat)
  : DecideableEnsemble (fun a => f a > f' a) :=
  {| dec a := if le_lt_dec (f a) (f' a) then false else true |}.
Proof.
  intros; find_if_inside; intuition.
Defined.

Instance DecideableEnsemble_And
         {A : Type}
         {P P' : Ensemble A}
         {P_dec : DecideableEnsemble P}
         {P'_dec : DecideableEnsemble P'}
: DecideableEnsemble (fun a => P a /\ P' a) :=
  {| dec a := (@dec _ _ P_dec a) && (@dec _ _  P'_dec a) |}.
Proof.
  intros; rewrite <- (@dec_decides_P _ P),
          <- (@dec_decides_P _ P').
  setoid_rewrite andb_true_iff; reflexivity.
Defined.

(* Class used to overload equality test notation (==) in queries. *)
Class Query_eq (A : Type) :=
      {A_eq_dec : forall a a' : A, {a = a'} + {a <> a'}}.

Infix "==" := (A_eq_dec) (at level 1).

Instance Query_eq_nat : Query_eq nat :=
  {| A_eq_dec := eq_nat_dec |}.

Instance Query_eq_bool : Query_eq bool :=
  {| A_eq_dec := bool_dec |}.

Instance Query_eq_list {A}
         (_ : Query_eq A)
  : Query_eq (list A) :=
  {| A_eq_dec := List.list_eq_dec A_eq_dec |}.

Instance DecideableEnsemble_NEqDec
         {A B : Type}
         {b_eq_dec : Query_eq B}
         (f f' : A -> B)
: DecideableEnsemble (fun a : A => f a <> f' a) :=
  {| dec a := if A_eq_dec (f a) (f' a) then false else true |}.
Proof.
  intros; find_if_inside; intuition.
Defined.

Instance DecideableEnsemble_EqDec {A B : Type}
         (B_eq_dec : Query_eq B)
         (f f' : A -> B)
: DecideableEnsemble (fun a => eq (f a) (f' a)) :=
  {| dec a := if A_eq_dec (f a) (f' a) then true else false |}.
Proof.
  intros; find_if_inside; split; congruence.
Defined.

Instance DecideableEnsemble_Not
         {A : Type}
         (P : Ensemble A)
         {P_dec : DecideableEnsemble P}
: DecideableEnsemble (fun a => ~ P a) :=
  {| dec a := negb (dec a) |}.
Proof.
  intros; case_eq (dec a); intros; intuition eauto.
  - discriminate.
  - rewrite dec_decides_P in H; intuition.
  - rewrite <- dec_decides_P in H1; congruence.
Defined.

Instance DecideableEnsemble_True
         {A : Type}
: DecideableEnsemble (fun a : A => True) :=
  {| dec a := true |}.
Proof.
  intros; intuition eauto.
Defined.

Instance DecideableEnsemble_False
         {A : Type}
: DecideableEnsemble (fun a : A => False) :=
  {| dec a := false |}.
Proof.
  intros; intuition eauto; discriminate.
Defined.

Instance DecideableEnsemble_Or
         {A : Type}
         (P P' : Ensemble A)
         {P_dec : DecideableEnsemble P}
         {P'_dec : DecideableEnsemble P'}
: DecideableEnsemble (fun a : A => P a \/ P' a) :=
  {| dec a := if dec (P := P) a then true else dec (P := P') a |}.
Proof.
  intros; case_eq (dec (P := P) a);
  [ rewrite dec_decides_P | rewrite Decides_false];
  intuition.
  setoid_rewrite dec_decides_P in H0; intuition.
  setoid_rewrite dec_decides_P; intuition.
Defined.
