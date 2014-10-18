(** * Definition of Context Free Grammars *)
Require Import Coq.Lists.List Coq.Program.Program.
Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Import Omega.

Set Implicit Arguments.

(** Something is string-like (for a given type of characters) if it
    has an associative concatenation operation and decidable
    equality. *)
Module Type PreStringLike.
  Parameter CharType : Type.
  Parameter t : Type.
  Delimit Scope string_like_scope with string_like.
  Bind Scope string_like_scope with t.
  Local Open Scope string_like_scope.
  Parameter Singleton : CharType -> t.
  Notation "[[ x ]]" := (Singleton x) : string_like_scope.
  Parameter Empty : t.
  Parameter Concat : t -> t -> t.
  Infix "++" := Concat : string_like_scope.
  Parameter bool_eq : t -> t -> bool.
  Infix "=s" := bool_eq (at level 70, right associativity) : string_like_scope.
  Axiom bool_eq_correct : forall x y, (x =s y) = true <-> x = y.
  Parameter Length : t -> nat.
  Axiom Associativity : forall x y z, (x ++ y) ++ z = x ++ (y ++ z).
  Axiom LeftId : forall x, Empty ++ x = x.
  Axiom RightId : forall x, x ++ Empty = x.
  Axiom Length_correct : forall s1 s2, Length s1 + Length s2 = Length (s1 ++ s2).
  Axiom Length_Empty : Length Empty = 0.
  Axiom Empty_Length : forall s1, Length s1 = 0 -> s1 = Empty.
End PreStringLike.

Module Type StringLike.
  Include PreStringLike.

  Parameter str_le : t -> t -> Prop.
  Infix "≤s" := str_le (at level 70, right associativity).
  Axiom str_le_refl : Reflexive str_le.
  Global Existing Instance str_le_refl.
  Axiom str_le_antisym : Antisymmetric _ eq str_le.
  Global Existing Instance str_le_antisym.
  Axiom str_le_trans : Transitive str_le.
  Global Existing Instance str_le_trans.
  Axiom str_le1_append : forall s1 s2, s1 ≤s s1 ++ s2.
  Axiom str_le2_append : forall s1 s2, s2 ≤s s1 ++ s2.
End StringLike.

Module MakeStringLike (S : PreStringLike) <: StringLike.
  Include S.

  Definition str_le s1 s2
    := Length s1 < Length s2 \/ s1 = s2.
  Infix "≤s" := str_le (at level 70, right associativity).

  Global Instance str_le_refl : Reflexive str_le.
  Proof.
    repeat intro; right; reflexivity.
  Qed.

  Global Instance str_le_antisym : Antisymmetric _ eq str_le.
  Proof.
    intros ? ? [H0|H0]; repeat subst; intros [H1|H1]; repeat subst; try reflexivity.
    exfalso; eapply Lt.lt_irrefl;
    etransitivity; eassumption.
  Qed.

  Global Instance str_le_trans : Transitive str_le.
  Proof.
    intros ? ? ? [H0|H0]; repeat subst; intros [H1|H1]; repeat subst;
    first [ reflexivity
          | left; assumption
          | left; etransitivity; eassumption ].
  Qed.

  Global Add Parametric Relation : _ str_le
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
             | [ H : S _ = 0 |- _ ] => destruct (NPeano.Nat.neq_succ_0 _ H)
             | [ |- ?x < ?x + S _ \/ _ ] => left; omega
             | [ |- ?x < S _ + ?x \/ _ ] => left; omega
           end.

  Lemma str_le1_append s1 s2
  : s1 ≤s s1 ++ s2.
  Proof.
    hnf.
    rewrite <- Length_correct.
    case_eq (s2 =s Empty);
      destruct (NPeano.Nat.eq_dec (Length s2) 0);
      str_le_append_t.
  Qed.

  Lemma str_le2_append s1 s2
  : s2 ≤s s1 ++ s2.
  Proof.
    hnf.
    rewrite <- Length_correct.
    case_eq (s1 =s Empty);
      destruct (NPeano.Nat.eq_dec (Length s1) 0);
      str_le_append_t.
  Qed.
End MakeStringLike.
