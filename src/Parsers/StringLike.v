(** * Definition of Context Free Grammars *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program.
Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Import Omega.

Set Implicit Arguments.
Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.

(** Something is string-like (for a given type of characters) if it
    has an associative concatenation operation and decidable
    equality. *)
Record string_like (CharType : Type) :=
  {
    String :> Type;
    Singleton : CharType -> String where "[ x ]" := (Singleton x);
    Empty : String;
    Concat : String -> String -> String where "x ++ y" := (Concat x y);
    bool_eq : String -> String -> bool;
    bool_eq_correct : forall x y : String, bool_eq x y = true <-> x = y;
    Length : String -> nat;
    Associativity : forall x y z, (x ++ y) ++ z = x ++ (y ++ z);
    LeftId : forall x, Empty ++ x = x;
    RightId : forall x, x ++ Empty = x;
    Length_correct : forall s1 s2, Length s1 + Length s2 = Length (s1 ++ s2);
    Length_Empty : Length Empty = 0;
    Empty_Length : forall s1, Length s1 = 0 -> s1 = Empty
  }.

Delimit Scope string_like_scope with string_like.
Bind Scope string_like_scope with String.
Arguments Concat {_%type_scope _} (_ _)%string_like.
Arguments bool_eq {_%type_scope _} (_ _)%string_like.
Arguments Length {_%type_scope _} _%string_like.
Notation "[[ x ]]" := (@Singleton _ _ x) : string_like_scope.
Infix "++" := (@Concat _ _) : string_like_scope.
Infix "=s" := (@bool_eq _ _) (at level 70, right associativity) : string_like_scope.

Local Hint Extern 0 => match goal with H : S _ = 0 |- _ => destruct (NPeano.Nat.neq_succ_0 _ H) end.

Definition stringlike_dec {CharType} {String : string_like CharType} (s1 s2 : String)
: { s1 = s2 } + { s1 <> s2 }.
Proof.
  case_eq (bool_eq s1 s2); intro H; [ left | right ].
  { apply bool_eq_correct; exact H. }
  { intro H'; apply bool_eq_correct in H'.
    generalize dependent (s1 =s s2)%string_like; clear; intros.
    abstract congruence. }
Defined.

Definition string_stringlike : string_like Ascii.ascii.
Proof.
  refine {| String := string;
            Singleton := fun x => String.String x EmptyString;
            Empty := EmptyString;
            Concat := append;
            Length := String.length;
            bool_eq x y := if string_dec x y then true else false |};
  solve [ abstract (let x := fresh "x" in
                    let IHx := fresh "IHx" in
                    intro x; induction x as [|? ? IHx]; try reflexivity; simpl;
                    intros;
                    f_equal;
                    auto)
        | intros; split; congruence
        | intros; edestruct string_dec; split; congruence ].
Defined.

Definition str_le {CharType} {String : string_like CharType} (s1 s2 : String)
  := Length s1 < Length s2 \/ s1 = s2.
Infix "≤s" := str_le (at level 70, right associativity).

Global Instance str_le_refl {CharType String} : Reflexive (@str_le CharType String).
Proof.
  repeat intro; right; reflexivity.
Qed.

Global Instance str_le_antisym {CharType String} : Antisymmetric _ eq (@str_le CharType String).
Proof.
  intros ? ? [H0|H0]; repeat subst; intros [H1|H1]; repeat subst; try reflexivity.
  exfalso; eapply Lt.lt_irrefl;
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
