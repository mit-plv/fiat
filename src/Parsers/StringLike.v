(** * Definition of Context Free Grammars *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program.
Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Import Coq.Logic.EqdepFacts.
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
    Empty_Length : forall s1, Length s1 = 0 -> s1 = Empty;
    Not_Singleton_Empty : forall x, Singleton x <> Empty
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
        | intros; edestruct string_dec; split; congruence
        | abstract (repeat intro; exfalso; congruence) ].
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

(** TODO: Move these *)
Lemma le_pred n m (H : n <= m) : pred n <= pred m.
Proof.
  induction H.
  { constructor. }
  { destruct m; simpl in *; try constructor; assumption. }
Defined.

Lemma le_SS n m (H : n <= m) : S n <= S m.
Proof.
  induction H.
  { constructor. }
  { constructor; assumption. }
Defined.

Lemma le_canonical n m : {n <= m} + {~n <= m}.
Proof.
  revert n; induction m; intro n.
  { destruct n.
    { left; constructor. }
    { right; clear.
      abstract auto with arith. } }
  { destruct (IHm n) as [IHm'|IHm'].
    { left; constructor; assumption. }
    { clear IHm'.
      specialize (IHm (pred n)).
      destruct IHm as [IHm|IHm], n; simpl in *.
      { left; constructor; assumption. }
      { left; apply le_SS; assumption. }
      { exfalso.
        abstract auto with arith. }
      { right; intro H.
        abstract (apply le_pred in H; simpl in *; auto). } } }
Defined.

Lemma le_canonical_nn {n} : le_canonical n n = left (le_n _).
Proof.
  induction n; simpl; try reflexivity.
  rewrite IHn; clear IHn.
  edestruct le_canonical; [ exfalso | reflexivity ].
  { eapply le_Sn_n; eassumption. }
Qed.

Lemma le_canonical_nS {n m pf} (H : le_canonical n m = left pf)
: le_canonical n (S m) = left (le_S _ _ pf).
Proof.
  simpl; rewrite H; reflexivity.
Qed.

Fixpoint le_proof_irrelevance_left {n m} (pf : n <= m)
: left pf = le_canonical n m.
Proof.
  destruct pf.
  { clear. rewrite le_canonical_nn; reflexivity. }
  { erewrite le_canonical_nS; [ reflexivity | ].
    symmetry.
    apply le_proof_irrelevance_left. }
Defined.

Lemma le_proof_irrelevance' {n m} (pf : {n <= m} + {~n <= m})
: le_canonical n m = match pf, le_canonical n m with
                       | left pf', _ => left pf'
                       | _, right pf' => right pf'
                       | right pf', left pf'' => match pf' pf'' with end
                     end.
Proof.
  destruct pf.
  { erewrite <- le_proof_irrelevance_left; reflexivity. }
  { edestruct le_canonical; try reflexivity.
    exfalso; eauto. }
Qed.

Lemma le_proof_irrelevance {n m} (pf pf' : n <= m) : pf = pf'.
Proof.
  transitivity (match le_canonical n m with
                  | left pf' => pf'
                  | right pf' => match pf' pf with end
                end).
  { rewrite (le_proof_irrelevance' (left pf)); reflexivity. }
  { rewrite (le_proof_irrelevance' (left pf')); reflexivity. }
Qed.

Lemma Eq_rect_eq_UIP_helper {U x y} (p : x = y :> U)
: p = match p in (_ = y) return (x = y) with eq_refl => eq_refl end.
Proof.
  destruct p; reflexivity.
Defined.

Lemma Eq_rect_eq_UIP_ U : Eq_rect_eq U -> UIP_ U.
Proof.
  lazy; intro H.
  intros x y p1 p2.
  destruct p2.
  specialize (H x (fun y => x = y) eq_refl p1); simpl in *.
  rewrite <- Eq_rect_eq_UIP_helper in H.
  symmetry; assumption.
Qed.

Definition dec_eq_adjust' {U x} (p : forall y : U, {x = y} + {x <> y}) y
: {x = y} + {x <> y}
  := match p x, p y with
       | left pf, left pf' => left (eq_trans (eq_sym pf) pf')
       | right pf, _ => match pf eq_refl with end
       | _, right pf => right pf
     end.

Lemma concat_Vp {U x y} (p : x = y :> U)
: eq_trans (eq_sym p) p = eq_refl.
Proof.
  destruct p; reflexivity.
Defined.

Lemma dec_eq_uip' {U x y} (pf : x = y)
      (p : forall y : U, {x = y} + {x <> y})
: pf = match dec_eq_adjust' p y with
         | left pf' => pf'
         | right pf' => match pf' pf with end
       end.
Proof.
  destruct pf.
  unfold dec_eq_adjust'.
  destruct (p x) as [|n].
  { symmetry; apply concat_Vp. }
  { destruct (n eq_refl). }
Defined.

Lemma dec_eq_uip {U x}
      (dec : forall y : U, {x = y} + {x <> y})
      y
      (p q : x = y :> U)
: p = q.
Proof.
  etransitivity; [ | symmetry ].
  { apply (dec_eq_uip' _ dec). }
  { etransitivity; [ apply (dec_eq_uip' _ dec) | ].
    edestruct @dec_eq_adjust' as [|n]; try reflexivity.
    destruct (n p). }
Qed.

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
