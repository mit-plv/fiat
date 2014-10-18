Require Export Coq.Strings.String.
Require Export Parsers.StringLike.

Set Implicit Arguments.

Module StringPreStringLike <: PreStringLike.
  Definition CharType := Ascii.ascii.
  Definition t := string.
  Delimit Scope string_like_scope with string_like.
  Bind Scope string_like_scope with t.
  Local Open Scope string_like_scope.
  Definition Singleton (x : CharType) : t := String.String x EmptyString.
  Definition Empty : t := EmptyString.
  Definition Concat : t -> t -> t := append.
  Definition bool_eq (x y : t) := if string_dec x y then true else false.
  Definition Length : t -> nat := String.length.

  Notation "[[ x ]]" := (Singleton x) : string_like_scope.
  Infix "++" := Concat : string_like_scope.
  Infix "=s" := bool_eq (at level 70, right associativity) : string_like_scope.

  Local Hint Unfold bool_eq Concat Empty Singleton t CharType Length : core.
  Local Hint Extern 0 => match goal with H : S _ = 0 |- _ => destruct (NPeano.Nat.neq_succ_0 _ H) end.

  Local Ltac t :=
    autounfold with core in *;
    solve [ abstract (let x := fresh "x" in
                      let IHx := fresh "IHx" in
                      intro x; induction x as [|? ? IHx]; try reflexivity; simpl;
                      intros;
                      f_equal;
                      auto)
          | intros; split; congruence
          | intros; edestruct string_dec; split; congruence ].

  Lemma bool_eq_correct : forall x y, (x =s y) = true <-> x = y.
  Proof. t. Qed.
  Lemma Associativity : forall x y z, (x ++ y) ++ z = x ++ (y ++ z).
  Proof. t. Qed.
  Lemma LeftId : forall x, Empty ++ x = x.
  Proof. t. Qed.
  Lemma RightId : forall x, x ++ Empty = x.
  Proof. t. Qed.
  Lemma Length_correct : forall s1 s2, Length s1 + Length s2 = Length (s1 ++ s2).
  Proof. t. Qed.
  Lemma Length_Empty : Length Empty = 0.
  Proof. t. Qed.
  Lemma Empty_Length : forall s1, Length s1 = 0 -> s1 = Empty.
  Proof. t. Qed.
End StringPreStringLike.

Module StringStringLike := MakeStringLike StringPreStringLike.
