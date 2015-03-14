(** * Definitions of some specific string-like types *)
Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Parsers.StringLike.Core Parsers.StringLike.Properties.
Require Import Common Common.Equality.

Set Implicit Arguments.

Section indexed.
  Context {CharType} {String0 : string_like CharType}.

  Definition empty_unique start length (str : String0)
    := (if (implb (str =s Empty _)%string_like
                  ((if Nat.eq_dec start 0 then true else false)
                     && (if Nat.eq_dec length 0 then true else false)))
             && (implb (if Nat.eq_dec length 0 then true else false)
                       (str =s Empty _)%string_like)
        then True
        else False)%bool.

  Local Arguments empty_unique / .

  Local Notation String1
    := ({ s : (nat * nat) * String0 (* (start_char, length, string) *)
        | empty_unique (fst (fst s)) (snd (fst s)) (snd s) }) (only parsing).

  Definition singleton (x : CharType) : String1.
  Proof.
    exists (0, 1, Singleton String0 x); simpl.
    abstract
      (
        case_eq ([[ x ]] =s Empty String0)%string_like; try constructor; [];
        intro H; exfalso;
        apply bool_eq_correct in H;
        apply Not_Singleton_Empty in H; trivial
      ).
  Defined.

  Global Arguments singleton / .

  Definition empty : String1.
  Proof.
    exists (0, 0, Empty String0); simpl.
    abstract (
        rewrite (proj2 (bool_eq_correct String0 (Empty _) (Empty _)) eq_refl);
        constructor
      ).
  Defined.

  Global Arguments empty / .

  Definition indexed_dec_eq' (s1 s2 : String1)
  : {proj1_sig s1 = proj1_sig s2} + {proj1_sig s1 <> proj1_sig s2}.
  Proof.
    revert s1 s2.
    repeat decide equality.
    match goal with
      | [ |- {?a = ?b} + {_} ]
        => case_eq (bool_eq a b); intro H; [ left | right ]
    end.
    { apply bool_eq_correct; assumption. }
    { intro H'; apply bool_eq_correct in H'.
      pose proof (eq_trans (eq_sym H') H) as H''.
      clear -H''.
      abstract discriminate. }
  Defined.

  Definition indexed_dec_eq (s1 s2 : String1)
  : {s1 = s2} + {s1 <> s2}.
  Proof.
    destruct (indexed_dec_eq' s1 s2) as [|n]; [ left | right ].
    { abstract (
          repeat match goal with
                   | [ s : sig _ |- _ ] => destruct s
                   | _ => progress simpl in *
                   | _ => progress subst
                   | _ => apply f_equal
                   | [ H : if ?b then _ else _ |- _ ] => destruct b
                   | [ H : True |- _ ] => destruct H
                   | [ H : False |- _ ] => destruct H
                   | _ => reflexivity
                 end
        ). }
    { intro H.
      apply (f_equal (@proj1_sig _ _)) in H.
      exact (n H). }
  Defined.

  Definition reduce (s : String1) : String1.
  Proof.
    SearchAbout ({_ <= _} + {_}).
    exists (0,
            snd (fst (proj1_sig s)),
            if Compare_dec.le_dec (Length (snd (proj1_sig s))) (fst (fst (proj1_sig s)))
            then
            fst (SplitAt
                   String0 (snd (fst (proj1_sig s)))
                   (snd (SplitAt String0 (fst (fst (proj1_sig s))) (snd (proj1_sig s)))))).
    simpl.
    repeat match goal with
             | [ H : _ |- _ ] => rewrite Length_Empty in H
             | [ H : _ |- _ ] => rewrite SplitAtLength_correct in H
             | [ H : _ |- _ ] => rewrite Bool.andb_false_r in H
             | [ H : _ |- _ ] => rewrite Bool.andb_true_r in H
             | _ => progress simpl in *
             | [ H : sig _ |- _ ] => destruct H
             | [ H : (_ * _)%type |- _ ] => destruct H
             | _ => progress subst
             | [ |- True ] => exact I
             | _ => congruence
             | [ |- context[(?s =s Empty String0)%string_like] ]
               => let H := fresh in
                  case_eq ((s =s Empty String0)%string_like);
                    intro H;
                    [ apply bool_eq_correct, (f_equal Length) in H | ]
             | [ |- context[Nat.eq_dec ?x ?y] ]
               => destruct (Nat.eq_dec x y)
             | [ H : min ?x ?y = _ |- _ ]
               => let H' := fresh in
                  destruct (Nat.min_dec x y) as [H'|H'];
                    rewrite H' in H;
                    clear H'
             | [ H' : context[(?s =s Empty String0)%string_like] |- _ ]
               => revert H';
                 let H := fresh in
                  case_eq ((s =s Empty String0)%string_like);
                    intros H H';
                    [ apply bool_eq_correct, (f_equal Length) in H | ]
           end.
    Focus 2.
    lazymatch goal with
             | [ H : min ?x ?y |- _ ]
               => let H' := fresh in
                  destruct (Nat.min_dec x y) as [H'|H'];
                    rewrite H' in H
end.
    SearchAbout (min _ _ = _)%bool.

  Definition indexed_stringlike
  : string_like CharType.
  Proof.
    refine {| String := String1;
              Singleton x := singleton x;
              Empty := empty;
              Length s := snd (fst (proj1_sig s));
              bool_eq s1 s2 := if indexed_dec_eq s1 s2 then true else false;
              SplitAt n s := (if Nat.eq_dec n 0
                              then (empty, s)
                              else if Compare_dec.le_dec (snd (fst (proj1_sig s))) n
                                   then (s, empty)
                                   else (exist _ (fst (fst (proj1_sig s)), n, snd (proj1_sig s)) _,
                                         exist _ (fst (fst (proj1_sig s)) + n, snd (fst (proj1_sig s)) - n, snd (proj1_sig s)) _));
              Concat s1 s2 := if (snd (proj1_sig s1) =s Empty _)%string_like
                              then s2
                              else if (snd (proj1_sig s2) =s Empty _)%string_like
                                   then s1
                                   else if (((snd (proj1_sig s1) =s snd (proj1_sig s2))%string_like)
                                              && (if Nat.eq_dec (fst (fst (proj1_sig s1)) + snd (fst (proj1_sig s1))) (fst (fst (proj1_sig s2))) then true else false))%bool
                                        then exist
                                               _
                                               (fst (fst (proj1_sig s1)),
                                                snd (fst (proj1_sig s1)) + snd (fst (proj1_sig s2)),
                                                snd (proj1_sig s1))
                                               _
                                        else
                                          exist
                                            _
                                            (0,
                                             snd (fst (proj1_sig s1)) + snd (fst (proj1_sig s2)),
                                             Concat (fst (SplitAt String0 (fst (fst (proj1_sig s1)) + snd (fst (proj1_sig s1))) (snd (proj1_sig s1))))
                                                    (snd (SplitAt String0 (fst (fst (proj1_sig s2))) (snd (proj1_sig s2)))))
                                            _ |}.
    { repeat match goal with
               | _ => intro
               | [ |- context[indexed_dec_eq ?x ?y] ] => destruct (indexed_dec_eq x y)
               | _ => progress subst
               | _ => split
               | _ => discriminate
               | _ => congruence
             end. }
    {
      |}.

|}.
|}.
            Concat := append;
            Length := String.length;
            bool_eq x y := if string_dec x y then true else false;
            SplitAt n s := (substring 0 n s, substring n (S (String.length s)) s)
         |};
  solve [ abstract (let x := fresh "x" in
                    let IHx := fresh "IHx" in
                    intro x; induction x as [|? ? IHx]; try reflexivity; simpl;
                    intros;
                    f_equal;
                    auto)
        | intros; split; congruence
        | intros; edestruct string_dec; split; congruence
        | abstract (repeat intro; exfalso; congruence)
        | abstract (simpl; intros; rewrite substring_concat', substring_correct3; auto with arith)
        | abstract (
              simpl;
              intros n s; revert n;
              induction s; intro n; destruct n; simpl; try reflexivity;
              rewrite IHs; reflexivity
            ) ].
Defined.



Local Hint Extern 0 => match goal with H : S _ = 0 |- _ => destruct (Nat.neq_succ_0 _ H) end.

Definition string_stringlike : string_like Ascii.ascii.
Proof.
  refine {| String := string;
            Singleton := fun x => String.String x EmptyString;
            Empty := EmptyString;
            Concat := append;
            Length := String.length;
            bool_eq x y := if string_dec x y then true else false;
            SplitAt n s := (substring 0 n s, substring n (S (String.length s)) s)
         |};
  solve [ abstract (let x := fresh "x" in
                    let IHx := fresh "IHx" in
                    intro x; induction x as [|? ? IHx]; try reflexivity; simpl;
                    intros;
                    f_equal;
                    auto)
        | intros; split; congruence
        | intros; edestruct string_dec; split; congruence
        | abstract (repeat intro; exfalso; congruence)
        | abstract (simpl; intros; rewrite substring_concat', substring_correct3; auto with arith)
        | abstract (
              simpl;
              intros n s; revert n;
              induction s; intro n; destruct n; simpl; try reflexivity;
              rewrite IHs; reflexivity
            ) ].
Defined.
