(** * Definitions of some specific string-like types *)
Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import ADTSynthesis.Parsers.StringLike.Core.
Require Import ADTSynthesis.Common.

Set Implicit Arguments.

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
        | abstract (
              simpl; intros;
              rewrite ?substring_concat', ?substring_correct3, ?substring_concat_length, ?substring_concat0 by auto with arith;
              auto with arith
            )
        | abstract (
              simpl;
              intros n s; revert n;
              induction s; intro n; destruct n; simpl; try reflexivity;
              rewrite IHs; reflexivity
        ) ].
Defined.
