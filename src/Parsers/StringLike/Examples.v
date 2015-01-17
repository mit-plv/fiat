(** * Definitions of some specific string-like types *)
Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Parsers.StringLike.Core.

Set Implicit Arguments.

Local Hint Extern 0 => match goal with H : S _ = 0 |- _ => destruct (Nat.neq_succ_0 _ H) end.

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
