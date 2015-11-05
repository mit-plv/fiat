Require Import Coq.Numbers.Natural.Peano.NPeano Coq.Strings.String Coq.Arith.Lt Coq.Arith.Compare_dec.

Section GenSym.
  Local Unset Implicit Arguments.
  Local Open Scope string_scope.

  Lemma digitLtBase m {n} : not (m + n < m).
  Proof.
    red; intros; eapply Le.le_Sn_n; eauto using Le.le_trans, Plus.le_plus_l.
  Qed.

  Definition DigitToString (n: {n | n < 10}) :=
    match n with
    | exist 0 _ => "0" | exist 1 _ => "1" | exist 2 _ => "2" | exist 3 _ => "3" | exist 4 _ => "4"
    | exist 5 _ => "5" | exist 6 _ => "6" | exist 7 _ => "7" | exist 8 _ => "8" | exist 9 _ => "9"
    | exist n pr => False_rect _ (digitLtBase 10 pr)
    end.

  Fixpoint NumberToString_rec (fuel: nat) (n: nat) :=
    match fuel with
    | O => ""
    | S fuel =>
      match (lt_dec n 10) with
      | left pr  => DigitToString (exist _ n pr)
      | right pr => NumberToString_rec fuel (n / 10) ++ NumberToString_rec fuel (n mod 10)
      end
    end.

  Definition NumberToString (n: nat) :=
    NumberToString_rec n (pred n).
End GenSym.

Ltac gensym_rec prefix start :=
  let name := (eval compute in (prefix ++ NumberToString start)%string) in
  lazymatch goal with
  | |- context[name] => gensym_rec prefix (S start)
  | H : context[name] |- _ => gensym_rec prefix (S start)
  | H := context[name] |- _ => gensym_rec prefix (S start)
  | _ => constr:(name)
  end.

Ltac gensym prefix :=
  gensym_rec prefix 0.
