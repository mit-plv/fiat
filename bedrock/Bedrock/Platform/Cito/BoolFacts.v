Require Import Eqdep_dec.
Require Import Bool.

Module BoolDT <: DecidableType.
  Definition U := bool.
  Definition eq_dec := bool_dec.
End BoolDT.

Module Import BoolDED := DecidableEqDep BoolDT.

Lemma bool_irre (a b : bool) (H1 H2 : a = b) : H1 = H2.
Proof.
  eapply UIP.
Qed.

Require Import Sumbool.

Definition boolcase := sumbool_of_bool.
