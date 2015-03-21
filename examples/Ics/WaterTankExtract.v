Require Import Ics WaterTank.

Module Parameters.
  Definition tankMax := 100.
  Definition sensorAccuracy := 5.

  Theorem sensorAccuracy_positive : 0 <= sensorAccuracy.
  Proof.
    unfold sensorAccuracy; omega.
  Qed.

  Definition fillRate := 3.
  Definition emptyRate := 2.

  Definition minFill := 1.
  Definition maxFill := 3.
  Definition minEmpty := 1.
  Definition maxEmpty := 2.

  Theorem fillBounds : minFill <= maxFill.
  Proof.
    unfold minFill, maxFill; omega.
  Qed.

  Theorem emptyBounds : minEmpty <= maxEmpty.
  Proof.
    unfold minEmpty, maxEmpty; omega.
  Qed.
End Parameters.

Module D := Deterministic(Parameters).
Module N := Nondeterministic(Parameters).

(** Let's take the extra step to OCaml code via extraction. *)

Module Det.
  Import D.

  Definition new : Z -> cRep impl'.
    extractConstructor impl' "new".
  Defined.

  Definition update : cRep impl' -> Z -> cRep impl' * unit.
    extractMethod impl' "update".
  Defined.

  Definition timestep : cRep impl' -> Z -> cRep impl' * action.
    extractMethod impl' "timestep".
  Defined.
End Det.

Module Nondet.
  Import N.

  Definition new : Z -> cRep impl'.
    extractConstructor impl' "new".
  Defined.

  Definition update : cRep impl' -> Z -> cRep impl' * unit.
    extractMethod impl' "update".
  Defined.

  Definition timestep : cRep impl' -> request -> cRep impl' * action.
    extractMethod impl' "timestep".
  Defined.
End Nondet.

Recursive Extraction Det Nondet.
