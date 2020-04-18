Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep Bedrock.Platform.Malloc.
Require Import Bedrock.Platform.Facade.examples.FiatADTs.

Infix "===" := (@Same_set W).

Definition empty := Empty_set W.
Notation "%0" := empty.

(* Who knows why this wrapper is necessary to keep the tactics happy.... *)
Module Type HAS.
  Parameter has : Ensemble W -> W -> Prop.
  Axiom has_eq : has = Ensembles.In _.
End HAS.

Module Has : HAS.
  Definition has := Ensembles.In W.
  Theorem has_eq : has = Ensembles.In _.
    auto.
  Qed.
End Has.

Import Has.
Export Has.

Infix "%has" := has (at level 70).

Definition add := Ensembles.Add W.
Infix "%+" := add (at level 50).

Definition sub := Subtract W.
Infix "%-" := sub (at level 50).

Section adt.
  Variable P : Ensemble W -> W -> HProp.
  Variable res : nat.

  Definition newS := SPEC("extra_stack") reserving res
    PRE[_] mallocHeap 0
    POST[R] P %0 R * mallocHeap 0.

  Definition deleteS := SPEC("extra_stack", "self") reserving res
    Al s,
    PRE[V] P s (V "self") * mallocHeap 0
    POST[R] [| R = $0 |] * mallocHeap 0.

  Definition memS := SPEC("extra_stack", "self", "n") reserving res
    Al s,
    PRE[V] P s (V "self") * mallocHeap 0
    POST[R] [| s %has V "n" \is R |] * P s (V "self") * mallocHeap 0.

  Definition addS := SPEC("extra_stack", "self", "n") reserving res
    Al s,
    PRE[V] P s (V "self") * mallocHeap 0
    POST[R] [| R = $0 |] * P (s %+ V "n") (V "self") * mallocHeap 0.

  Definition removeS := SPEC("extra_stack", "self", "n") reserving res
    Al s,
    PRE[V] P s (V "self") * mallocHeap 0
    POST[R] [| R = $0 |] * P (s %- V "n") (V "self") * mallocHeap 0.

  Definition cardinal_is (s : Ensemble W) (R : W) :=
    exists n, cardinal _ s n /\ R = natToWord _ n.

  Definition sizeS := SPEC("extra_stack", "self") reserving res
    Al s,
    PRE[V] P s (V "self") * mallocHeap 0
    POST[R] [| cardinal_is s R |] * P s (V "self") * mallocHeap 0.
End adt.
