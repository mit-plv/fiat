Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Malloc.

Require Import Bedrock.Platform.Cito.WordKey.

Require Import Coq.MSets.MSetRBT.
Module WordSet := Make W_as_OT_new.

Section adt.
  Variable P : WordSet.t -> W -> HProp.
  Variable res : nat.

  Definition newS := SPEC("extra_stack") reserving res
    PRE[_] mallocHeap 0
    POST[R] P WordSet.empty R * mallocHeap 0.

  Definition deleteS := SPEC("extra_stack", "self") reserving res
    Al s,
    PRE[V] P s (V "self") * mallocHeap 0
    POST[_] mallocHeap 0.

  Definition memS := SPEC("extra_stack", "self", "n") reserving res
    Al s,
    PRE[V] P s (V "self") * mallocHeap 0
    POST[R] [| R = WordSet.mem (V "n") s |] * P s (V "self") * mallocHeap 0.

  Definition addS := SPEC("extra_stack", "self", "n") reserving res
    Al s,
    PRE[V] P s (V "self") * mallocHeap 0
    POST[_] P (WordSet.add (V "n") s) (V "self") * mallocHeap 0.

  Definition sizeS := SPEC("extra_stack", "self") reserving res
    Al s,
    PRE[V] P s (V "self") * mallocHeap 0
    POST[R] [| R = WordSet.cardinal s |] * P s (V "self") * mallocHeap 0.
End adt.
