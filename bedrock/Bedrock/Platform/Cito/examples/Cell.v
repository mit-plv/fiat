Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Malloc.


Section adt.
  Variable P : W -> W -> HProp.
  Variable res : nat.

  Definition newS := SPEC("extra_stack") reserving res
    PRE[_] mallocHeap 0
    POST[R] P 0 R * mallocHeap 0.

  Definition deleteS := SPEC("extra_stack", "self") reserving res
    Al c,
    PRE[V] P c (V "self") * mallocHeap 0
    POST[_] mallocHeap 0.

  Definition readS := SPEC("extra_stack", "self") reserving res
    Al c,
    PRE[V] P c (V "self") * mallocHeap 0
    POST[R] [| R = c |] * P c (V "self") * mallocHeap 0.

  Definition writeS := SPEC("extra_stack", "self", "n") reserving res
    Al c,
    PRE[V] P c (V "self") * mallocHeap 0
    POST[_] P (V "n") (V "self") * mallocHeap 0.
End adt.
