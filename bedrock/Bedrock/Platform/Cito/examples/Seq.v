Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Malloc.


Section adt.
  Variable P : list W -> W -> HProp.
  Variable res : nat.

  Definition newS := SPEC("extra_stack", "len") reserving res
    PRE[V] [| goodSize (2 + wordToNat (V "len")) |] * mallocHeap 0
    POST[R] Ex ws, P ws R * [| length ws = wordToNat (V "len") |] * mallocHeap 0.

  Definition deleteS := SPEC("extra_stack", "self") reserving res
    Al ws,
    PRE[V] P ws (V "self") * mallocHeap 0
    POST[_] mallocHeap 0.

  Definition readS := SPEC("extra_stack", "self", "n") reserving res
    Al ws,
    PRE[V] P ws (V "self") * [| V "n" < natToW (length ws) |] * mallocHeap 0
    POST[R] [| R = Array.sel ws (V "n") |] * P ws (V "self") * mallocHeap 0.

  Definition writeS := SPEC("extra_stack", "self", "n", "v") reserving res
    Al ws,
    PRE[V] P ws (V "self") * [| V "n" < natToW (length ws) |] * mallocHeap 0
    POST[_] P (Array.upd ws (V "n") (V "v")) (V "self") * mallocHeap 0.
End adt.
