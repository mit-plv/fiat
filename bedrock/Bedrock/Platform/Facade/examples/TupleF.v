Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep Bedrock.Platform.Malloc.

Section adt.
  Variable P : list W -> W -> HProp.
  Variable res : nat.

  Definition newS := SPEC("extra_stack", "len") reserving res
    PRE[V] [| V "len" >= $2 |] * mallocHeap 0
    POST[R] Ex ls, P ls R * [| length ls = wordToNat (V "len") |] * mallocHeap 0.

  Definition deleteS := SPEC("extra_stack", "self", "len") reserving res
    Al ls,
    PRE[V] P ls (V "self") * [| length ls = wordToNat (V "len") |] * mallocHeap 0
    POST[R] [| R = $0 |] * mallocHeap 0.

  Definition copyS := SPEC("extra_stack", "self", "len") reserving res
    Al ls,
    PRE[V] P ls (V "self") * [| length ls = wordToNat (V "len") |] * [| $2 <= V "len" |] * mallocHeap 0
    POST[R] P ls (V "self") * P ls R * mallocHeap 0.

  Definition getS := SPEC("extra_stack", "self", "pos") reserving res
    Al ls,
    PRE[V] P ls (V "self") * [| V "pos" < natToW (length ls) |] * mallocHeap 0
    POST[R] [| R = Array.sel ls (V "pos") |] * P ls (V "self") * mallocHeap 0.

  Definition setS := SPEC("extra_stack", "self", "pos", "val") reserving res
    Al ls,
    PRE[V] P ls (V "self") * [| V "pos" < natToW (length ls) |] * mallocHeap 0
    POST[R] [| R = $0 |] * P (Array.upd ls (V "pos") (V "val")) (V "self") * mallocHeap 0.
End adt.
