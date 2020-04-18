Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep Bedrock.Platform.Malloc.

Section adt.
  Variable P : list W -> W -> HProp.
  Variable res : nat.

  Definition newS := SPEC("extra_stack") reserving res
    PRE[_] mallocHeap 0
    POST[R] P nil R * mallocHeap 0.

  Definition deleteS := SPEC("extra_stack", "self") reserving res
    Al ls,
    PRE[V] P ls (V "self") * mallocHeap 0
    POST[R] [| R = $0 |] * mallocHeap 0.

  Definition popS := SPEC("extra_stack", "self") reserving res
    Al x, Al ls,
    PRE[V] P (x :: ls) (V "self") * mallocHeap 0
    POST[R] [| R = x |] * P ls (V "self") * mallocHeap 0.

  Definition emptyS := SPEC("extra_stack", "self") reserving res
    Al ls,
    PRE[V] P ls (V "self") * mallocHeap 0
    POST[R] [| (ls = nil) \is R |] * P ls (V "self") * mallocHeap 0.

  Definition pushS := SPEC("extra_stack", "self", "n") reserving res
    Al ls,
    PRE[V] P ls (V "self") * mallocHeap 0
    POST[R] [| R = $0 |] * P (V "n" :: ls) (V "self") * mallocHeap 0.

  Definition copyS := SPEC("extra_stack", "self") reserving res
    Al ls,
    PRE[V] P ls (V "self") * mallocHeap 0
    POST[R] P ls (V "self") * P ls R * mallocHeap 0.

  Definition revS := SPEC("extra_stack", "self") reserving res
    Al ls,
    PRE[V] P ls (V "self") * mallocHeap 0
    POST[R] [| R = $0 |] * P (rev ls) (V "self") * mallocHeap 0.

  Definition lengthS := SPEC("extra_stack", "self") reserving res
    Al ls,
    PRE[V] P ls (V "self") * mallocHeap 0
    POST[R] [| R = $ (length ls) |] * P ls (V "self") * mallocHeap 0.
End adt.
