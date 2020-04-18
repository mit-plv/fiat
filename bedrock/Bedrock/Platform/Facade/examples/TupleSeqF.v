Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep Bedrock.Platform.Malloc.

Require Import Bedrock.Platform.Facade.examples.TuplesF.

Section adt.
  Variable tuple : list W -> W -> HProp.
  Variable P : list (list W) -> W -> HProp.
  Variable res : nat.

  Definition newS := SPEC("extra_stack") reserving res
    PRE[_] mallocHeap 0
    POST[R] P nil R * mallocHeap 0.

  Definition deleteS := SPEC("extra_stack", "self") reserving res
    PRE[V] P nil (V "self") * mallocHeap 0
    POST[R] [| R = $0 |] * mallocHeap 0.

  Definition copyS := SPEC("extra_stack", "self", "len") reserving res
    Al ls,
    PRE[V] P ls (V "self") * [| allTuplesLen (wordToNat (V "len")) ls |] * [| $2 <= V "len" |] * mallocHeap 0
    POST[R] P ls (V "self") * P ls R * mallocHeap 0.

  Definition copyAppendS := SPEC("extra_stack", "self", "other", "len") reserving res
    Al ls1, Al ls2,
    PRE[V] P ls1 (V "self") * P ls2 (V "other") * [| $2 <= V "len" |] * mallocHeap 0
      * [| allTuplesLen (wordToNat (V "len")) ls1 |]
    POST[R] [| R = $0 |] * P ls1 (V "self") * P (ls1 ++ ls2) (V "other") * mallocHeap 0.

  Definition popS := SPEC("extra_stack", "self") reserving res
    Al x, Al ls,
    PRE[V] P (x :: ls) (V "self") * mallocHeap 0
    POST[R] tuple x R * P ls (V "self") * mallocHeap 0.

  Definition emptyS := SPEC("extra_stack", "self") reserving res
    Al ls,
    PRE[V] P ls (V "self") * mallocHeap 0
    POST[R] [| (ls = nil) \is R |] * P ls (V "self") * mallocHeap 0.

  Definition pushS := SPEC("extra_stack", "self", "tup") reserving res
    Al ls, Al tup,
    PRE[V] P ls (V "self") * tuple tup (V "tup") * mallocHeap 0
    POST[R] [| R = $0 |] * P (tup :: ls) (V "self") * mallocHeap 0.

  Definition revS := SPEC("extra_stack", "self") reserving res
    Al ls,
    PRE[V] P ls (V "self") * mallocHeap 0
    POST[R] [| R = $0 |] * P (rev ls) (V "self") * mallocHeap 0.

  Definition lengthS := SPEC("extra_stack", "self") reserving res
    Al ls,
    PRE[V] P ls (V "self") * mallocHeap 0
    POST[R] [| R = $ (length ls) |] * P ls (V "self") * mallocHeap 0.
End adt.

Lemma allTuplesLen_first : forall A len t ts,
  allTuplesLen (A := A) len (t :: ts)
  -> length t = len.
Proof.
  simpl; tauto.
Qed.

Lemma allTuplesLen_rest : forall A len t ts,
  allTuplesLen (A := A) len (t :: ts)
  -> allTuplesLen len ts.
Proof.
  simpl; tauto.
Qed.

Hint Immediate allTuplesLen_first allTuplesLen_rest.
