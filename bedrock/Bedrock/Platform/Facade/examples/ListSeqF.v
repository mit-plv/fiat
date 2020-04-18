Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Malloc Bedrock.Platform.Facade.examples.SeqF.


Module Type ADT.
  Parameter lseq : list W -> W -> HProp.
  Parameter lseq' : list W -> W -> HProp.

  Axiom lseq_fwd : forall ls c, lseq ls c ===> [| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * lseq' ls p.
  Axiom lseq_bwd : forall ls (c : W), ([| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * lseq' ls p) ===> lseq ls c.

  Axiom lseq'_empty_fwd : forall ls (c : W), c = 0
    -> lseq' ls c
    ===> [| ls = nil |].

  Axiom lseq'_empty_bwd : forall ls (c : W), c = 0
    -> [| ls = nil |] ===> lseq' ls c.

  Axiom lseq'_nonempty_fwd : forall ls (c : W), c <> 0
    -> lseq' ls c
    ===> Ex x, Ex ls', [| ls = x :: ls' |] * [| freeable c 2 |] * Ex p', (c ==*> x, p')
        * lseq' ls' p'.

  Axiom lseq'_nonempty_bwd : forall ls (c : W), c <> 0
    -> (Ex x, Ex ls', [| ls = x :: ls' |] * [| freeable c 2 |] * Ex p', (c ==*> x, p')
        * lseq' ls' p') ===> lseq' ls c.

  Axiom lseq'_cons_fwd : forall x ls (c : W),
    lseq' (x :: ls) c
    ===> [| c <> 0 |] * [| freeable c 2 |] * Ex p', (c ==*> x, p') * lseq' ls p'.
End ADT.

Module Adt : ADT.
  Open Scope Sep_scope.

  Fixpoint lseq' (ls : list W) (p : W) : HProp :=
    match ls with
      | nil => [| p = 0 |]
      | x :: ls' => [| p <> 0 |] * [| freeable p 2 |]
        * Ex p', (p ==*> x, p')
        * lseq' ls' p'
    end.

  Definition lseq (ls : list W) (c : W) : HProp :=
    [| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * lseq' ls p.

  Theorem lseq_fwd : forall ls c, lseq ls c ===> [| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * lseq' ls p.
    unfold lseq; sepLemma.
  Qed.

  Theorem lseq_bwd : forall ls (c : W), ([| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * lseq' ls p) ===> lseq ls c.
    unfold lseq; sepLemma.
  Qed.

  Theorem lseq'_empty_fwd : forall ls (c : W), c = 0
    -> lseq' ls c
    ===> [| ls = nil |].
    destruct ls; sepLemma.
  Qed.

  Theorem lseq'_empty_bwd : forall ls (c : W), c = 0
    -> [| ls = nil |] ===> lseq' ls c.
    destruct ls; sepLemma.
  Qed.

  Theorem lseq'_nonempty_fwd : forall ls (c : W), c <> 0
    -> lseq' ls c
    ===> Ex x, Ex ls', [| ls = x :: ls' |] * [| freeable c 2 |] * Ex p', (c ==*> x, p')
        * lseq' ls' p'.
    destruct ls; sepLemma.
  Qed.

  Theorem lseq'_nonempty_bwd : forall ls (c : W), c <> 0
    -> (Ex x, Ex ls', [| ls = x :: ls' |] * [| freeable c 2 |] * Ex p', (c ==*> x, p')
        * lseq' ls' p') ===> lseq' ls c.
    destruct ls; sepLemma.
    injection H0; sepLemma.
  Qed.

  Theorem lseq'_cons_fwd : forall x ls (c : W),
    lseq' (x :: ls) c
    ===> [| c <> 0 |] * [| freeable c 2 |] * Ex p', (c ==*> x, p') * lseq' ls p'.
    sepLemma.
  Qed.
End Adt.

Import Adt.
Export Adt.

Definition hints : TacPackage.
  prepare (lseq_fwd, lseq'_empty_fwd, lseq'_nonempty_fwd, lseq'_cons_fwd)
  (lseq_bwd, lseq'_empty_bwd, lseq'_nonempty_bwd).
Defined.

Definition newS := newS lseq 8.
Definition deleteS := deleteS lseq 7.
Definition popS := popS lseq 8.
Definition emptyS := emptyS lseq 0.
Definition pushS := pushS lseq 8.
Definition copyS := copyS lseq 10.
Definition revS := revS lseq 2.
Definition lengthS := lengthS lseq 1.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "ListSeq" {{
    bfunction "new"("extra_stack", "x") [newS]
      "x" <-- Call "malloc"!"malloc"(0, 2)
      [PRE[_, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |] * mallocHeap 0
       POST[R'] lseq nil R' * mallocHeap 0];;

      "x" *<- 0;;
      Return "x"
    end

    with bfunction "delete"("extra_stack", "self", "ls") [deleteS]
      "ls" <-* "self";;

      Call "malloc"!"free"(0, "self", 2)
      [Al s,
        PRE[V] lseq' s (V "ls") * mallocHeap 0
        POST[R] [| R = $0 |] * mallocHeap 0];;

      [Al s,
        PRE[V] lseq' s (V "ls") * mallocHeap 0
        POST[R] [| R = $0 |] * mallocHeap 0]
      While ("ls" <> 0) {
        "self" <-* "ls"+4;;
        Call "malloc"!"free"(0, "ls", 2)
        [Al s,
          PRE[V] lseq' s (V "self") * mallocHeap 0
          POST[R] [| R = $0 |] * mallocHeap 0];;

        "ls" <- "self"
      };;

      Return 0
    end

    with bfunction "pop"("extra_stack", "self", "tmp", "r") [popS]
      "tmp" <-* "self";;
      "r" <-* "tmp";;
      "extra_stack" <-* "tmp"+4;;
      "self" *<- "extra_stack";;

      Call "malloc"!"free"(0, "tmp", 2)
      [PRE[V] Emp
       POST[R] [| R = V "r" |] ];;

      Return "r"
    end

    with bfunction "empty"("extra_stack", "self") [emptyS]
      "self" <-* "self";;

      If ("self" = 0) {
        Return 1
      } else {
        Return 0
      }
    end

    with bfunction "push"("extra_stack", "self", "n", "tmp") [pushS]
      "tmp" <-- Call "malloc"!"malloc"(0, 2)
      [Al p,
       PRE[V, R] V "self" =*> p * R =?> 2
       POST[R'] [| R' = $0 |] * V "self" =*> R * (R ==*> V "n", p) ];;

      "tmp" *<- "n";;
      "extra_stack" <-* "self";;
      "tmp"+4 *<- "extra_stack";;
      "self" *<- "tmp";;
      Return 0
    end

    with bfunction "copy"("extra_stack", "self", "new", "acc", "tmp") [copyS]
      "self" <-* "self";;

      "new" <-- Call "malloc"!"malloc"(0, 2)
      [Al ls,
       PRE[V, R] lseq' ls (V "self") * R =?> 1 * mallocHeap 0
       POST[R'] [| R' = R |] * lseq' ls (V "self") * Ex p, R =*> p * lseq' ls p * mallocHeap 0];;
      "acc" <- "new";;

      [Al ls,
       PRE[V] lseq' ls (V "self") * V "acc" =?> 1 * mallocHeap 0
       POST[R] [| R = V "new" |] * lseq' ls (V "self") * Ex p, V "acc" =*> p * lseq' ls p * mallocHeap 0]
      While ("self" <> 0) {
        "tmp" <-* "self";;
        "self" <-* "self"+4;;

        "extra_stack" <-- Call "malloc"!"malloc"(0, 2)
        [Al ls,
         PRE[V, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |]
                 * lseq' ls (V "self") * V "acc" =?> 1 * mallocHeap 0
         POST[R'] [| R' = V "new" |] * lseq' ls (V "self") * Ex p, V "acc" =*> p
                * lseq' (V "tmp" :: ls) p * mallocHeap 0];;

        "acc" *<- "extra_stack";;
        "extra_stack" *<- "tmp";;
        "acc" <- "extra_stack"+4
      };;

      "acc" *<- 0;;
      Return "new"
    end

    with bfunction "length"("extra_stack", "self", "acc") [lengthS]
      "self" <-* "self";;
      "acc" <- 0;;

      [Al ls,
       PRE[V] lseq' ls (V "self")
       POST[R] [| R = V "acc" ^+ $ (length ls) |] * lseq' ls (V "self") ]
      While ("self" <> 0) {
        "acc" <- "acc" + 1;;
        "self" <-* "self"+4
      };;

      Return "acc"
    end with bfunction "rev"("extra_stack", "self", "from", "to") [revS]
      "from" <-* "self";;
      "to" <- 0;;

      [Al ls, Al ls',
       PRE[V] V "self" =?> 1 * lseq' ls (V "from") * lseq' ls' (V "to")
       POST[R] [| R = $0 |] * Ex p, V "self" =*> p * lseq' (rev_append ls ls') p]
      While ("from" <> 0) {
        "extra_stack" <-* "from"+4;;
        "from"+4 *<- "to";;
        "to" <- "from";;
        "from" <- "extra_stack"
      };;

      "self" *<- "to";;
      Return 0
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Theorem ok : moduleOk m.
  vcgen; abstract (sep hints; eauto; try rewrite natToW_S; try rewrite <- rev_alt;
                   eauto; step auto_ext).
Qed.
