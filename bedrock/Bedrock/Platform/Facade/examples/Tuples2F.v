Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Facade.examples.TupleF Bedrock.Platform.Facade.examples.ArrayTupleF.
Require Import Bedrock.Platform.Malloc Bedrock.Platform.Facade.examples.TupleSeqF.
Require Import Bedrock.Platform.Facade.examples.TupleListF Bedrock.Platform.Facade.examples.TuplesF.
Require Import Bedrock.Platform.Facade.examples.Tuples1F.


Module Type ADT.
  Parameter tuples2 : W -> W -> W -> tuples -> W -> HProp.
  Parameter tree : W -> W -> W -> skel -> tuples -> W -> HProp.

  Axiom tuples2_fwd : forall len key1 key2 ts c, tuples2 len key1 key2 ts c
    ===> [| c <> 0 |] * [| freeable c 4 |] * [| $2 <= len |]
        * Ex p, Ex sk, (c ==*> len, key1, key2, p) * tree len key1 key2 sk ts p
        * [| key1 < len |] * [| key2 < len |].
  Axiom tuples2_bwd : forall len key1 key2 ts (c : W),
    ([| c <> 0 |] * [| freeable c 4 |] * [| $2 <= len |]
    * Ex p, Ex sk, (c ==*> len, key1, key2, p) * tree len key1 key2 sk ts p
    * [| key1 < len |] * [| key2 < len |])
    ===> tuples2 len key1 key2 ts c.

  (* Sometimes this version is necessary to integrate well with the automation. *)
  Axiom tuples2_eq : forall len key1 key2 ts c, tuples2 len key1 key2 ts c
    = ([| c <> 0 |] * [| freeable c 4 |] * [| $2 <= len |]
        * Ex p, Ex sk, (c ==*> len, key1, key2, p) * tree len key1 key2 sk ts p
        * [| key1 < len |]* [| key2 < len |])%Sep.

  Axiom tree_Equiv : forall len key1 key2 sk ts1 ts2 p,
    Equiv ts1 ts2
    -> tree len key1 key2 sk ts1 p ===> tree len key1 key2 sk ts2 p.

  Axiom tree_leaf_fwd : forall len key1 key2 sk ts (p : W), p = 0
    -> tree len key1 key2 sk ts p ===> [| sk = Leaf |] * [| empty ts |].

  Axiom tree_leaf_bwd : forall len key1 key2 sk ts (p : W), p = 0
    -> [| sk = Leaf |] * [| empty ts |] ===> tree len key1 key2 sk ts p.

  Axiom tree_node_fwd : forall len key1 key2 sk ts (p : W), p <> 0
    -> tree len key1 key2 sk ts p ===> Ex sk1, Ex sk2, Ex p1, Ex k, Ex t0, Ex p2,
        [| sk = Node sk1 sk2 |]
        * (p ==*> p1, k, t0, p2)
        * tree len key1 key2 sk1 (keepLt ts key1 k) p1
        * tuples1 len key2 (keepEq ts key1 k) t0
        * tree len key1 key2 sk2 (keepGt ts key1 k) p2.

  Axiom tree_node_bwd : forall len key1 key2 sk ts (p : W), p <> 0
    -> (Ex sk1, Ex sk2, Ex p1, Ex k, Ex t0, Ex p2, [| sk = Node sk1 sk2 |]
        * (p ==*> p1, k, t0, p2)
        * tree len key1 key2 sk1 (keepLt ts key1 k) p1
        * tuples1 len key2 (keepEq ts key1 k) t0
        * tree len key1 key2 sk2 (keepGt ts key1 k) p2) ===> tree len key1 key2 sk ts p.


  Parameter stack : W -> W -> W -> list (tuples * W) -> W -> HProp.
  (* This last one is used as we walk a tree in full to enumerate. *)

  Axiom stack_nil_fwd : forall len key1 key2 tss (p : W), p = 0
    -> stack len key1 key2 tss p ===> [| tss = nil |].

  Axiom stack_nil_bwd : forall len key1 key2 tss (p : W), p = 0
    -> [| tss = nil |] ===> stack len key1 key2 tss p.

  Axiom stack_cons_fwd : forall len key1 key2 tss (p : W), p <> 0
    -> stack len key1 key2 tss p ===> Ex ts, Ex tp, Ex tss', [| tss = (ts, tp) :: tss' |] * [| freeable p 2 |]
      * [| functional ts |]
      * Ex sk, Ex p', (p ==*> tp, p') * tree len key1 key2 sk ts tp * stack len key1 key2 tss' p'.

  Axiom stack_cons_bwd : forall len key1 key2 tss (p : W), p <> 0
    -> (Ex ts, Ex tp, Ex tss', [| tss = (ts, tp) :: tss' |] * [| freeable p 2 |] * [| functional ts |]
      * Ex sk, Ex p', (p ==*> tp, p') * tree len key1 key2 sk ts tp * stack len key1 key2 tss' p')
      ===> stack len key1 key2 tss p.
End ADT.

Module Adt : ADT.
  Open Scope Sep_scope.

  Fixpoint tree (len key1 key2 : W) (sk : skel) (ts : tuples) (p : W) : HProp :=
    match sk with
    | Leaf => [| p = 0 |] * [| empty ts |]
    | Node sk1 sk2 => [| p <> 0 |]
      * Ex p1, Ex k, Ex t0, Ex p2, (p ==*> p1, k, t0, p2)
        * tree len key1 key2 sk1 (keepLt ts key1 k) p1
        * tuples1 len key2 (keepEq ts key1 k) t0
        * tree len key1 key2 sk2 (keepGt ts key1 k) p2
    end.

  Fixpoint stack (len key1 key2 : W) (tss : list (tuples * W)) (p : W) : HProp :=
    match tss with
    | nil => [| p = 0 |]
    | (ts, tp) :: tss' => [| p <> 0 |] * [| freeable p 2 |] * [| functional ts |] * Ex sk, Ex p', (p ==*> tp, p')
                    * tree len key1 key2 sk ts tp * stack len key1 key2 tss' p'
    end.

  Definition tuples2 (len key1 key2 : W) (ts : tuples) (c : W) : HProp :=
    [| c <> 0 |] * [| freeable c 4 |] * [| $2 <= len |]
    * Ex p, Ex sk, (c ==*> len, key1, key2, p) * tree len key1 key2 sk ts p
    * [| key1 < len |] * [| key2 < len |].

  Theorem stack_nil_fwd : forall len key1 key2 tss (p : W), p = 0
    -> stack len key1 key2 tss p ===> [| tss = nil |].
  Proof.
    destruct tss as [ ? | [ ] ]; sepLemma.
  Qed.

  Theorem stack_nil_bwd : forall len key1 key2 tss (p : W), p = 0
    -> [| tss = nil |] ===> stack len key1 key2 tss p.
  Proof.
    destruct tss as [ ? | [ ] ]; sepLemma.
  Qed.

  Theorem stack_cons_fwd : forall len key1 key2 tss (p : W), p <> 0
    -> stack len key1 key2 tss p ===> Ex ts, Ex tp, Ex tss', [| tss = (ts, tp) :: tss' |] * [| freeable p 2 |]
      * [| functional ts |]
      * Ex sk, Ex p', (p ==*> tp, p') * tree len key1 key2 sk ts tp * stack len key1 key2 tss' p'.
  Proof.
    destruct tss as [ ? | [ ] ]; sepLemma.
  Qed.

  Theorem stack_cons_bwd : forall len key1 key2 tss (p : W), p <> 0
    -> (Ex ts, Ex tp, Ex tss', [| tss = (ts, tp) :: tss' |] * [| freeable p 2 |] * [| functional ts |]
      * Ex sk, Ex p', (p ==*> tp, p') * tree len key1 key2 sk ts tp * stack len key1 key2 tss' p')
      ===> stack len key1 key2 tss p.
  Proof.
    destruct tss as [ ? | [ ] ]; sepLemma.
    injection H0; sepLemma; auto.
    injection H0; sepLemma.
  Qed.

  Theorem tuples2_fwd : forall len key1 key2 ts c, tuples2 len key1 key2 ts c
    ===> [| c <> 0 |] * [| freeable c 4 |] * [| $2 <= len |]
    * Ex p, Ex sk, (c ==*> len, key1, key2, p) * tree len key1 key2 sk ts p
    * [| key1 < len |] * [| key2 < len |].
  Proof.
    unfold tuples2; sepLemma; eauto.
  Qed.

  Theorem tuples2_bwd : forall len key1 key2 ts (c : W),
    ([| c <> 0 |] * [| freeable c 4 |] * [| $2 <= len |]
     * Ex p, Ex sk, (c ==*> len, key1, key2, p) * tree len key1 key2 sk ts p
     * [| key1 < len |] * [| key2 < len |])
    ===> tuples2 len key1 key2 ts c.
  Proof.
    unfold tuples2; sepLemma; eauto.
  Qed.

  Theorem tuples2_eq : forall len key1 key2 ts c, tuples2 len key1 key2 ts c
    = ([| c <> 0 |] * [| freeable c 4 |] * [| $2 <= len |]
        * Ex p, Ex sk, (c ==*> len, key1, key2, p) * tree len key1 key2 sk ts p
        * [| key1 < len |] * [| key2 < len |])%Sep.
  Proof.
    auto.
  Qed.

  Theorem tree_Equiv : forall len key1 key2 sk ts1 ts2 p,
    Equiv ts1 ts2
    -> tree len key1 key2 sk ts1 p ===> tree len key1 key2 sk ts2 p.
  Proof.
    induction sk; sepLemma.

    Equiv.

    repeat apply himp_star_frame; eauto.
    eapply tuples1_Equiv; eauto.
  Qed.

  Theorem tree_leaf_fwd : forall len key1 key2 sk ts (p : W), p = 0
    -> tree len key1 key2 sk ts p ===> [| sk = Leaf |] * [| empty ts |].
  Proof.
    destruct sk; sepLemma.
  Qed.

  Theorem tree_leaf_bwd : forall len key1 key2 sk ts (p : W), p = 0
    -> [| sk = Leaf |] * [| empty ts |] ===> tree len key1 key2 sk ts p.
  Proof.
    destruct sk; sepLemma.
  Qed.

  Theorem tree_node_fwd : forall len key1 key2 sk ts (p : W), p <> 0
    -> tree len key1 key2 sk ts p ===> Ex sk1, Ex sk2, Ex p1, Ex k, Ex t0, Ex p2,
        [| sk = Node sk1 sk2 |]
        * (p ==*> p1, k, t0, p2)
        * tree len key1 key2 sk1 (keepLt ts key1 k) p1
        * tuples1 len key2 (keepEq ts key1 k) t0
        * tree len key1 key2 sk2 (keepGt ts key1 k) p2.
  Proof.
    destruct sk; sepLemma.
  Qed.

  Theorem tree_node_bwd : forall len key1 key2 sk ts (p : W), p <> 0
    -> (Ex sk1, Ex sk2, Ex p1, Ex k, Ex t0, Ex p2, [| sk = Node sk1 sk2 |]
        * (p ==*> p1, k, t0, p2)
        * tree len key1 key2 sk1 (keepLt ts key1 k) p1
        * tuples1 len key2 (keepEq ts key1 k) t0
        * tree len key1 key2 sk2 (keepGt ts key1 k) p2) ===> tree len key1 key2 sk ts p.
  Proof.
    destruct sk; sepLemma.
    injection H0; sepLemma.
  Qed.
End Adt.

Import Adt.
Export Adt.

Definition hints : TacPackage.
  prepare (tuples2_fwd, tree_leaf_fwd, tree_node_fwd, stack_nil_fwd, stack_cons_fwd)
          (tuples2_bwd, tree_leaf_bwd, tree_node_bwd, stack_nil_bwd, stack_cons_bwd).
Defined.

(* Also, we want a way to indicate that the trees in a stack are intact, even though the stack has been freed. *)
Fixpoint stacktrees (len key1 key2 : W) (tss : list (tuples * W)) : HProp :=
  match tss with
  | nil => Emp
  | (ts, tp) :: tss' => (Ex sk, tree len key1 key2 sk ts tp) * stacktrees len key1 key2 tss'
  end%Sep.

Definition newS := SPEC("extra_stack", "len", "key1", "key2") reserving 7
  PRE[V] [| V "len" >= $2 |] * [| V "key1" < V "len" |]  * [| V "key2" < V "len" |] * mallocHeap 0
  POST[R] tuples2 (V "len") (V "key1") (V "key2") Empty R * mallocHeap 0.

Definition insertS := SPEC("extra_stack", "self", "tup") reserving 31
  Al len, Al key1, Al key2, Al ts, Al t, Al ts',
  PRE[V] tuples2 len key1 key2 ts (V "self") * tuple t (V "tup") * [| length t = wordToNat len |] * mallocHeap 0
         * [| insert ts t ts' |]
  POST[R] [| R = $0 |] * tuples2 len key1 key2 ts' (V "self") * mallocHeap 0.

Definition findBothS := SPEC("extra_stack", "self", "k1", "k2") reserving 38
  Al len, Al key1, Al key2, Al ts,
  PRE[V] tuples2 len key1 key2 ts (V "self") * mallocHeap 0
  POST[R] tuples2 len key1 key2 ts (V "self") * Ex ls, lseq ls R * mallocHeap 0
        * [| EnsembleIndexedListEquivalence (keepEq (keepEq ts key1 (V "k1")) key2 (V "k2")) ls |].

Definition findFirstS := SPEC("extra_stack", "self", "k1") reserving 37
  Al len, Al key1, Al key2, Al ts,
  PRE[V] tuples2 len key1 key2 ts (V "self") * [| functional ts |] * mallocHeap 0
  POST[R] tuples2 len key1 key2 ts (V "self") * Ex ls, lseq ls R * mallocHeap 0
        * [| EnsembleIndexedListEquivalence (keepEq ts key1 (V "k1")) ls |].

Definition enumerateS := SPEC("extra_stack", "self") reserving 36
  Al len, Al key1, Al key2, Al ts,
  PRE[V] tuples2 len key1 key2 ts (V "self") * [| functional ts |] * mallocHeap 0
  POST[R] tuples2 len key1 key2 ts (V "self") * Ex ls, lseq ls R * mallocHeap 0
        * [| EnsembleIndexedListEquivalence ts ls |].

Definition findSecondS := SPEC("extra_stack", "self", "k2") reserving 36
  Al len, Al key1, Al key2, Al ts,
  PRE[V] tuples2 len key1 key2 ts (V "self") * [| functional ts |] * mallocHeap 0
  POST[R] tuples2 len key1 key2 ts (V "self") * Ex ls, lseq ls R * mallocHeap 0
        * [| EnsembleIndexedListEquivalence (keepEq ts key2 (V "k2")) ls |].

Fixpoint multiEquivalenceEq (key k : W) (tss : list (tuples * W)) (ls : list tupl) : Prop :=
  match tss with
  | nil => ls = nil
  | (ts, _) :: tss' => exists ls1 ls2, EnsembleIndexedListEquivalence (keepEq ts key k) ls1
                                       /\ multiEquivalenceEq key k tss' ls2
                                       /\ ls = ls2 ++ ls1
  end.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "ArrayTuple"!"get" @ [ArrayTupleF.getS], "TupleList"!"new" @ [TupleListF.newS],
                           "Tuples1"!"new" @ [Tuples1F.newS], "Tuples1"!"insert" @ [Tuples1F.insertS],
                           "Tuples1"!"find" @ [Tuples1F.findS], "Tuples1"!"findInto" @ [Tuples1F.findIntoS],
                           "Tuples1"!"enumerate" @ [Tuples1F.enumerateS], "Tuples1"!"enumerateInto" @ [Tuples1F.enumerateIntoS] ]]
  bmodule "Tuples2" {{
    bfunction "new"("extra_stack", "len", "key1", "key2") [newS]
      "extra_stack" <-- Call "malloc"!"malloc"(0, 4)
      [PRE[V, R] R =?> 4 * [| R <> 0 |] * [| freeable R 4 |]
              * [| (V "len" >= $2)%word |] * [| (V "key1" < V "len")%word |] * [| (V "key2" < V "len")%word |]
       POST[R'] tuples2 (V "len") (V "key1") (V "key2") Empty R'];;

      "extra_stack" *<- "len";;
      "extra_stack" + 4 *<- "key1";;
      "extra_stack" + 8 *<- "key2";;
      "extra_stack" + 12 *<- 0;;
      Return "extra_stack"
    end

    with bfunction "insert"("extra_stack", "self", "tup", "len", "key1", "key2", "p", "k1", "k2") [insertS]
      "len" <-* "self";;
      "key1" <-* "self" + 4;;
      "key2" <-* "self" + 8;;
      "self" <- "self" + 12;;
      "p" <-* "self";;
      "k1" <-- Call "ArrayTuple"!"get"("extra_stack", "tup", "key1")
      [Al ts, Al t, Al ts', Al sk,
       PRE[V, R] V "self" =*> V "p" * tree (V "len") (V "key1") (V "key2") sk ts (V "p") * tuple t (V "tup")
         * [| length t = wordToNat (V "len") |] * [| (V "key1" < V "len")%word |]
         * [| (V "key2" < V "len")%word |] * mallocHeap 0
         * [| R = Array.sel t (V "key1") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R'] [| R' = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key1") (V "key2") sk' ts' p * mallocHeap 0];;

      [Al ts, Al t, Al ts', Al sk,
       PRE[V] V "self" =*> V "p" * tree (V "len") (V "key1") (V "key2") sk ts (V "p") * tuple t (V "tup")
         * [| length t = wordToNat (V "len") |] * [| (V "key1" < V "len")%word |]
         * [| (V "key2" < V "len")%word |] * mallocHeap 0
         * [| V "k1" = Array.sel t (V "key1") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R] [| R = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key1") (V "key2") sk' ts' p * mallocHeap 0]
      While ("p" <> 0) {
        "k2" <-* "p" + 4;;

        If ("k1" = "k2") {
          (* Found existing node for this key.  Add to its collection. *)
          "k2" <-* "p" + 8;;
          Call "Tuples1"!"insert"("extra_stack", "k2", "tup")
          [PRE[_] Emp
           POST[R] [| R = $0 |] ];;
          Return 0
        } else {
          (* No match.  Proceed to appropriate subtree. *)
          If ("k1" < "k2") {
            "self" <- "p"
          } else {
            "self" <- "p" + 12
          };;
          "p" <-* "self"
        }
      };;

      (* This key hasn't been added yet.  Create a new tree node for it. *)
      "k2" <-- Call "Tuples1"!"new"("extra_stack", "len", "key2")
      [Al ts, Al t, Al ts',
       PRE[V, R] tuples1 (V "len") (V "key2") Empty R * [| empty ts |]
         * V "self" =*> V "p" * tuple t (V "tup")
         * [| length t = wordToNat (V "len") |] * [| (V "key1" < V "len")%word |]
         * [| (V "key2" < V "len")%word |] * mallocHeap 0
         * [| V "k1" = Array.sel t (V "key1") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R'] [| R' = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key1") (V "key2") sk' ts' p * mallocHeap 0];;

      Call "Tuples1"!"insert"("extra_stack", "k2", "tup")
      [Al ts, Al t, Al ts',
       PRE[V] tuples1 (V "len") (V "key2") ts' (V "k2") * [| empty ts |]
         * V "self" =*> V "p"
         * [| length t = wordToNat (V "len") |] * [| (V "key1" < V "len")%word |]
         * [| (V "key2" < V "len")%word |] * mallocHeap 0
         * [| V "k1" = Array.sel t (V "key1") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R] [| R = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key1") (V "key2") sk' ts' p * mallocHeap 0];;

      "p" <-- Call "malloc"!"malloc"(0, 4)
      [Al ts, Al t, Al ts',
       PRE[V, R] R =?> 4 * [| R <> 0 |] * [| empty ts |]
         * tuples1 (V "len") (V "key2") ts' (V "k2")
         * V "self" =*> V "p"
         * [| length t = wordToNat (V "len") |] * [| (V "key1" < V "len")%word |]
         * [| (V "key2" < V "len")%word |] * mallocHeap 0
         * [| V "k1" = Array.sel t (V "key1") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R] [| R = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key1") (V "key2") sk' ts' p * mallocHeap 0];;

      "p" *<- 0;;
      "p" + 4 *<- "k1";;
      "p" + 8 *<- "k2";;
      "p" + 12 *<- 0;;
      "self" *<- "p";;
      Return 0
    end

    with bfunction "findBoth"("extra_stack", "self", "k1", "k2") [findBothS]
      "self" <-* "self" + 12;;

      [Al len, Al key1, Al key2, Al sk, Al ts,
       PRE[V] tree len key1 key2 sk ts (V "self") * mallocHeap 0
       POST[R] tree len key1 key2 sk ts (V "self") * Ex ls, lseq ls R * mallocHeap 0
             * [| EnsembleIndexedListEquivalence (keepEq (keepEq ts key1 (V "k1")) key2 (V "k2")) ls |] ]
      While ("self" <> 0) {
        "extra_stack" <-* "self" + 4;;

        If ("extra_stack" = "k1") {
          (* Found existing node for this key.  Delegate to the nested data structure found here. *)
          "extra_stack" <-* "self" + 8;;
          "self" <-- Call "Tuples1"!"find"("extra_stack", "extra_stack", "k2")
          [PRE[_, R] Emp
           POST[R'] [| R' = R |] ];;
          Return "self"
        } else {
          (* No match.  Proceed to appropriate subtree. *)
          If ("k1" < "extra_stack") {
            "self" <-* "self"
          } else {
            "self" <-* "self" + 12
          }
        }
      };;

      (* No match.  Prepare a new empty list to return. *)
      "self" <-- Call "TupleList"!"new"("extra_stack")
      [PRE[_, R] Emp
       POST[R'] [| R' = R |] ];;
      Return "self"
    end

    with bfunction "findFirst"("extra_stack", "self", "k1") [findFirstS]
      "self" <-* "self" + 12;;

      [Al len, Al key1, Al key2, Al sk, Al ts,
       PRE[V] tree len key1 key2 sk ts (V "self") * [| functional ts |] * mallocHeap 0
       POST[R] tree len key1 key2 sk ts (V "self") * Ex ls, lseq ls R * mallocHeap 0
             * [| EnsembleIndexedListEquivalence (keepEq ts key1 (V "k1")) ls |] ]
      While ("self" <> 0) {
        "extra_stack" <-* "self" + 4;;

        If ("extra_stack" = "k1") {
          (* Found existing node for this key.  Delegate to the nested data structure found here. *)
          "extra_stack" <-* "self" + 8;;
          "self" <-- Call "Tuples1"!"enumerate"("extra_stack", "extra_stack")
          [PRE[_, R] Emp
           POST[R'] [| R' = R |] ];;
          Return "self"
        } else {
          (* No match.  Proceed to appropriate subtree. *)
          If ("k1" < "extra_stack") {
            "self" <-* "self"
          } else {
            "self" <-* "self" + 12
          }
        }
      };;

      (* No match.  Prepare a new empty list to return. *)
      "self" <-- Call "TupleList"!"new"("extra_stack")
      [PRE[_, R] Emp
       POST[R'] [| R' = R |] ];;
      Return "self"
    end

    with bfunction "enumerate"("extra_stack", "self", "ls", "stack", "tmp") [enumerateS]
      "self" <-* "self" + 12;;
      "ls" <-- Call "TupleList"!"new"("extra_stack")
      [Al len, Al key1, Al key2, Al sk, Al ts,
       PRE[V, R] lseq nil R * tree len key1 key2 sk ts (V "self") * [| functional ts |] * mallocHeap 0
       POST[R'] Ex sk', tree len key1 key2 sk' ts (V "self") * Ex ls, lseq ls R' * mallocHeap 0
             * [| EnsembleIndexedListEquivalence ts ls |] ];;

      "stack" <-- Call "malloc"!"malloc"(0, 2)
      [Al len, Al key1, Al key2, Al sk, Al ts,
       PRE[V, R] R =?> 2 * [| R <> $0 |] * [| freeable R 2 |] * [| functional ts |]
               * tree len key1 key2 sk ts (V "self") * lseq nil (V "ls") * mallocHeap 0
       POST[R'] Ex sk', tree len key1 key2 sk' ts (V "self")
             * Ex ls, lseq ls R' * mallocHeap 0
             * [| EnsembleIndexedListEquivalence ts ls |]];;

      "stack" *<- "self";;
      "stack" + 4 *<- 0;;

      [Al len, Al key1, Al key2, Al tss, Al ls,
       PRE[V, R] stack len key1 key2 tss (V "stack") * lseq ls (V "ls") * mallocHeap 0
       POST[R'] stacktrees len key1 key2 tss
             * Ex ls', lseq (ls' ++ ls) R' * mallocHeap 0
             * [| multiEquivalence tss ls' |] ]
      While ("stack" <> 0) {
        "self" <-* "stack";;
        "tmp" <-* "stack" + 4;;

        Call "malloc"!"free"(0, "stack", 2)
        [Al len, Al key1, Al key2, Al tss, Al ls, Al sk, Al tp, Al ts,
         PRE[V, R] stack len key1 key2 tss (V "tmp") * tree len key1 key2 sk ts (V "self")
                 * lseq ls (V "ls") * mallocHeap 0 * [| functional ts |]
         POST[R'] Ex sk', stacktrees len key1 key2 tss * tree len key1 key2 sk' ts (V "self")
                * Ex ls', lseq (ls' ++ ls) R' * mallocHeap 0
                * [| multiEquivalence ((ts, tp) :: tss) ls' |]];;

        "stack" <- "tmp";;

        If ("self" = 0) {
          Skip
        } else {
          "tmp" <-* "self" + 8;;
          Call "Tuples1"!"enumerateInto"("extra_stack", "tmp", "ls")
          [Al len, Al key1, Al key2, Al tss, Al ls, Al p1, Al sk1, Al ts1, Al p2, Al sk2, Al ts2,
           PRE[V] stack len key1 key2 tss (V "stack")
             * V "self" =*> p1 * tree len key1 key2 sk1 ts1 p1 * [| functional ts1 |]
             * (V "self" ^+ $12) =*> p2 * tree len key1 key2 sk2 ts2 p2 * [| functional ts2 |]
             * lseq ls (V "ls") * mallocHeap 0
           POST[R] stacktrees len key1 key2 tss
             * Ex sk1', V "self" =*> p1 * tree len key1 key2 sk1' ts1 p1
             * Ex sk2', (V "self" ^+ $12) =*> p2 * tree len key1 key2 sk2' ts2 p2
             * Ex ls', lseq (ls' ++ ls) R * mallocHeap 0
             * [| multiEquivalence ((ts2, p1) :: (ts1, p2) :: tss) ls' |]];;

          "tmp" <-- Call "malloc"!"malloc"(0, 2)
          [Al len, Al key1, Al key2, Al tss, Al ls, Al p1, Al sk1, Al ts1, Al p2, Al sk2, Al ts2,
           PRE[V, R] R =?> 2 * [| R <> $0 |] * [| freeable R 2 |]
             * stack len key1 key2 tss (V "stack")
             * V "self" =*> p1 * tree len key1 key2 sk1 ts1 p1 * [| functional ts1 |]
             * (V "self" ^+ $12) =*> p2 * tree len key1 key2 sk2 ts2 p2 * [| functional ts2 |]
             * lseq ls (V "ls") * mallocHeap 0
           POST[R'] stacktrees len key1 key2 tss
             * Ex sk1', V "self" =*> p1 * tree len key1 key2 sk1' ts1 p1
             * Ex sk2', (V "self" ^+ $12) =*> p2 * tree len key1 key2 sk2' ts2 p2
             * Ex ls', lseq (ls' ++ ls) R' * mallocHeap 0
             * [| multiEquivalence ((ts2, p2) :: (ts1, p1) :: tss) ls' |]];;

          "extra_stack" <-* "self";;
          "tmp" *<- "extra_stack";;
          "tmp" + 4 *<- "stack";;
          "stack" <- "tmp";;

          "tmp" <-- Call "malloc"!"malloc"(0, 2)
          [Al len, Al key1, Al key2, Al tss, Al ls, Al p2, Al sk2, Al ts2,
           PRE[V, R] R =?> 2 * [| R <> $0 |] * [| freeable R 2 |]
             * stack len key1 key2 tss (V "stack")
             * (V "self" ^+ $12) =*> p2 * tree len key1 key2 sk2 ts2 p2 * [| functional ts2 |]
             * lseq ls (V "ls") * mallocHeap 0
           POST[R'] stacktrees len key1 key2 tss
             * Ex sk2', (V "self" ^+ $12) =*> p2 * tree len key1 key2 sk2' ts2 p2
             * Ex ls', lseq (ls' ++ ls) R' * mallocHeap 0
             * [| multiEquivalence ((ts2, p2) :: tss) ls' |]];;

          "extra_stack" <-* "self" + 12;;
          "tmp" *<- "extra_stack";;
          "tmp" + 4 *<- "stack";;
          "stack" <- "tmp"
        }
      };;

      Return "ls"
    end

    with bfunction "findSecond"("extra_stack", "self", "k2", "ls", "stack", "tmp") [findSecondS]
      "self" <-* "self" + 12;;
      "ls" <-- Call "TupleList"!"new"("extra_stack")
      [Al len, Al key1, Al key2, Al sk, Al ts,
       PRE[V, R] lseq nil R * tree len key1 key2 sk ts (V "self") * [| functional ts |] * mallocHeap 0
       POST[R'] Ex sk', tree len key1 key2 sk' ts (V "self") * Ex ls, lseq ls R' * mallocHeap 0
             * [| EnsembleIndexedListEquivalence (keepEq ts key2 (V "k2")) ls |] ];;

      "stack" <-- Call "malloc"!"malloc"(0, 2)
      [Al len, Al key1, Al key2, Al sk, Al ts,
       PRE[V, R] R =?> 2 * [| R <> $0 |] * [| freeable R 2 |] * [| functional ts |]
               * tree len key1 key2 sk ts (V "self") * lseq nil (V "ls") * mallocHeap 0
       POST[R'] Ex sk', tree len key1 key2 sk' ts (V "self")
             * Ex ls, lseq ls R' * mallocHeap 0
             * [| EnsembleIndexedListEquivalence (keepEq ts key2 (V "k2")) ls |]];;

      "stack" *<- "self";;
      "stack" + 4 *<- 0;;

      [Al len, Al key1, Al key2, Al tss, Al ls,
       PRE[V, R] stack len key1 key2 tss (V "stack") * lseq ls (V "ls") * mallocHeap 0
       POST[R'] stacktrees len key1 key2 tss
             * Ex ls', lseq (ls' ++ ls) R' * mallocHeap 0
             * [| multiEquivalenceEq key2 (V "k2") tss ls' |] ]
      While ("stack" <> 0) {
        "self" <-* "stack";;
        "tmp" <-* "stack" + 4;;

        Call "malloc"!"free"(0, "stack", 2)
        [Al len, Al key1, Al key2, Al tss, Al ls, Al sk, Al tp, Al ts,
         PRE[V, R] stack len key1 key2 tss (V "tmp") * tree len key1 key2 sk ts (V "self")
                 * lseq ls (V "ls") * mallocHeap 0 * [| functional ts |]
         POST[R'] Ex sk', stacktrees len key1 key2 tss * tree len key1 key2 sk' ts (V "self")
                * Ex ls', lseq (ls' ++ ls) R' * mallocHeap 0
                * [| multiEquivalenceEq key2 (V "k2") ((ts, tp) :: tss) ls' |]];;

        "stack" <- "tmp";;

        If ("self" = 0) {
          Skip
        } else {
          "tmp" <-* "self" + 8;;
          Call "Tuples1"!"findInto"("extra_stack", "tmp", "k2", "ls")
          [Al len, Al key1, Al key2, Al tss, Al ls, Al p1, Al sk1, Al ts1, Al p2, Al sk2, Al ts2,
           PRE[V] stack len key1 key2 tss (V "stack")
             * V "self" =*> p1 * tree len key1 key2 sk1 ts1 p1 * [| functional ts1 |]
             * (V "self" ^+ $12) =*> p2 * tree len key1 key2 sk2 ts2 p2 * [| functional ts2 |]
             * lseq ls (V "ls") * mallocHeap 0
           POST[R] stacktrees len key1 key2 tss
             * Ex sk1', V "self" =*> p1 * tree len key1 key2 sk1' ts1 p1
             * Ex sk2', (V "self" ^+ $12) =*> p2 * tree len key1 key2 sk2' ts2 p2
             * Ex ls', lseq (ls' ++ ls) R * mallocHeap 0
             * [| multiEquivalenceEq key2 (V "k2") ((ts2, p1) :: (ts1, p2) :: tss) ls' |]];;

          "tmp" <-- Call "malloc"!"malloc"(0, 2)
          [Al len, Al key1, Al key2, Al tss, Al ls, Al p1, Al sk1, Al ts1, Al p2, Al sk2, Al ts2,
           PRE[V, R] R =?> 2 * [| R <> $0 |] * [| freeable R 2 |]
             * stack len key1 key2 tss (V "stack")
             * V "self" =*> p1 * tree len key1 key2 sk1 ts1 p1 * [| functional ts1 |]
             * (V "self" ^+ $12) =*> p2 * tree len key1 key2 sk2 ts2 p2 * [| functional ts2 |]
             * lseq ls (V "ls") * mallocHeap 0
           POST[R'] stacktrees len key1 key2 tss
             * Ex sk1', V "self" =*> p1 * tree len key1 key2 sk1' ts1 p1
             * Ex sk2', (V "self" ^+ $12) =*> p2 * tree len key1 key2 sk2' ts2 p2
             * Ex ls', lseq (ls' ++ ls) R' * mallocHeap 0
             * [| multiEquivalenceEq key2 (V "k2") ((ts2, p2) :: (ts1, p1) :: tss) ls' |]];;

          "extra_stack" <-* "self";;
          "tmp" *<- "extra_stack";;
          "tmp" + 4 *<- "stack";;
          "stack" <- "tmp";;

          "tmp" <-- Call "malloc"!"malloc"(0, 2)
          [Al len, Al key1, Al key2, Al tss, Al ls, Al p2, Al sk2, Al ts2,
           PRE[V, R] R =?> 2 * [| R <> $0 |] * [| freeable R 2 |]
             * stack len key1 key2 tss (V "stack")
             * (V "self" ^+ $12) =*> p2 * tree len key1 key2 sk2 ts2 p2 * [| functional ts2 |]
             * lseq ls (V "ls") * mallocHeap 0
           POST[R'] stacktrees len key1 key2 tss
             * Ex sk2', (V "self" ^+ $12) =*> p2 * tree len key1 key2 sk2' ts2 p2
             * Ex ls', lseq (ls' ++ ls) R' * mallocHeap 0
             * [| multiEquivalenceEq key2 (V "k2") ((ts2, p2) :: tss) ls' |]];;

          "extra_stack" <-* "self" + 12;;
          "tmp" *<- "extra_stack";;
          "tmp" + 4 *<- "stack";;
          "stack" <- "tmp"
        }
      };;

      Return "ls"
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Ltac descend' := try rewrite tuples2_eq; descend;
                 try match goal with
                     | [ H : insert _ ?b _ |- context[insert _ ?b' _] ] =>
                       unify b b'
                     end.

Ltac tree_cong :=
  try rewrite app_assoc;
  repeat apply himp_star_frame; try ((apply tuples1_Equiv || apply tree_Equiv); solve [ eauto ]);
  descend'; step hints; eauto.

Ltac t := solve [ enterFunction
            || (post; evaluate hints; descend; try unifyLocals; repeat (step hints; descend'); eauto;
                try tree_cong) ].

Lemma EnsembleIndexedListEquivalence_keepEq_keepEq_keepLt : forall ts k1 key1 key2 k k' v,
  EnsembleIndexedListEquivalence (keepEq (keepEq (keepLt ts key1 k1) key1 k) key2 k') v
  -> k < k1
  -> EnsembleIndexedListEquivalence (keepEq (keepEq ts key1 k) key2 k') v.
Proof.
  unfold EnsembleIndexedListEquivalence; Equiv'; intuition.

  destruct H1; intuition (subst; simpl in * ).

  exists x; intros.
  apply H.
  unfold TuplesF.keepEq, Ensembles.In in *; intuition.
  subst.
  rewrite sel_alt; auto.

  unfold UnIndexedEnsembleListEquivalence, Ensembles.In in *.
  destruct H2; intuition subst.
  exists x; intuition.
  apply H.
  unfold TuplesF.keepEq, Ensembles.In in *; intuition.
  subst.
  rewrite sel_alt; auto.
  apply H in H2.
  unfold TuplesF.keepEq, Ensembles.In in *; intuition.
Qed.

Hint Immediate EnsembleIndexedListEquivalence_keepEq_keepEq_keepLt.

Lemma EnsembleIndexedListEquivalence_keepEq_keepEq_keepGt : forall ts k1 key1 key2 k k' v,
  EnsembleIndexedListEquivalence (keepEq (keepEq (keepGt ts key1 k1) key1 k) key2 k') v
  -> k1 <= k
  -> k <> k1
  -> EnsembleIndexedListEquivalence (keepEq (keepEq ts key1 k) key2 k') v.
Proof.
  unfold EnsembleIndexedListEquivalence; Equiv'; intuition.

  destruct H2; intuition (subst; simpl in * ).
  exists x; intuition (subst; simpl in * ).

  apply H.
  unfold TuplesF.keepEq, Ensembles.In in *; intuition.
  subst.
  rewrite sel_alt; auto.

  unfold UnIndexedEnsembleListEquivalence, Ensembles.In in *.
  destruct H3; intuition subst.
  exists x; intuition.
  apply H.
  unfold TuplesF.keepEq, Ensembles.In in *; intuition.
  subst.
  rewrite sel_alt; auto.
  apply H in H3.
  unfold TuplesF.keepEq, Ensembles.In in *; intuition.
Qed.

Hint Resolve EnsembleIndexedListEquivalence_keepEq_keepEq_keepGt.

Lemma EnsembleIndexedListEquivalence_keepEq_keepEq_empty : forall ts key1 k key2 k',
  empty ts
  -> EnsembleIndexedListEquivalence (keepEq (keepEq ts key1 k) key2 k') nil.
Proof.
  unfold EnsembleIndexedListEquivalence; Equiv'; intuition.
  exists 0; firstorder.
  hnf.
  exists nil; firstorder.
  constructor.
Qed.

Hint Immediate EnsembleIndexedListEquivalence_keepEq_keepEq_empty.

Opaque multiEquivalence.

Lemma multiEq_init : forall key k ts tp ls,
  multiEquivalenceEq key k ((ts, tp) :: nil) ls
  -> EnsembleIndexedListEquivalence (keepEq ts key k) ls.
Proof.
  simpl.
  destruct 2 as [ ? [ ] ]; intuition subst.
  assumption.
Qed.

Hint Immediate multiEq_init.

Lemma multiEq_empty : forall key k tss ls ts tp,
  multiEquivalenceEq key k tss ls
  -> empty ts
  -> multiEquivalenceEq key k ((ts, tp) :: tss) ls.
Proof.
  simpl.
  intros.
  exists nil, ls; intuition.
Qed.

Hint Immediate multiEq_empty.

Hint Extern 1 (TuplesF.keepEq _ _ _ _ _ _) =>
  unfold TuplesF.keepEq, Ensembles.In in *; intuition idtac.

Theorem multiEq_step1 : forall key' k' ts tp key k tp1 tp2 tss ls1 ls2,
  multiEquivalenceEq key' k' ((keepGt ts key k, tp2) :: (keepLt ts key k, tp1) :: tss) ls1
  -> EnsembleIndexedListEquivalence (keepEq (keepEq ts key k) key' k') ls2
  -> functional ts
  -> multiEquivalenceEq key' k' ((ts, tp) :: tss) (ls1 ++ ls2).
Proof.
  unfold functional, EnsembleIndexedListEquivalence, UnIndexedEnsembleListEquivalence; Equiv'; intuition;
  repeat match goal with
         | [ H : Logic.ex _ |- _ ] => destruct H; intuition (subst; simpl in * )
         end.

  exists (x3 ++ x1 ++ map indexedElement x).
  exists x4; intuition.
  2: repeat rewrite app_assoc; reflexivity.
  unfold EnsembleIndexedListEquivalence, UnIndexedEnsembleListEquivalence in *; Equiv'; intuition;
  repeat match goal with
         | [ H : Logic.ex _ |- _ ] => destruct H; intuition (subst; simpl in * )
         end.

  exists (max x0 (max x1 x3)); intuition idtac.
  destruct (weq (Array.sel (indexedElement element) key) k); subst.
  assert (elementIndex element < x0)%nat by auto.
  specialize (Max.max_spec x1 x3); specialize (Max.max_spec x0 (max x1 x3)); intuition.

  destruct (wlt_dec (Array.sel (indexedElement element) key) k).
  assert (elementIndex element < x3)%nat by auto.
  specialize (Max.max_spec x1 x3); specialize (Max.max_spec x0 (max x1 x3)); intuition.

  assert (elementIndex element < x1)%nat by intuition.
  specialize (Max.max_spec x1 x3); specialize (Max.max_spec x0 (max x1 x3)); intuition.

  exists (x2 ++ x5 ++ x).
  repeat rewrite map_app; intuition.
  destruct (weq (Array.sel (indexedElement x6) key) k); subst.
  assert (In x6 x)%nat by (apply H0; auto).
  eauto using in_or_app.

  destruct (wlt_dec (Array.sel (indexedElement x6) key) k).
  assert (In x6 x2)%nat by (apply H4; auto).
  eauto using in_or_app.

  assert (In x6 x5)%nat by (apply H7; intuition).
  eauto using in_or_app.

  apply in_app_or in H8; intuition.
  firstorder.
  apply in_app_or in H9; intuition; firstorder.

  repeat apply NoDup_app; auto.

  intros.
  apply in_map_iff in H8.
  apply in_map_iff in H9.
  destruct H8, H9; intuition subst.
  apply H7 in H13.
  apply H0 in H14.
  unfold TuplesF.keepEq, Ensembles.In in *; intuition subst.
  specialize (H1 _ _ H9 H14 H8); subst.
  rewrite sel_alt in *.
  nomega.

  intros.
  apply in_app_or in H9; intuition.

  apply in_map_iff in H8.
  apply in_map_iff in H12.
  destruct H8, H12; intuition subst.
  apply H4 in H13.
  apply H7 in H14.
  unfold TuplesF.keepEq, Ensembles.In in *; intuition subst.
  specialize (H1 _ _ H9 H14 H8); subst.
  rewrite sel_alt in *.
  nomega.

  apply in_map_iff in H8.
  apply in_map_iff in H12.
  destruct H8, H12; intuition subst.
  apply H4 in H13.
  apply H0 in H14.
  unfold TuplesF.keepEq, Ensembles.In in *; intuition subst.
  specialize (H1 _ _ H9 H14 H8); subst.
  rewrite sel_alt in *.
  nomega.
Qed.

Hint Immediate multiEq_step1.

Lemma multiEq_nil : forall key k, multiEquivalenceEq key k nil nil.
Proof.
  reflexivity.
Qed.

Hint Immediate multiEq_nil.

Opaque multiEquivalenceEq.

Theorem ok : moduleOk m.
Proof.
  vcgen; try abstract t; t.

  Grab Existential Variables.
  exact 0.
  exact 0.
Qed.
