Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Facade.examples.TupleF Bedrock.Platform.Facade.examples.ArrayTupleF.
Require Import Bedrock.Platform.Malloc Bedrock.Platform.Facade.examples.TupleSeqF.
Require Import Bedrock.Platform.Facade.examples.TupleListF Bedrock.Platform.Facade.examples.TuplesF.
Require Import Bedrock.Platform.Facade.examples.Tuples0F.

Inductive skel :=
| Leaf
| Node (sk1 sk2 : skel).

Definition keepEq : tuples -> W -> W -> tuples :=
  keepEq (@eq _) (natToW 0).
Definition keepLt (ts : tuples) (key k : W) : tuples :=
  fun tup => Ensembles.In _ ts tup /\ Array.sel (indexedElement tup) key < k.
Definition keepGt (ts : tuples) (key k : W) : tuples :=
  fun tup => Ensembles.In _ ts tup /\ Array.sel (indexedElement tup) key > k.
Definition empty (ts : tuples) := forall t, ~Ensembles.In _ ts t.

Ltac Equiv' := unfold insert, EnsembleInsert, Equiv,
               keepEq, keepLt, keepGt, empty, Ensembles.In, UnConstrFreshIdx in *.
Ltac Equiv := Equiv'; firstorder idtac.

Theorem keepEq_Equiv : forall ts1 ts2 key k,
  Equiv ts1 ts2
  -> Equiv (keepEq ts1 key k) (keepEq ts2 key k).
Proof.
  Equiv.
Qed.

Theorem keepLt_Equiv : forall ts1 ts2 key k,
  Equiv ts1 ts2
  -> Equiv (keepLt ts1 key k) (keepLt ts2 key k).
Proof.
  Equiv.
Qed.

Theorem keepGt_Equiv : forall ts1 ts2 key k,
  Equiv ts1 ts2
  -> Equiv (keepGt ts1 key k) (keepGt ts2 key k).
Proof.
  Equiv.
Qed.

Hint Immediate keepEq_Equiv keepLt_Equiv keepGt_Equiv.


Module Type ADT.
  Parameter tuples1 : W -> W -> tuples -> W -> HProp.
  Parameter tree : W -> W -> skel -> tuples -> W -> HProp.

  Axiom tuples1_fwd : forall len key ts c, tuples1 len key ts c
    ===> [| c <> 0 |] * [| freeable c 3 |] * [| $2 <= len |]
        * Ex p, Ex sk, (c ==*> len, key, p) * tree len key sk ts p * [| key < len |].
  Axiom tuples1_bwd : forall len key ts (c : W),
    ([| c <> 0 |] * [| freeable c 3 |] * [| $2 <= len |]
    * Ex p, Ex sk, (c ==*> len, key, p) * tree len key sk ts p * [| key < len |])
    ===> tuples1 len key ts c.

  (* Sometimes this version is necessary to integrate well with the automation. *)
  Axiom tuples1_eq : forall len key ts c, tuples1 len key ts c
    = ([| c <> 0 |] * [| freeable c 3 |] * [| $2 <= len |]
        * Ex p, Ex sk, (c ==*> len, key, p) * tree len key sk ts p * [| key < len |])%Sep.

  Axiom tuples1_Equiv : forall len key ts1 ts2 p,
    Equiv ts1 ts2
    -> tuples1 len key ts1 p ===> tuples1 len key ts2 p.

  Axiom tree_Equiv : forall len key sk ts1 ts2 p,
    Equiv ts1 ts2
    -> tree len key sk ts1 p ===> tree len key sk ts2 p.

  Axiom tree_leaf_fwd : forall len key sk ts (p : W), p = 0
    -> tree len key sk ts p ===> [| sk = Leaf |] * [| empty ts |].

  Axiom tree_leaf_bwd : forall len key sk ts (p : W), p = 0
    -> [| sk = Leaf |] * [| empty ts |] ===> tree len key sk ts p.

  Axiom tree_node_fwd : forall len key sk ts (p : W), p <> 0
    -> tree len key sk ts p ===> Ex sk1, Ex sk2, Ex p1, Ex k, Ex t0, Ex p2, [| sk = Node sk1 sk2 |]
        * (p ==*> p1, k, t0, p2)
        * tree len key sk1 (keepLt ts key k) p1
        * tuples0 len (keepEq ts key k) t0
        * tree len key sk2 (keepGt ts key k) p2.

  Axiom tree_node_bwd : forall len key sk ts (p : W), p <> 0
    -> (Ex sk1, Ex sk2, Ex p1, Ex k, Ex t0, Ex p2, [| sk = Node sk1 sk2 |]
        * (p ==*> p1, k, t0, p2)
        * tree len key sk1 (keepLt ts key k) p1
        * tuples0 len (keepEq ts key k) t0
        * tree len key sk2 (keepGt ts key k) p2) ===> tree len key sk ts p.


  Parameter stack : W -> W -> list (tuples * W) -> W -> HProp.
  (* This last one is used as we walk a tree in full to enumerate. *)

  Axiom stack_nil_fwd : forall len key tss (p : W), p = 0
    -> stack len key tss p ===> [| tss = nil |].

  Axiom stack_nil_bwd : forall len key tss (p : W), p = 0
    -> [| tss = nil |] ===> stack len key tss p.

  Axiom stack_cons_fwd : forall len key tss (p : W), p <> 0
    -> stack len key tss p ===> Ex ts, Ex tp, Ex tss', [| tss = (ts, tp) :: tss' |] * [| freeable p 2 |]
      * [| functional ts |]
      * Ex sk, Ex p', (p ==*> tp, p') * tree len key sk ts tp * stack len key tss' p'.

  Axiom stack_cons_bwd : forall len key tss (p : W), p <> 0
    -> (Ex ts, Ex tp, Ex tss', [| tss = (ts, tp) :: tss' |] * [| freeable p 2 |] * [| functional ts |]
      * Ex sk, Ex p', (p ==*> tp, p') * tree len key sk ts tp * stack len key tss' p')
      ===> stack len key tss p.
End ADT.

Module Adt : ADT.
  Open Scope Sep_scope.

  Fixpoint tree (len key : W) (sk : skel) (ts : tuples) (p : W) : HProp :=
    match sk with
    | Leaf => [| p = 0 |] * [| empty ts |]
    | Node sk1 sk2 => [| p <> 0 |]
      * Ex p1, Ex k, Ex t0, Ex p2, (p ==*> p1, k, t0, p2)
        * tree len key sk1 (keepLt ts key k) p1
        * tuples0 len (keepEq ts key k) t0
        * tree len key sk2 (keepGt ts key k) p2
    end.

  Fixpoint stack (len key : W) (tss : list (tuples * W)) (p : W) : HProp :=
    match tss with
    | nil => [| p = 0 |]
    | (ts, tp) :: tss' => [| p <> 0 |] * [| freeable p 2 |] * [| functional ts |] * Ex sk, Ex p', (p ==*> tp, p')
                    * tree len key sk ts tp * stack len key tss' p'
    end.

  Definition tuples1 (len key : W) (ts : tuples) (c : W) : HProp :=
    [| c <> 0 |] * [| freeable c 3 |] * [| $2 <= len |]
    * Ex p, Ex sk, (c ==*> len, key, p) * tree len key sk ts p * [| key < len |].

  Theorem stack_nil_fwd : forall len key tss (p : W), p = 0
    -> stack len key tss p ===> [| tss = nil |].
  Proof.
    destruct tss as [ ? | [ ] ]; sepLemma.
  Qed.

  Theorem stack_nil_bwd : forall len key tss (p : W), p = 0
    -> [| tss = nil |] ===> stack len key tss p.
  Proof.
    destruct tss as [ ? | [ ] ]; sepLemma.
  Qed.

  Theorem stack_cons_fwd : forall len key tss (p : W), p <> 0
    -> stack len key tss p ===> Ex ts, Ex tp, Ex tss', [| tss = (ts, tp) :: tss' |] * [| freeable p 2 |]
      * [| functional ts |]
      * Ex sk, Ex p', (p ==*> tp, p') * tree len key sk ts tp * stack len key tss' p'.
  Proof.
    destruct tss as [ ? | [ ] ]; sepLemma.
  Qed.

  Theorem stack_cons_bwd : forall len key tss (p : W), p <> 0
    -> (Ex ts, Ex tp, Ex tss', [| tss = (ts, tp) :: tss' |] * [| freeable p 2 |] * [| functional ts |]
      * Ex sk, Ex p', (p ==*> tp, p') * tree len key sk ts tp * stack len key tss' p')
      ===> stack len key tss p.
  Proof.
    destruct tss as [ ? | [ ] ]; sepLemma.
    injection H0; sepLemma; auto.
    injection H0; sepLemma.
  Qed.

  Theorem tuples1_fwd : forall len key ts c, tuples1 len key ts c
    ===> [| c <> 0 |] * [| freeable c 3 |] * [| $2 <= len |]
    * Ex p, Ex sk, (c ==*> len, key, p) * tree len key sk ts p * [| key < len |].
  Proof.
    unfold tuples1; sepLemma; eauto.
  Qed.

  Theorem tuples1_bwd : forall len key ts (c : W),
    ([| c <> 0 |] * [| freeable c 3 |] * [| $2 <= len |]
     * Ex p, Ex sk, (c ==*> len, key, p) * tree len key sk ts p * [| key < len |])
    ===> tuples1 len key ts c.
  Proof.
    unfold tuples1; sepLemma; eauto.
  Qed.

  Theorem tuples1_eq : forall len key ts c, tuples1 len key ts c
    = ([| c <> 0 |] * [| freeable c 3 |] * [| $2 <= len |]
        * Ex p, Ex sk, (c ==*> len, key, p) * tree len key sk ts p * [| key < len |])%Sep.
  Proof.
    auto.
  Qed.

  Theorem tree_Equiv : forall len key sk ts1 ts2 p,
    Equiv ts1 ts2
    -> tree len key sk ts1 p ===> tree len key sk ts2 p.
  Proof.
    induction sk; sepLemma.

    Equiv.

    repeat apply himp_star_frame; eauto.
    eapply tuples0_Equiv; eauto.
  Qed.

  Theorem tuples1_Equiv : forall len key ts1 ts2 p,
    Equiv ts1 ts2
    -> tuples1 len key ts1 p ===> tuples1 len key ts2 p.
  Proof.
    unfold tuples1; sepLemma.
    eapply tree_Equiv; eauto.
  Qed.

  Theorem tree_leaf_fwd : forall len key sk ts (p : W), p = 0
    -> tree len key sk ts p ===> [| sk = Leaf |] * [| empty ts |].
  Proof.
    destruct sk; sepLemma.
  Qed.

  Theorem tree_leaf_bwd : forall len key sk ts (p : W), p = 0
    -> [| sk = Leaf |] * [| empty ts |] ===> tree len key sk ts p.
  Proof.
    destruct sk; sepLemma.
  Qed.

  Theorem tree_node_fwd : forall len key sk ts (p : W), p <> 0
    -> tree len key sk ts p ===> Ex sk1, Ex sk2, Ex p1, Ex k, Ex t0, Ex p2, [| sk = Node sk1 sk2 |]
        * (p ==*> p1, k, t0, p2)
        * tree len key sk1 (keepLt ts key k) p1
        * tuples0 len (keepEq ts key k) t0
        * tree len key sk2 (keepGt ts key k) p2.
  Proof.
    destruct sk; sepLemma.
  Qed.

  Theorem tree_node_bwd : forall len key sk ts (p : W), p <> 0
    -> (Ex sk1, Ex sk2, Ex p1, Ex k, Ex t0, Ex p2, [| sk = Node sk1 sk2 |]
        * (p ==*> p1, k, t0, p2)
        * tree len key sk1 (keepLt ts key k) p1
        * tuples0 len (keepEq ts key k) t0
        * tree len key sk2 (keepGt ts key k) p2) ===> tree len key sk ts p.
  Proof.
    destruct sk; sepLemma.
    injection H0; sepLemma.
  Qed.
End Adt.

Import Adt.
Export Adt.

Definition hints : TacPackage.
  prepare (tuples1_fwd, tree_leaf_fwd, tree_node_fwd, stack_nil_fwd, stack_cons_fwd)
          (tuples1_bwd, tree_leaf_bwd, tree_node_bwd, stack_nil_bwd, stack_cons_bwd).
Defined.

(* Also, we want a way to indicate that the trees in a stack are intact, even though the stack has been freed. *)
Fixpoint stacktrees (len key : W) (tss : list (tuples * W)) : HProp :=
  match tss with
  | nil => Emp
  | (ts, tp) :: tss' => (Ex sk, tree len key sk ts tp) * stacktrees len key tss'
  end%Sep.

Definition newS := SPEC("extra_stack", "len", "key") reserving 7
  PRE[V] [| V "len" >= $2 |] * [| V "key" < V "len" |] * mallocHeap 0
  POST[R] tuples1 (V "len") (V "key") Empty R * mallocHeap 0.

Definition insertS := SPEC("extra_stack", "self", "tup") reserving 21
  Al len, Al key, Al ts, Al t, Al ts',
  PRE[V] tuples1 len key ts (V "self") * tuple t (V "tup") * [| length t = wordToNat len |] * mallocHeap 0
         * [| insert ts t ts' |]
  POST[R] [| R = $0 |] * tuples1 len key ts' (V "self") * mallocHeap 0.

Definition findS := SPEC("extra_stack", "self", "k") reserving 34
  Al len, Al key, Al ts,
  PRE[V] tuples1 len key ts (V "self") * mallocHeap 0
  POST[R] tuples1 len key ts (V "self") * Ex ls, lseq ls R * mallocHeap 0
        * [| EnsembleIndexedListEquivalence (keepEq ts key (V "k")) ls |].

Definition findIntoS := SPEC("extra_stack", "self", "k", "ls") reserving 28
  Al len, Al key, Al ts, Al ls,
  PRE[V] tuples1 len key ts (V "self") * lseq ls (V "ls") * mallocHeap 0
  POST[R] [| R = $0 |] * tuples1 len key ts (V "self") * Ex ls', lseq (ls' ++ ls) (V "ls") * mallocHeap 0
          * [| EnsembleIndexedListEquivalence (keepEq ts key (V "k")) ls' |].

Definition enumerateS := SPEC("extra_stack", "self") reserving 34
  Al len, Al key, Al ts,
  PRE[V] tuples1 len key ts (V "self") * [| functional ts |] * mallocHeap 0
  POST[R] tuples1 len key ts (V "self") * Ex ls, lseq ls R * mallocHeap 0
          * [| EnsembleIndexedListEquivalence ts ls |].

Definition enumerateIntoS := SPEC("extra_stack", "self", "ls") reserving 29
  Al len, Al key, Al ts, Al ls,
  PRE[V] tuples1 len key ts (V "self") * lseq ls (V "ls") * [| functional ts |] * mallocHeap 0
  POST[R] [| R = $0 |] * tuples1 len key ts (V "self") * Ex ls', lseq (ls' ++ ls) (V "ls") * mallocHeap 0
          * [| EnsembleIndexedListEquivalence ts ls' |].

Fixpoint multiEquivalence (tss : list (tuples * W)) (ls : list tupl) : Prop :=
  match tss with
  | nil => ls = nil
  | (ts, _) :: tss' => exists ls1 ls2, EnsembleIndexedListEquivalence ts ls1
                                       /\ multiEquivalence tss' ls2
                                       /\ ls = ls2 ++ ls1
  end.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "ArrayTuple"!"get" @ [ArrayTupleF.getS], "TupleList"!"new" @ [TupleListF.newS],
                           "Tuples0"!"new" @ [Tuples0F.newS], "Tuples0"!"insert" @ [Tuples0F.insertS],
                           "Tuples0"!"enumerateInto" @ [Tuples0F.enumerateIntoS] ]]
  bmodule "Tuples1" {{
    bfunction "new"("extra_stack", "len", "key") [newS]
      "extra_stack" <-- Call "malloc"!"malloc"(0, 3)
      [PRE[V, R] R =?> 3 * [| R <> 0 |] * [| freeable R 3 |]
              * [| (V "len" >= $2)%word |] * [| (V "key" < V "len")%word |]
       POST[R'] tuples1 (V "len") (V "key") Empty R'];;

      "extra_stack" *<- "len";;
      "extra_stack" + 4 *<- "key";;
      "extra_stack" + 8 *<- 0;;
      Return "extra_stack"
    end

    with bfunction "insert"("extra_stack", "self", "tup", "len", "key", "p", "k1", "k2") [insertS]
      "len" <-* "self";;
      "key" <-* "self" + 4;;
      "self" <- "self" + 8;;
      "p" <-* "self";;
      "k1" <-- Call "ArrayTuple"!"get"("extra_stack", "tup", "key")
      [Al ts, Al t, Al ts', Al sk,
       PRE[V, R] V "self" =*> V "p" * tree (V "len") (V "key") sk ts (V "p") * tuple t (V "tup")
         * [| length t = wordToNat (V "len") |] * [| (V "key" < V "len")%word |] * mallocHeap 0
         * [| R = Array.sel t (V "key") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R'] [| R' = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key") sk' ts' p * mallocHeap 0];;

      [Al ts, Al t, Al ts', Al sk,
       PRE[V] V "self" =*> V "p" * tree (V "len") (V "key") sk ts (V "p") * tuple t (V "tup")
         * [| length t = wordToNat (V "len") |] * [| (V "key" < V "len")%word |] * mallocHeap 0
         * [| V "k1" = Array.sel t (V "key") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R] [| R = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key") sk' ts' p * mallocHeap 0]
      While ("p" <> 0) {
        "k2" <-* "p" + 4;;

        If ("k1" = "k2") {
          (* Found existing node for this key.  Add to its collection. *)
          "k2" <-* "p" + 8;;
          Call "Tuples0"!"insert"("extra_stack", "k2", "tup")
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
      "k2" <-- Call "Tuples0"!"new"("extra_stack", "len")
      [Al ts, Al t, Al ts',
       PRE[V, R] tuples0 (V "len") Empty R * [| empty ts |]
         * V "self" =*> V "p" * tuple t (V "tup")
         * [| length t = wordToNat (V "len") |] * [| (V "key" < V "len")%word |] * mallocHeap 0
         * [| V "k1" = Array.sel t (V "key") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R'] [| R' = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key") sk' ts' p * mallocHeap 0];;

      Call "Tuples0"!"insert"("extra_stack", "k2", "tup")
      [Al ts, Al t, Al ts',
       PRE[V] tuples0 (V "len") ts' (V "k2") * [| empty ts |]
         * V "self" =*> V "p"
         * [| length t = wordToNat (V "len") |] * [| (V "key" < V "len")%word |] * mallocHeap 0
         * [| V "k1" = Array.sel t (V "key") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R] [| R = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key") sk' ts' p * mallocHeap 0];;

      "p" <-- Call "malloc"!"malloc"(0, 4)
      [Al ts, Al t, Al ts',
       PRE[V, R] R =?> 4 * [| R <> 0 |] * [| empty ts |]
         * tuples0 (V "len") ts' (V "k2")
         * V "self" =*> V "p"
         * [| length t = wordToNat (V "len") |] * [| (V "key" < V "len")%word |] * mallocHeap 0
         * [| V "k1" = Array.sel t (V "key") |] * [| ($2 <= V "len")%word |] * [| insert ts t ts' |]
       POST[R] [| R = $0 |] * Ex p, Ex sk',
         V "self" =*> p * tree (V "len") (V "key") sk' ts' p * mallocHeap 0];;

      "p" *<- 0;;
      "p" + 4 *<- "k1";;
      "p" + 8 *<- "k2";;
      "p" + 12 *<- 0;;
      "self" *<- "p";;
      Return 0
    end

    with bfunction "find"("extra_stack", "self", "k", "ls") [findS]
      "ls" <-- Call "TupleList"!"new"("extra_stack")
      [Al len, Al key, Al ts,
       PRE[V, R] lseq nil R * tuples1 len key ts (V "self") * mallocHeap 0
       POST[R'] tuples1 len key ts (V "self")
             * Ex ls, lseq ls R' * mallocHeap 0
             * [| EnsembleIndexedListEquivalence (keepEq ts key (V "k")) ls |] ];;

      Call "Tuples1"!"findInto"("extra_stack", "self", "k", "ls")
      [PRE[V] Emp
       POST[R] [| R = V "ls" |] ];;
      Return "ls"
    end
    with bfunction "findInto"("extra_stack", "self", "k", "ls", "k2") [findIntoS]
      "self" <-* "self" + 8;;

      [Al len, Al key, Al sk, Al ts, Al ls,
       PRE[V] tree len key sk ts (V "self") * lseq ls (V "ls") * mallocHeap 0
       POST[R] [| R = $0 |] * tree len key sk ts (V "self") * Ex ls', lseq (ls' ++ ls) (V "ls") * mallocHeap 0
             * [| EnsembleIndexedListEquivalence (keepEq ts key (V "k")) ls' |] ]
      While ("self" <> 0) {
        "k2" <-* "self" + 4;;

        If ("k2" = "k") {
          (* Found existing node for this key.  Duplicate its collection. *)
          "k2" <-* "self" + 8;;
          Call "Tuples0"!"enumerateInto"("extra_stack", "k2", "ls")
          [PRE[_] Emp
           POST[R] [| R = $0 |] ];;
          Return 0
        } else {
          (* No match.  Proceed to appropriate subtree. *)
          If ("k" < "k2") {
            "self" <-* "self"
          } else {
            "self" <-* "self" + 12
          }
        }
      };;

      (* In this delightful imperative version, we just do nada if we don't find a match. *)
      Return 0
    end

    with bfunction "enumerate"("extra_stack", "self", "ls") [enumerateS]
      "ls" <-- Call "TupleList"!"new"("extra_stack")
      [Al len, Al key, Al ts,
       PRE[V, R] lseq nil R * tuples1 len key ts (V "self") * [| functional ts |] * mallocHeap 0
       POST[R'] tuples1 len key ts (V "self")
             * Ex ls, lseq ls R' * mallocHeap 0
             * [| EnsembleIndexedListEquivalence ts ls |] ];;

      Call "Tuples1"!"enumerateInto"("extra_stack", "self", "ls")
      [PRE[V] Emp
       POST[R] [| R = V "ls" |] ];;
      Return "ls"
    end

    with bfunction "enumerateInto"("extra_stack", "self", "ls", "stack", "tmp") [enumerateIntoS]
      "self" <-* "self" + 8;;
      "stack" <-- Call "malloc"!"malloc"(0, 2)
      [Al len, Al key, Al sk, Al ts, Al ls,
       PRE[V, R] R =?> 2 * [| R <> $0 |] * [| freeable R 2 |] * [| functional ts |]
               * tree len key sk ts (V "self") * lseq ls (V "ls") * mallocHeap 0
       POST[R'] Ex sk', [| R' = $0 |] * tree len key sk' ts (V "self")
             * Ex ls', lseq (ls' ++ ls) (V "ls") * mallocHeap 0
             * [| EnsembleIndexedListEquivalence ts ls' |]];;

      "stack" *<- "self";;
      "stack" + 4 *<- 0;;

      [Al len, Al key, Al tss, Al ls,
       PRE[V, R] stack len key tss (V "stack") * lseq ls (V "ls") * mallocHeap 0
       POST[R'] [| R' = $0 |] * stacktrees len key tss
             * Ex ls', lseq (ls' ++ ls) (V "ls") * mallocHeap 0
             * [| multiEquivalence tss ls' |] ]
      While ("stack" <> 0) {
        "self" <-* "stack";;
        "tmp" <-* "stack" + 4;;

        Call "malloc"!"free"(0, "stack", 2)
        [Al len, Al key, Al tss, Al ls, Al sk, Al tp, Al ts,
         PRE[V, R] stack len key tss (V "tmp") * tree len key sk ts (V "self")
                 * lseq ls (V "ls") * mallocHeap 0 * [| functional ts |]
         POST[R'] Ex sk', [| R' = $0 |] * stacktrees len key tss * tree len key sk' ts (V "self")
                * Ex ls', lseq (ls' ++ ls) (V "ls") * mallocHeap 0
                * [| multiEquivalence ((ts, tp) :: tss) ls' |]];;

        "stack" <- "tmp";;

        If ("self" = 0) {
          Skip
        } else {
          "tmp" <-* "self" + 8;;
          Call "Tuples0"!"enumerateInto"("extra_stack", "tmp", "ls")
          [Al len, Al key, Al tss, Al ls, Al p1, Al sk1, Al ts1, Al p2, Al sk2, Al ts2,
           PRE[V] stack len key tss (V "stack")
             * V "self" =*> p1 * tree len key sk1 ts1 p1 * [| functional ts1 |]
             * (V "self" ^+ $12) =*> p2 * tree len key sk2 ts2 p2 * [| functional ts2 |]
             * lseq ls (V "ls") * mallocHeap 0
           POST[R] [| R = $0 |] * stacktrees len key tss
             * Ex sk1', V "self" =*> p1 * tree len key sk1' ts1 p1
             * Ex sk2', (V "self" ^+ $12) =*> p2 * tree len key sk2' ts2 p2
             * Ex ls', lseq (ls' ++ ls) (V "ls") * mallocHeap 0
             * [| multiEquivalence ((ts2, p1) :: (ts1, p2) :: tss) ls' |]];;

          "tmp" <-- Call "malloc"!"malloc"(0, 2)
          [Al len, Al key, Al tss, Al ls, Al p1, Al sk1, Al ts1, Al p2, Al sk2, Al ts2,
           PRE[V, R] R =?> 2 * [| R <> $0 |] * [| freeable R 2 |]
             * stack len key tss (V "stack")
             * V "self" =*> p1 * tree len key sk1 ts1 p1 * [| functional ts1 |]
             * (V "self" ^+ $12) =*> p2 * tree len key sk2 ts2 p2 * [| functional ts2 |]
             * lseq ls (V "ls") * mallocHeap 0
           POST[R'] [| R' = $0 |] * stacktrees len key tss
             * Ex sk1', V "self" =*> p1 * tree len key sk1' ts1 p1
             * Ex sk2', (V "self" ^+ $12) =*> p2 * tree len key sk2' ts2 p2
             * Ex ls', lseq (ls' ++ ls) (V "ls") * mallocHeap 0
             * [| multiEquivalence ((ts2, p2) :: (ts1, p1) :: tss) ls' |]];;

          "extra_stack" <-* "self";;
          "tmp" *<- "extra_stack";;
          "tmp" + 4 *<- "stack";;
          "stack" <- "tmp";;

          "tmp" <-- Call "malloc"!"malloc"(0, 2)
          [Al len, Al key, Al tss, Al ls, Al p2, Al sk2, Al ts2,
           PRE[V, R] R =?> 2 * [| R <> $0 |] * [| freeable R 2 |]
             * stack len key tss (V "stack")
             * (V "self" ^+ $12) =*> p2 * tree len key sk2 ts2 p2 * [| functional ts2 |]
             * lseq ls (V "ls") * mallocHeap 0
           POST[R'] [| R' = $0 |] * stacktrees len key tss
             * Ex sk2', (V "self" ^+ $12) =*> p2 * tree len key sk2' ts2 p2
             * Ex ls', lseq (ls' ++ ls) (V "ls") * mallocHeap 0
             * [| multiEquivalence ((ts2, p2) :: tss) ls' |]];;

          "extra_stack" <-* "self" + 12;;
          "tmp" *<- "extra_stack";;
          "tmp" + 4 *<- "stack";;
          "stack" <- "tmp"
        }
      };;

      Return 0
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Lemma empty_Empty : empty Empty.
Proof.
  hnf; intuition.
Qed.

Hint Resolve empty_Empty.

Lemma insert_keepLt : forall ts t ts' key k1 k,
  insert ts t ts'
  -> k1 = Array.sel t key
  -> k1 < k
  -> insert (keepLt ts key k) t (keepLt ts' key k).
Proof.
  Equiv.
  subst; simpl.
  exists x; intuition (subst; simpl in *; auto).
  apply H2 in H3; intuition (subst; simpl in * ).
  apply H2; tauto.
  firstorder.
Qed.

Hint Immediate insert_keepLt.

Lemma selN_alt : forall t key,
    Array.selN t key =
    match nth_error t key with
    | Some k0 => k0
    | None => 0
    end.
Proof.
  induction t; destruct key; simpl; intuition.
Qed.

Lemma sel_alt : forall t key,
    Array.sel t key =
    match nth_error t (wordToNat key) with
    | Some k0 => k0
    | None => 0
    end.
Proof.
  intros; apply selN_alt.
Qed.

Lemma sel_alt' : forall (t : list W) key,
    match nth_error t (wordToNat key) with
    | Some k0 => k0
    | None => 0
    end
    = Array.sel t key.
Proof.
  symmetry; apply sel_alt.
Qed.

Hint Immediate sel_alt sel_alt'.

Lemma Equiv_keepEq_lt : forall k1 k ts key ts' t,
  insert ts t ts'
  -> k1 <> k
  -> k1 = Array.sel t key
  -> Equiv (keepEq ts key k) (keepEq ts' key k).
Proof.
  Equiv.
  subst.
  apply H2 in H3; intuition (subst; simpl in * ).
  exfalso; eauto.
Qed.

Hint Immediate Equiv_keepEq_lt.

Lemma Equiv_keepGt_lt : forall k1 k ts key ts' t,
  insert ts t ts'
  -> k1 < k
  -> k1 = Array.sel t key
  -> Equiv (keepGt ts key k) (keepGt ts' key k).
Proof.
  Equiv.
  subst.
  apply H2 in H3; intuition (subst; simpl in * ).
  nomega.
Qed.

Hint Immediate Equiv_keepGt_lt.

Lemma Equiv_keepEq_gt : forall k1 k ts key ts' t,
  insert ts t ts'
  -> k1 <> k
  -> k1 = Array.sel t key
  -> Equiv (keepEq ts key k) (keepEq ts' key k).
Proof.
  Equiv.
  subst.
  apply H2 in H3; intuition (subst; simpl in * ).
  exfalso; eauto.
Qed.

Hint Immediate Equiv_keepEq_lt.

Lemma Equiv_keepLt_gt : forall k1 k ts key ts' t,
  insert ts t ts'
  -> k <= k1
  -> k1 <> k
  -> k1 = Array.sel t key
  -> Equiv (keepLt ts key k) (keepLt ts' key k).
Proof.
  Equiv.
  subst.
  apply H3 in H4; intuition (subst; simpl in * ).
  tauto.
Qed.

Hint Immediate Equiv_keepLt_gt.

Lemma insert_keepGt : forall ts t ts' key k1 k,
  insert ts t ts'
  -> k1 = Array.sel t key
  -> k <= k1
  -> k1 <> k
  -> insert (keepGt ts key k) t (keepGt ts' key k).
Proof.
  Equiv.
  subst; simpl.
  exists x; intuition (subst; simpl in *; auto).
  apply H3 in H4; intuition (subst; simpl in * ).
  apply H3; tauto.
  destruct (weq (Array.sel t key) k); intuition.
  firstorder.
Qed.

Hint Immediate insert_keepGt.

Lemma insert_keepEq : forall ts t ts' key k1,
  insert ts t ts'
  -> k1 = Array.sel t key
  -> insert (keepEq ts key k1) t (keepEq ts' key k1).
Proof.
  unfold keepEq, TuplesF.keepEq.
  Equiv.
  subst; simpl.
  exists x; intuition (subst; simpl in *; auto).
  apply H1 in H2; intuition (subst; simpl in * ).
  apply H1; tauto.
  eauto.
  firstorder.
Qed.

Hint Immediate insert_keepEq.

Lemma Equiv_keepLt_eq : forall k ts key ts' t,
  insert ts t ts'
  -> k = Array.sel t key
  -> Equiv (keepLt ts key k) (keepLt ts' key k).
Proof.
  Equiv.
  subst.
  apply H1 in H2; intuition (subst; simpl in * ).
  nomega.
Qed.

Lemma Equiv_keepGt_eq : forall k ts key ts' t,
  insert ts t ts'
  -> k = Array.sel t key
  -> Equiv (keepGt ts key k) (keepGt ts' key k).
Proof.
  Equiv.
  subst.
  apply H1 in H2; intuition (subst; simpl in * ).
  nomega.
Qed.

Hint Immediate Equiv_keepLt_eq Equiv_keepGt_eq.

Lemma insert_empty_Empty : forall ts t ts',
  empty ts
  -> insert ts t ts'
  -> insert Empty t ts'.
Proof.
  Equiv.
Qed.

Hint Immediate insert_empty_Empty.

Theorem keepEq_eq : forall ts t ts' key k,
  insert ts t ts'
  -> empty ts
  -> k = Array.sel t key
  -> Equiv ts' (keepEq ts' key k).
Proof.
  Equiv.
  apply H2 in H3; intuition (subst; simpl in * ).
  symmetry; eauto.
  firstorder.
Qed.

Hint Immediate keepEq_eq.

Theorem empty_keepLt : forall ts t ts' key k1,
  insert ts t ts'
  -> empty ts
  -> k1 = Array.sel t key
  -> empty (keepLt ts' key k1).
Proof.
  Equiv.
  intuition.
  apply H2 in H4; intuition (subst; simpl in * ).
  nomega.
  eauto.
Qed.

Theorem empty_keepGt : forall ts t ts' key k1,
  insert ts t ts'
  -> empty ts
  -> k1 = Array.sel t key
  -> empty (keepGt ts' key k1).
Proof.
  Equiv.
  intuition.
  apply H2 in H4; intuition (subst; simpl in * ).
  nomega.
  eauto.
Qed.

Hint Immediate empty_keepLt empty_keepGt.

Lemma EnsembleIndexedListEquivalence_keepEq_keepLt : forall ts k1 key k v,
  EnsembleIndexedListEquivalence (keepEq (keepLt ts key k1) key k) v
  -> k < k1
  -> EnsembleIndexedListEquivalence (keepEq ts key k) v.
Proof.
  unfold EnsembleIndexedListEquivalence; Equiv'; intuition.

  destruct H1; intuition (subst; simpl in * ).

  eexists; intros; apply H.
  unfold TuplesF.keepEq, Ensembles.In in *; intuition.
  rewrite sel_alt.
  congruence.

  unfold UnIndexedEnsembleListEquivalence in *.
  destruct H2; intuition subst.
  exists x; intuition.
  apply H.
  unfold TuplesF.keepEq, Ensembles.In in *; intuition.
  rewrite sel_alt.
  congruence.
  apply H in H2.
  unfold TuplesF.keepEq, Ensembles.In in *; intuition.
Qed.

Hint Immediate EnsembleIndexedListEquivalence_keepEq_keepLt.

Lemma cmp : forall k k1 : W,
    ~k < k1
    -> k <> k1
    -> k1 < k.
Proof.
  intros.
  destruct (wlt_dec k1 k); auto.
  exfalso; apply H0.
  apply MoreArrays.wordToNat_inj.
  nomega.
Qed.

Hint Immediate cmp.

Lemma EnsembleIndexedListEquivalence_keepEq_keepGt : forall ts k1 key k v,
  EnsembleIndexedListEquivalence (keepEq (keepGt ts key k1) key k) v
  -> k1 <= k
  -> k <> k1
  -> EnsembleIndexedListEquivalence (keepEq ts key k) v.
Proof.
  unfold EnsembleIndexedListEquivalence; Equiv'; intuition.

  destruct H2; intuition (subst; simpl in * ).
  exists x; intuition (subst; simpl in * ).

  apply H.
  unfold TuplesF.keepEq, Ensembles.In in *; intuition subst.
  rewrite sel_alt.
  auto.

  unfold UnIndexedEnsembleListEquivalence in *.
  destruct H3; intuition subst.
  exists x; intuition.
  apply H.
  unfold TuplesF.keepEq, Ensembles.In in *; intuition subst.
  rewrite sel_alt.
  auto.
  apply H in H3.
  unfold TuplesF.keepEq, Ensembles.In in *; intuition.
Qed.

Hint Resolve EnsembleIndexedListEquivalence_keepEq_keepGt.

Lemma EnsembleIndexedListEquivalence_keepEq_empty : forall ts key k,
  empty ts
  -> EnsembleIndexedListEquivalence (keepEq ts key k) nil.
Proof.
  unfold EnsembleIndexedListEquivalence; Equiv'; intuition.
  exists 0; firstorder.
  hnf.
  exists nil; firstorder.
  constructor.
Qed.

Hint Immediate EnsembleIndexedListEquivalence_keepEq_empty.

Hint Rewrite <- app_nil_end : sepFormula.

Lemma multi_init : forall ts tp ls,
  multiEquivalence ((ts, tp) :: nil) ls
  -> EnsembleIndexedListEquivalence ts ls.
Proof.
  simpl.
  destruct 2 as [ ? [ ] ]; intuition subst.
  assumption.
Qed.

Hint Immediate multi_init.

Lemma multi_empty : forall tss ls ts tp,
  multiEquivalence tss ls
  -> empty ts
  -> multiEquivalence ((ts, tp) :: tss) ls.
Proof.
  simpl.
  intros.
  exists nil, ls; intuition.
  hnf.
  intuition.
  exists 0; hnf; intros.
  apply H0 in H1; tauto.
  exists nil.
  intuition.
  apply H0 in H1; tauto.
  constructor.
Qed.

Hint Immediate multi_empty.

Theorem NoDup_app : forall A (ls1 ls2 : list A),
  NoDup ls1
  -> NoDup ls2
  -> (forall x, In x ls1 -> In x ls2 -> False)
  -> NoDup (ls1 ++ ls2).
Proof.
  induction 1; simpl; intuition.
  constructor.
  intro.
  apply in_app_or in H4; intuition eauto.
  eauto.
Qed.

Hint Unfold TuplesF.keepEq.

Theorem multi_step1 : forall ts tp key k tp1 tp2 tss ls1 ls2,
  multiEquivalence ((keepGt ts key k, tp2) :: (keepLt ts key k, tp1) :: tss) ls1
  -> EnsembleIndexedListEquivalence (keepEq ts key k) ls2
  -> functional ts
  -> multiEquivalence ((ts, tp) :: tss) (ls1 ++ ls2).
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

  exists (max x0 (max x1 x3)); intros.
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
  intuition subst.
  unfold TuplesF.keepEq in H14; intuition.
  specialize (H1 _ _ H13 H9 H8); subst.
  rewrite sel_alt' in *.
  nomega.

  intros.
  apply in_app_or in H9; intuition.

  apply in_map_iff in H8.
  apply in_map_iff in H12.
  destruct H8, H12; intuition subst.
  apply H4 in H13.
  apply H7 in H14.
  intuition subst.
  specialize (H1 _ _ H13 H9 H8); subst.
  nomega.

  apply in_map_iff in H8.
  apply in_map_iff in H12.
  destruct H8, H12; intuition subst.
  apply H4 in H13.
  apply H0 in H14.
  intuition subst.
  unfold TuplesF.keepEq in H14; intuition.
  specialize (H1 _ _ H13 H9 H8); subst.
  rewrite sel_alt' in *.
  nomega.
Qed.

Hint Immediate multi_step1.

Opaque multiEquivalence.

Lemma functional_keepLt : forall ts key k,
  functional ts
  -> functional (keepLt ts key k).
Proof.
  unfold functional, keepLt, Ensembles.In; firstorder.
Qed.

Lemma functional_keepGt : forall ts key k,
  functional ts
  -> functional (keepGt ts key k).
Proof.
  unfold functional, keepLt, Ensembles.In; firstorder.
Qed.

Lemma functional_keepEq : forall ts key k,
  functional ts
  -> functional (keepEq ts key k).
Proof.
  unfold functional, keepEq, Ensembles.In; firstorder.
Qed.

Hint Immediate functional_keepLt functional_keepGt functional_keepEq.

Lemma multi_nil : multiEquivalence nil nil.
Proof.
  Transparent multiEquivalence.
  reflexivity.
  Opaque multiEquivalence.
Qed.

Hint Immediate multi_nil.

Ltac unifyLocals :=
  match goal with
  | [ _ : interp _ (![?P1] ?x) |- interp _ (![?P2] ?x) ] =>
    match P1 with
    | context[locals _ ?vs1 ?y _] =>
      match P2 with
      | context[locals _ ?vs2 y _] => unify vs1 vs2; descend
      end
    end
  | [ |- interp _ (![?P1] ?x ---> ![?P2] ?x)%PropX ] =>
    match P1 with
    | context[locals ?y ?vs1 _ _] =>
      match P2 with
      | context[locals y ?vs2 _ _] => unify vs1 vs2; descend
      end
    end
  end.

Ltac descend' := try rewrite tuples1_eq; descend;
                try match goal with
                    | [ H : insert _ ?b _ |- context[insert _ ?b' _] ] =>
                      unify b b'
                    end.

Ltac tree_cong :=
  try rewrite app_assoc;
  repeat apply himp_star_frame; try ((apply tuples0_Equiv || apply tree_Equiv); solve [ eauto ]);
  descend'; step hints; eauto.

Ltac t := solve [ enterFunction
            || (post; evaluate hints; descend; try unifyLocals; repeat (step hints; descend'); eauto;
                try tree_cong) ].

Theorem ok : moduleOk m.
Proof.
  vcgen; try abstract t; t.

  Grab Existential Variables.
  exact 0.
Qed.
