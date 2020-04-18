Require Import Bedrock.Examples.AutoSep Bedrock.Examples.Malloc Bedrock.Examples.Sets.

Set Implicit Arguments.


Local Hint Extern 3 (himp _ _ _) => apply himp_star_frame.
Local Hint Extern 3 (himp _ _ _) => apply himp_star_frame_comm.

Inductive tree :=
| Leaf
| Node : tree -> tree -> tree.

Module Type BST.
  Parameter bst' : set -> tree -> W -> HProp.
  Parameter bst : set -> W -> HProp.

  Axiom bst'_extensional : forall s t p, HProp_extensional (bst' s t p).
  Axiom bst_extensional : forall s p, HProp_extensional (bst s p).

  Axiom bst'_set_extensional : forall t s s' p, s %= s' -> bst' s t p ===> bst' s' t p.

  Axiom bst_fwd : forall s p, bst s p ===> [| freeable p 2 |]
    * Ex t, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * bst' s t r.
  Axiom bst_bwd : forall s p, ([| freeable p 2 |]
    * Ex t, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * bst' s t r) ===> bst s p.

  Axiom nil_fwd : forall s t (p : W), p = 0 -> bst' s t p ===> [| s %= empty /\ t = Leaf |].
  Axiom nil_bwd : forall s t (p : W), p = 0 -> [| s %= empty /\ t = Leaf |] ===> bst' s t p.

  Axiom cons_fwd : forall s t (p : W), p <> 0 -> bst' s t p ===>
    Ex t1, Ex t2, Ex p1, Ex v, Ex p2, (p ==*> p1, v, p2) * bst' (s %< v) t1 p1 * bst' (s %> v) t2 p2
    * [| freeable p 3 /\ t = Node t1 t2 /\ v %in s |].

  Axiom cons_bwd : forall s t (p : W), p <> 0 ->
    (Ex t1, Ex t2, Ex p1, Ex v, Ex p2, (p ==*> p1, v, p2) * bst' (s %< v) t1 p1 * bst' (s %> v) t2 p2
      * [| freeable p 3 /\ t = Node t1 t2 /\ v %in s |]) ===> bst' s t p.
End BST.

Module Bst : BST.
  Open Scope Sep_scope.

  Fixpoint bst' (s : set) (t : tree) (p : W) : HProp :=
    match t with
      | Leaf => [| p = 0 /\ s %= empty |]
      | Node t1 t2 => [| p <> 0 /\ freeable p 3 |] * Ex p1, Ex v, Ex p2, (p ==*> p1, v, p2)
        * bst' (s %< v) t1 p1
        * bst' (s %> v) t2 p2
        * [| v %in s |]
    end.

  Definition bst (s : set) (p : W) := [| freeable p 2 |]
    * Ex t, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * bst' s t r.

  Theorem bst'_extensional : forall s t p, HProp_extensional (bst' s t p).
    destruct t; reflexivity.
  Qed.

  Theorem bst_extensional : forall s p, HProp_extensional (bst s p).
    reflexivity.
  Qed.

  Theorem bst'_set_extensional : forall t s s' p, s %= s' -> bst' s t p ===> bst' s' t p.
    induction t; sepLemma.
  Qed.

  Theorem bst_fwd : forall s p, bst s p ===> [| freeable p 2 |]
    * Ex t, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * bst' s t r.
    unfold bst; sepLemma.
  Qed.

  Theorem bst_bwd : forall s p, ([| freeable p 2 |]
    * Ex t, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * bst' s t r) ===> bst s p.
    unfold bst; sepLemma.
  Qed.

  Theorem nil_fwd : forall s t (p : W), p = 0 -> bst' s t p ===> [| s %= empty /\ t = Leaf |].
    destruct t; sepLemma.
  Qed.

  Theorem nil_bwd : forall s t (p : W), p = 0 -> [| s %= empty /\ t = Leaf |] ===> bst' s t p.
    destruct t; sepLemma.
  Qed.

  Theorem cons_fwd : forall s t (p : W), p <> 0 -> bst' s t p ===>
    Ex t1, Ex t2, Ex p1, Ex v, Ex p2, (p ==*> p1, v, p2) * bst' (s %< v) t1 p1 * bst' (s %> v) t2 p2
    * [| freeable p 3 /\ t = Node t1 t2 /\ v %in s |].
    destruct t; sepLemma.
  Qed.

  Theorem cons_bwd : forall s t (p : W), p <> 0 ->
    (Ex t1, Ex t2, Ex p1, Ex v, Ex p2, (p ==*> p1, v, p2) * bst' (s %< v) t1 p1 * bst' (s %> v) t2 p2
    * [| freeable p 3 /\ t = Node t1 t2 /\ v %in s |]) ===> bst' s t p.
    destruct t; sepLemma;
      match goal with
        | [ H : Node _ _ = Node _ _ |- _ ] => injection H; sepLemma
      end.
  Qed.
End Bst.

Import Bst.
Export Bst.
Hint Immediate bst_extensional bst'_extensional.

(*TIME Clear Timing Profile. *)

Definition hints : TacPackage.
(*TIME idtac "tree-set:prepare1". Time *)
  prepare (bst_fwd, nil_fwd, cons_fwd) (bst_bwd, nil_bwd, cons_bwd).
(*TIME Time *)Defined.

Definition removeMaxS : spec := SPEC("prev") reserving 6
  Al s, Al t, Al p,
  PRE[V] V "prev" =*> p * [| p <> 0 |] * bst' s t p * mallocHeap
  POST[R] Ex t', Ex p', [| R %in s |] * [| s %> R %= empty |]
    * V "prev" =*> p' * bst' (s %- R) t' p' * mallocHeap.

Definition initS := initS bst 7.
Definition lookupS := lookupS bst 1.
Definition addS := addS bst 7.
Definition removeS := removeS bst 10.

Definition bstM := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "bst" {{
  bfunction "init"("r") [initS]
    "r" <-- Call "malloc"!"malloc"(0)
    [PRE[_, R] R =?> 2 * [| freeable R 2 |]
     POST[R'] [| R' = R |] * bst empty R ];;
    "r" *<- 0;;
    Return "r"
  end with bfunction "lookup"("s", "k", "tmp") [lookupS]
    "s" <-* "s";;

    [Al s, Al t,
      PRE[V] bst' s t (V "s") * mallocHeap
      POST[R] [| (V "k" %in s) \is R |] * bst' s t (V "s") * mallocHeap]
    While ("s" <> 0) {
      "tmp" <- "s" + 4;;
      "tmp" <-* "tmp";;
      If ("k" = "tmp") {
        (* Key matches! *)
        Return 1
      } else {
        If ("k" < "tmp") {
          (* Searching for a lower key *)
          "s" <-* "s"
        } else {
          (* Searching for a higher key *)
          "s" <- "s" + 8;;
          "s" <-* "s"
        }
      }
    };;
    Return 0
  end with bfunction "add"("s", "k", "tmp") [addS]
    "tmp" <-* "s";;
    [Al s, Al t,
      PRE[V] V "s" =*> V "tmp" * bst' s t (V "tmp") * mallocHeap
      POST[_] Ex t', Ex p', V "s" =*> p' * bst' (s %+ V "k") t' p' * mallocHeap]
    While ("tmp" <> 0) {
      "tmp" <- "tmp" + 4;;
      "tmp" <-* "tmp";;
      If ("k" = "tmp") {
        (* Key matches!  No need for changes. *)
        Return 0
      } else {
        "s" <-* "s";;
        If ("k" < "tmp") {
          (* Searching for a lower key *)
          Skip
        } else {
          (* Searching for a higher key *)
          "s" <- "s" + 8
        };;
        "tmp" <-* "s"
      }
    };;

    (* Found a spot for a new node.  Allocate and initialize it. *)

    "tmp" <-- Call "malloc"!"malloc"(1)
    [PRE[V, R] V "s" =?> 1 * R =?> 3
     POST[_] V "s" =*> R * (R ==*> $0, V "k", $0)];;
    "s" *<- "tmp";;
    "tmp" *<- 0;;
    "tmp" <- "tmp" + 4;;
    "tmp" *<- "k";;
    "tmp" <- "tmp" + 4;;
    "tmp" *<- 0;;
    Return 0
  end with bfunction "removeMax"("prev", "s", "tmp") [removeMaxS]
    "s" <-* "prev";;

    [Al s, Al t,
      PRE[V] [| V "s" <> 0 |] * V "prev" =*> V "s" * bst' s t (V "s") * mallocHeap
      POST[R] Ex t', Ex p', [| R %in s |] * [| s %> R %= empty |]
        * V "prev" =*> p' * bst' (s %- R) t' p' * mallocHeap ]
    While (1 = 1) {
      "tmp" <- "s" + 8;;
      "tmp" <-* "tmp";;

      If ("tmp" <> 0) {
        (* Right subtree is nonempty.  Keep looping. *)
        "prev" <- "s" + 8;;
        "s" <- "tmp"
      } else {
        (* Right subtree is empty.  We can free this node and return its key. *)

        (* Overwrite pointer into this node with its left subtree. *)
        "tmp" <-* "s";;
        "prev" *<- "tmp";;

        (* Save key. *)
        "tmp" <- "s" + 4;;
        "tmp" <-* "tmp";;

        (* Free node. *)
        Call "malloc"!"free"("s", 1)
        [PRE[V] Emp
         POST[R] [| R = V "tmp" |] ];;

        (* Return key. *)
        Return "tmp"
      }
    };;

    Fail (* Unreachable! *)
  end with bfunction "remove"("s", "k", "prev", "tmp") [removeS]
    "prev" <- "s";;
    "s" <-* "prev";;

    [Al s, Al t,
      PRE[V] V "prev" =*> V "s" * bst' s t (V "s") * mallocHeap
      POST[_] Ex t', Ex p', V "prev" =*> p' * bst' (s %- V "k") t' p' * mallocHeap ]
    While ("s" <> 0) {
      "tmp" <- "s" + 4;;
      "tmp" <-* "tmp";;

      If ("k" = "tmp") {
        (* Key matches!  Now the hard part: pulling another node's data value up here (if possible),
         * and then deleting this node. *)
        "tmp" <-* "s";;
        If (0 = "tmp") {
          (* Oh my goodness!  This test expression is a hack to prevent unfolding from firing!
           * (Since the provers don't understand symmetry of [<>]) *)

          (* Empty left subtree.  Promote the right subtree to this position. *)

          "tmp" <- "s" + 8;;
          "tmp" <-* "tmp";;
          "prev" *<- "tmp";;

          Call "malloc"!"free"("s", 1)
          [PRE[_] Emp
           POST[_] Emp ];;

          Return 0
        } else {
          "tmp" <- "s" + 8;;
          "tmp" <-* "tmp";;
          If (0 = "tmp") {
            (* Empty right subtree.  Promote the left subtree to this position. *)

            "tmp" <-* "s";;
            "prev" *<- "tmp";;

            Call "malloc"!"free"("s", 1)
            [PRE[_] Emp
             POST[_] Emp ];;

            Return 0
          } else {
            (* Both subtrees nonempty.  Remove minimum from right subtree and put it in this position. *)

            "tmp" <-- Call "bst"!"removeMax"("s")
            [PRE[V, R] (V "s" ^+ $4) =?> 1
             POST[_] (V "s" ^+ $4) =*> R];;

            "s" <- "s" + 4;;
            "s" *<- "tmp";;
            Return 0
          }
        }
      } else {
        If ("k" < "tmp") {
          (* Searching for a lower key *)
          Skip
        } else {
          (* Searching for a higher key *)
          "s" <- "s" + 8
        };;
        "prev" <- "s";;
        "s" <-* "prev"
      }
    };;

    (* Key not found!  So deletion is an easy no-op. *)
    Return 0
  end
}}.

Hint Rewrite Nat2N.id : N.

Lemma exhausted_cases : forall a b : W, a <> b
  -> ~(a < b)
  -> a > b.
  intros.
  assert (wordToN a <> wordToN b) by (generalize wordToN_inj; firstorder).
  nomega.
Qed.

Local Hint Resolve exhausted_cases.
Local Hint Extern 5 (@eq W _ _) => words.
Local Hint Extern 3 (himp _ _ _) => apply bst'_set_extensional.

Theorem bstMOk : moduleOk bstM.
(*TIME idtac "tree-set:verify". Time *)
  vcgen; abstract (sep hints; auto).
(*TIME Time *)Qed.

(*TIME Print Timing Profile. *)
