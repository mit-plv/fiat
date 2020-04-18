Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Malloc Bedrock.Platform.Bags Bedrock.Platform.Arrays8 Bedrock.Platform.MoreArrays.
Import Bags.W_Bag.

Local Hint Extern 1 (@eq W _ _) => words.


Inductive shape :=
| Leaf : shape
| Node : shape -> shape -> shape.

Module Type TREE.
  Parameter tree : bag -> W -> HProp.
  Parameter tree' : bag -> shape -> W -> HProp.
  Parameter tree'' : bag -> shape -> W -> W -> HProp.

  Axiom tree_fwd : forall b p, tree b p ===> Ex t, Ex p', Ex junk, (p ==*> p', junk) * tree' b t p'.
  Axiom tree_bwd : forall b p, (Ex t, Ex p', Ex junk, (p ==*> p', junk) * tree' b t p') ===> tree b p.

  Axiom tree'_nil_fwd : forall b t (p : W), p = 0
    -> tree' b t p ===> [| t = Leaf |].
  Axiom tree'_nil_bwd : forall b t (p : W), p = 0
    -> [| t = Leaf |] ===> tree' b t p.

  Axiom tree'_cons_fwd : forall b t (p : W), p <> 0
    -> tree' b t p ===> Ex t1, Ex t2, Ex i, Ex c, Ex p1, Ex p2, [| t = Node t1 t2 |] * (p ==*> i, c, p1, p2)
        * tree'' b t1 p1 c * tree' b t2 p2.
  Axiom tree'_cons_bwd : forall b t (p : W), p <> 0
    -> (Ex t1, Ex t2, Ex i, Ex c, Ex p1, Ex p2, [| t = Node t1 t2 |] * (p ==*> i, c, p1, p2)
        * tree'' b t1 p1 c * tree' b t2 p2) ===> tree' b t p.

  Axiom tree'_weaken : forall b b', b %<= b'
    -> forall t p, tree' b t p ===> tree' b' t p.

  Axiom tree''_zero_fwd : forall b t p (c : W), c = 0
    -> tree'' b t p c ===> [| p %in b |] * [| t = Leaf |].
  Axiom tree''_zero_bwd : forall b t p (c : W), c = 0
    -> [| p %in b |] * [| t = Leaf |] ===> tree'' b t p c.

  Axiom tree''_nonzero_fwd : forall b t p (c : W), c <> 0
    -> tree'' b t p c ===> tree' b t p.
  Axiom tree''_nonzero_bwd : forall b t p (c : W), c <> 0
    -> tree' b t p ===> tree'' b t p c.
End TREE.

Module Tree : TREE.
  Open Scope Sep_scope.

  Fixpoint tree' (b : bag) (t : shape) (p : W) : HProp :=
    match t with
      | Leaf => [| p = 0 |]
      | Node t1 t2 => [| p <> 0 |] * Ex i, Ex c, Ex p1, Ex p2, (p ==*> i, c, p1, p2)
        * (if weq c $0 then [| p1 %in b |] * [| t1 = Leaf |] else tree' b t1 p1) * tree' b t2 p2
    end.

  Definition tree'' (b : bag) (t : shape) (p c : W) : HProp :=
    if weq c $0
      then [| p %in b |] * [| t = Leaf |]
      else tree' b t p.

  Definition tree (b : bag) (p : W) : HProp := Ex t, Ex p', Ex junk, (p ==*> p', junk) * tree' b t p'.

  Theorem tree_fwd : forall b p, tree b p ===> Ex t, Ex p', Ex junk, (p ==*> p', junk) * tree' b t p'.
    unfold tree; sepLemma.
  Qed.

  Theorem tree_bwd : forall b p, (Ex t, Ex p', Ex junk, (p ==*> p', junk) * tree' b t p') ===> tree b p.
    unfold tree; sepLemma.
  Qed.

  Ltac normalize :=
    match goal with
      | [ |- context C[(Ex i : W, Ex c : W, Ex p1 : W, Ex p2 : W,
        ?p =*> i * ((?p ^+ $4) =*> c * ((?p ^+ $8) =*> p1 * (?p ^+ $12) =*> p2))
        * (if weq c $0 then [| p1 %in ?b |] * [| ?t1 = Leaf |] else tree' ?b ?t1 p1) * tree' ?b ?t2 p2)%Sep] ] =>
      let G := context C[(Ex i : W, Ex c : W, Ex p1 : W, Ex p2 : W,
        p =*> i * ((p ^+ $4) =*> c * ((p ^+ $8) =*> p1 * (p ^+ $12) =*> p2))
        * tree'' b t1 p1 c * tree' b t2 p2)%Sep] in
      change G
    end.

  Theorem tree'_nil_fwd : forall b t (p : W), p = 0
    -> tree' b t p ===> [| t = Leaf |].
    destruct t; simpl; intros; try normalize; sepLemma.
  Qed.

  Theorem tree'_nil_bwd : forall b t (p : W), p = 0
    -> [| t = Leaf |] ===> tree' b t p.
    destruct t; simpl; intros; try normalize; sepLemma.
  Qed.

  Theorem tree'_cons_fwd : forall b t (p : W), p <> 0
    -> tree' b t p ===> Ex t1, Ex t2, Ex i, Ex c, Ex p1, Ex p2, [| t = Node t1 t2 |] * (p ==*> i, c, p1, p2)
        * tree'' b t1 p1 c * tree' b t2 p2.
    destruct t; simpl; intros; try normalize; sepLemma.
  Qed.

  Theorem tree'_cons_bwd : forall b t (p : W), p <> 0
    -> (Ex t1, Ex t2, Ex i, Ex c, Ex p1, Ex p2, [| t = Node t1 t2 |] * (p ==*> i, c, p1, p2)
        * tree'' b t1 p1 c * tree' b t2 p2) ===> tree' b t p.
    destruct t; simpl; intros; try normalize; sepLemma;
      match goal with
        | [ H : Node _ _ = Node _ _ |- _ ] => injection H0; intros; subst; sepLemma
      end.
  Qed.

  Theorem tree'_weaken : forall b b', b %<= b'
    -> forall t p, tree' b t p ===> tree' b' t p.
    induction t; simpl; intros; repeat normalize; sepLemma;
      apply himp_star_frame; auto;
        unfold tree''; destruct (weq x1 $0); auto; sepLemma; eauto using incl_mem.
  Qed.

  Transparent natToWord.

  Theorem tree''_zero_fwd : forall b t p (c : W), c = 0
    -> tree'' b t p c ===> [| p %in b |] * [| t = Leaf |].
    unfold tree''; intros; subst; sepLemma.
  Qed.

  Theorem tree''_zero_bwd : forall b t p (c : W), c = 0
    -> [| p %in b |] * [| t = Leaf |] ===> tree'' b t p c.
    unfold tree''; intros; subst; sepLemma.
  Qed.

  Theorem tree''_nonzero_fwd : forall b t p (c : W), c <> 0
    -> tree'' b t p c ===> tree' b t p.
    unfold tree''; intros; destruct (weq c $0); sepLemma.
  Qed.

  Theorem tree''_nonzero_bwd : forall b t p (c : W), c <> 0
    -> tree' b t p ===> tree'' b t p c.
    unfold tree''; intros; destruct (weq c $0); sepLemma.
  Qed.

End Tree.

Import Tree.
Export Tree.

Inductive debufferize := Debufferize.
Hint Constructors debufferize.

Definition hints : TacPackage.
  prepare (tree_fwd, tree'_nil_fwd, tree'_cons_fwd, tree''_zero_fwd, tree''_nonzero_fwd)
  (tree_bwd, tree'_nil_bwd, tree'_cons_bwd, tree''_zero_bwd, tree''_nonzero_bwd).
Defined.

Import Bags.W_Bag.

Definition newS := SPEC reserving 8
  PRE[_] mallocHeap 0
  POST[R] tree empty R * mallocHeap 0.

Definition lookupS := SPEC("t", "key", "keyLen") reserving 2
  Al b,
  PRE[V] tree b (V "t") * V "key" =?>8 wordToNat (V "keyLen")
  POST[R] [| R = 0 \/ R %in b |] * tree b (V "t") * V "key" =?>8 wordToNat (V "keyLen").

Definition insertS := SPEC("t", "key", "keyLen", "value") reserving 13
  Al b,
  PRE[V] tree b (V "t") * V "key" =?>8 wordToNat (V "keyLen") * mallocHeap 0
  POST[_] tree (b %+ V "value") (V "t") * V "key" =?>8 wordToNat (V "keyLen") * mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "sys"!"abort" @ [abortS] ]]
  bmodule "stringdb" {{
    bfunction "new"("r") [newS]
      "r" <-- Call "malloc"!"malloc"(0, 2)
      [PRE[_, R] R =?> 2
       POST[R'] tree empty R'];;

      "r" *<- 0;;
      Return "r"
    end with bfunction "lookup"("t", "key", "keyLen", "i", "c") [lookupS]
      "t" <-* "t";;

      [Al b, Al t,
        PRE[V] tree' b t (V "t") * V "key" =?>8 wordToNat (V "keyLen")
        POST[R] [| R = 0 \/ R %in b |] * tree' b t (V "t") * V "key" =?>8 wordToNat (V "keyLen")]
      While ("t" <> 0) {
        "i" <-* "t";;
        "c" <-* "t" + 4;;

        If ("c" = 0) {
          (* Search might be done, leaving just a test on the length of key. *)
          If ("i" = "keyLen") {
            "t" <-* "t" + 8;;
            Return "t"
          } else {
            "t" <-* "t" + 12
          }
        } else {
          (* Regular internal node, with an equality test on a particular character of key. *)
          If ("i" < "keyLen") {
            Note [debufferize];;

            Assert [Al b, Al t1, Al t2, Al p1, Al p2, Al bs,
              PRE[V] (V "t" ==*> V "i", V "c", p1, p2) * tree' b t1 p1 * tree' b t2 p2
                * array8 bs (V "key") * [| (V "i" < natToW (length bs))%word |]
                * [| length bs = wordToNat (V "keyLen") |]
              POST[R] [| R = 0 \/ R %in b |] * (V "t" ==*> V "i", V "c", p1, p2) * tree' b t1 p1 * tree' b t2 p2
                * V "key" =?>8 wordToNat (V "keyLen")];;

            "i" <-*8 "key" + "i";;

            Note [debufferize];;

            Assert [Al i, Al b, Al t1, Al t2, Al p1, Al p2,
              PRE[V] (V "t" ==*> i, V "c", p1, p2) * tree' b t1 p1 * tree' b t2 p2
                * V "key" =?>8 wordToNat (V "keyLen")
              POST[R] [| R = 0 \/ R %in b |] * (V "t" ==*> i, V "c", p1, p2) * tree' b t1 p1 * tree' b t2 p2
                * V "key" =?>8 wordToNat (V "keyLen")];;

            If ("i" = "c") {
              "t" <-* "t" + 8
            } else {
              "t" <-* "t" + 12
            }
          } else {
            "t" <-* "t" + 12
          }
        }
      };;

      Return 0
    end with bfunction "insert"("t", "key", "keyLen", "value", "p", "pos", "i", "c", "c2", "matched") [insertS]
      "p" <-* "t";;
      "pos" <- 0;;

      [Al b, Al t,
        PRE[V] V "t" =*> V "p" * tree' b t (V "p") * V "key" =?>8 wordToNat (V "keyLen") * mallocHeap 0
        POST[_] Ex p, Ex t', V "t" =*> p * tree' (b %+ V "value") t' p * V "key" =?>8 wordToNat (V "keyLen")
          * mallocHeap 0]
      While (0 = 0) {
        If ("pos" < "keyLen") {
          (* We are in the phase of matching characters in key. *)

          (* Read current character from key. *)
          Note [debufferize];;

          Assert [Al b, Al t, Al bs,
            PRE[V] V "t" =*> V "p" * tree' b t (V "p") * array8 bs (V "key") * mallocHeap 0
              * [| length bs = wordToNat (V "keyLen") |] * [| (V "pos" < natToW (length bs))%word |]
            POST[_] Ex p, Ex t', V "t" =*> p * tree' (b %+ V "value") t' p
              * V "key" =?>8 wordToNat (V "keyLen") * mallocHeap 0];;

          "c2" <- "key" + "pos";;
          "c2" <-*8 "c2";;

          Note [debufferize];;

          Assert [Al b, Al t,
            PRE[V] V "t" =*> V "p" * tree' b t (V "p")
              * V "key" =?>8 wordToNat (V "keyLen") * mallocHeap 0
            POST[_] Ex p, Ex t', V "t" =*> p * tree' (b %+ V "value") t' p
              * V "key" =?>8 wordToNat (V "keyLen") * mallocHeap 0];;

          If ("p" = 0) {
            "matched" <- 0
          } else {
            "i" <-* "p";;
            If ("i" = "pos") {
              "matched" <- 1
            } else {
              "matched" <- 0
            }
          };;

          If ("matched" = 1) {
            Assert [Al b, Al i, Al c, Al p1, Al p2, Al t1, Al t2,
              PRE[V] [| V "p" <> 0 |] * V "t" =*> V "p" * (V "p" ==*> i, c, p1, p2)
                * tree'' b t1 p1 c * tree' b t2 p2
                * V "key" =?>8 wordToNat (V "keyLen") * mallocHeap 0
              POST[_] Ex p, Ex t', V "t" =*> p * tree' (b %+ V "value") t' p
                * V "key" =?>8 wordToNat (V "keyLen") * mallocHeap 0];;

            (* The next test in the tree matches the character we are focusing on. *)
            "c" <-* "p"+4;;

            If ("c" = 0) {
              (* This is a length test that fails for us. *)
              "t" <- "p"+12
            } else {
              If ("c2" = "c") {
                (* Character match.  Continue along the "true" path. *)
                "t" <- "p"+8;;
                "pos" <- "pos" + 1
              } else {
                (* Character non-match.  Continue along the "false" path. *)
                "t" <- "p"+12
              }
            };;

            "p" <-* "t"
          } else {
            Assert [Al b, Al t,
              PRE[V] V "t" =*> V "p" * tree' b t (V "p")
                * V "key" =?>8 wordToNat (V "keyLen") * mallocHeap 0
              POST[_] Ex p, Ex t', V "t" =*> p * tree' (b %+ V "value") t' p
                * V "key" =?>8 wordToNat (V "keyLen") * mallocHeap 0];;

            (* The current position-character pair is not represented in the tree.  Let's add it here. *)
            "c" <-- Call "malloc"!"malloc"(0, 4)
            [Al b, Al t,
              PRE[V, R] R =?> 4 * [| R <> 0 |] * V "t" =*> V "p" * tree' b t (V "p")
                * V "key" =?>8 wordToNat (V "keyLen") * mallocHeap 0
              POST[_] Ex p, Ex t', V "t" =*> p * tree' (b %+ V "value") t' p
                * V "key" =?>8 wordToNat (V "keyLen") * mallocHeap 0];;

            If ("c2" = 0) {
              (* Informal invariant violated!  Key contains an internal '0' character. *)
              Call "sys"!"abort"()
              [PREonly[_] [| False |] ];;
              Fail
            } else {
              Skip
            };;

            "c" *<- "pos";;
            "c"+4 *<- "c2";;
            "c"+8 *<- 0;;
            "c"+12 *<- "p";;

            "t" *<- "c";;
            "t" <- "c"+8;;
            "p" <- 0;;
            "pos" <- "pos" + 1
          }
        } else {
          (* We are ready to insert the final check, on string length. *)

          "pos" <-- Call "malloc"!"malloc"(0, 4)
          [Al b, Al t,
            PRE[V, R] R =?> 4 * [| R <> 0 |] * V "t" =*> V "p" * tree' b t (V "p")
            POST[_] Ex p, Ex t', V "t" =*> p * tree' (b %+ V "value") t' p];;

          "pos" *<- "keyLen";;
          "pos"+4 *<- 0;;
          "pos"+8 *<- "value";;
          "pos"+12 *<- "p";;

          "t" *<- "pos";;
          Return 0
        }
      }
    end
  }}.

Hint Extern 1 (@eq W _ _) => words.

Ltac finish :=
  repeat match goal with
           | [ H : _ = _ |- _ ] => rewrite H
         end; try rewrite natToW_wordToNat;
  try apply tree'_weaken; auto.

Ltac t :=
  match goal with
    | [ |- forall stn_st specs, interp specs (Ex st', _ /\ [| evalInstrs _ _ (Assign (LvMem (Sp + natToW 0)%loc) (RvLval (LvReg Rp)) :: nil) = _ |])%PropX -> interp specs _ ] => solve [ sep hints ]
    | _ =>
      try match goal with
            | [ |- context[debufferize] ] => unfold buffer
          end;
      post; evaluate hints; try (discriminate || tauto); descend; try match_locals; sep hints; finish
  end.

Theorem ok : moduleOk m.
  vcgen; abstract t.
Qed.
