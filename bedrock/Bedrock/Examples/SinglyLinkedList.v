Require Import Bedrock.Examples.AutoSep.
Require Import Coq.Lists.List.

Set Implicit Arguments.


(** The king of the abstract predicates *)

Module Type SINGLY_LINKED_LIST.
  Parameter sll : list W -> W -> HProp.

  Axiom sll_extensional : forall ls p, HProp_extensional (sll ls p).

  Axiom nil_fwd : forall ls (p : W), p = 0
    -> sll ls p ===> [| ls = nil |].

  Axiom nil_bwd : forall ls (p : W), p = 0
    -> [| ls = nil |] ===> sll ls p.

  Axiom cons_fwd : forall ls (p : W), p <> 0
    -> sll ls p ===> Ex x, Ex ls', [| ls = x :: ls' |] * Ex p', (p ==*> x, p') * sll ls' p'.

  Axiom cons_bwd : forall ls (p : W), p <> 0
    -> (Ex x, Ex ls', [| ls = x :: ls' |] * Ex p', (p ==*> x, p') * sll ls' p') ===> sll ls p.
End SINGLY_LINKED_LIST.

Module SinglyLinkedList : SINGLY_LINKED_LIST.
  Open Scope Sep_scope.

  Fixpoint sll (ls : list W) (p : W) : HProp :=
    match ls with
      | nil => [| p = 0 |]
      | x :: ls' => [| p <> 0 |] * Ex p', (p ==*> x, p') * sll ls' p'
    end.

  Theorem sll_extensional : forall ls (p : W), HProp_extensional (sll ls p).
    destruct ls; reflexivity.
  Qed.

  Theorem nil_fwd : forall ls (p : W), p = 0
    -> sll ls p ===> [| ls = nil |].
    destruct ls; sepLemma.
  Qed.

  Theorem nil_bwd : forall ls (p : W), p = 0
    -> [| ls = nil |] ===> sll ls p.
    destruct ls; sepLemma.
  Qed.

  Theorem cons_fwd : forall ls (p : W), p <> 0
    -> sll ls p ===> Ex x, Ex ls', [| ls = x :: ls' |] * Ex p', (p ==*> x, p') * sll ls' p'.
    destruct ls; sepLemma.
  Qed.

  Theorem cons_bwd : forall ls (p : W), p <> 0
    -> (Ex x, Ex ls', [| ls = x :: ls' |] * Ex p', (p ==*> x, p') * sll ls' p') ===> sll ls p.
    destruct ls; sepLemma;
      match goal with
        | [ H : _ :: _ = _ :: _ |- _ ] => injection H; sepLemma
      end.
  Qed.
End SinglyLinkedList.

Import SinglyLinkedList.
Hint Immediate sll_extensional.

(*TIME Clear Timing Profile. *)

Definition hints : TacPackage.
(*TIME idtac "sll:prepare". Time *)
  prepare (nil_fwd, cons_fwd) (nil_bwd, cons_bwd).
(*TIME Time *)
Defined.

Definition null A (ls : list A) : bool :=
  match ls with
    | nil => true
    | _ => false
  end.

Definition nullS : spec := SPEC("x") reserving 0
  Al ls,
  PRE[V] sll ls (V "x")
  POST[R] [| R = null ls |] * sll ls (V "x").

Definition lengthS : spec := SPEC("x") reserving 1
  Al ls,
  PRE[V] sll ls (V "x")
  POST[R] [| R = length ls |] * sll ls (V "x").

Definition revS : spec := SPEC("x") reserving 3
  Al ls,
  PRE[V] sll ls (V "x")
  POST[R] sll (rev ls) R.

Definition appendS : spec := SPEC("x", "y") reserving 2
  Al ls1, Al ls2,
  PRE[V] sll ls1 (V "x") * sll ls2 (V "y")
  POST[R] sll (ls1 ++ ls2) R.

Definition sllM := bmodule "sll" {{
  bfunction "null"("x") [nullS]
    If ("x" = 0) {
      Return 1
    } else {
      Return 0
    }
  end with bfunction "length"("x", "n") [lengthS]
    "n" <- 0;;
    [Al ls,
      PRE[V] sll ls (V "x")
      POST[R] [| R = V "n" ^+ (length ls : W) |] * sll ls (V "x")]
    While ("x" <> 0) {
      "n" <- "n" + 1;;
      "x" <- "x" + 4;;
      "x" <-* "x"
    };;
    Return "n"
  end with bfunction "rev"("x", "acc", "tmp1", "tmp2") [revS]
    "acc" <- 0;;
    [Al ls, Al accLs,
      PRE[V] sll ls (V "x") * sll accLs (V "acc")
      POST[R] Ex ls', [| ls' = rev_append ls accLs |] * sll ls' R ]
    While ("x" <> 0) {
      "tmp2" <- "x";;
      "tmp1" <- "x" + 4;;
      "x" <-* "tmp1";;
      "tmp1" *<- "acc";;
      "acc" <- "tmp2"
    };;
    Return "acc"
  end with bfunction "append"("x", "y", "r", "tmp") [appendS]
    If ("x" = 0) {
      Return "y"
    } else {
      "r" <- "x";;
      "tmp" <- "x" + 4;;
      "tmp" <-* "tmp";;
      [Al p1, Al x, Al ls1, Al ls2,
        PRE[V] [| V "x" <> $0 |] * [| V "tmp" = p1 |]
          * V "x" =*> x * (V "x" ^+ $4) =*> p1 * sll ls1 p1 * sll ls2 (V "y")
        POST[R] [| R = V "r" |] * sll (x :: ls1 ++ ls2) (V "x") ]
      While ("tmp" <> 0) {
        "x" <- "tmp";;
        "tmp" <- "x" + 4;;
        "tmp" <-* "tmp"
      };;

      "tmp" <- "x" + 4;;
      "tmp" *<- "y";;
      Return "r"
    }
  end
}}.

Ltac notConst x :=
  match x with
    | O => fail 1
    | S ?x' => notConst x'
    | _ => idtac
  end.

Ltac finish := repeat match goal with
                        | [ H : _ = _ |- _ ] => rewrite H
                      end; simpl;
               repeat match goal with
                        | [ |- context[natToW (S ?x)] ] =>
                          notConst x; rewrite (natToW_S x)
                      end; try rewrite <- rev_alt;
               congruence || W_eq || reflexivity || tauto || eauto.

Theorem sllMOk : moduleOk sllM.
(*TIME idtac "sll:verify". Time *)
  vcgen; abstract (sep hints; finish).
(*TIME Time *)
Qed.

(*TIME Print Timing Profile. *)
