Require Import Coq.omega.Omega.
Require Import Bedrock.Examples.AutoSep Bedrock.Examples.Malloc.


Definition bag := W * W -> nat.

Theorem W_W_dec : forall x y : W * W, {x = y} + {x <> y}.
  decide equality; apply weq.
Qed.

Definition mem (p : W * W) (b : bag) := (b p > 0)%nat.
Infix "%in" := mem (at level 70, no associativity).

Definition empty : bag := fun _ => O.

Definition equiv (b1 b2 : bag) := forall p, b1 p = b2 p.
Infix "%=" := equiv (at level 70, no associativity).

Definition add (b : bag) (p : W * W) : bag := fun p' => if W_W_dec p' p then S (b p') else b p'.
Infix "%+" := add (at level 50, left associativity).

Definition del (b : bag) (p : W * W) : bag := fun p' => if W_W_dec p' p then pred (b p') else b p'.
Infix "%-" := del (at level 50, left associativity).

Ltac bags := subst;
  repeat match goal with
           | [ H : _ %= _ |- _ ] => generalize dependent H
           | [ H : _ %in _ |- _ ] => generalize dependent H
           | [ H : ~ _ %in _ |- _ ] => generalize dependent H
           | [ H : _ \is _ |- _ ] => generalize dependent H
           | [ H : @eq W _ _ |- _ ] => generalize dependent H
           | [ H : ~(@eq W _ _) |- _ ] => generalize dependent H
         end; clear;
  unfold equiv, empty, mem, add, del, propToWord, IF_then_else; intuition idtac;
    repeat (match goal with
              | [ H : (_, _) = (_, _) |- _ ] => injection H; clear H; intros; subst
              | [ |- context[if ?E then _ else _] ] => destruct E; subst
              | [ _ : context[if ?E then _ else _] |- _ ] => destruct E; subst
              | [ H : forall p : W * W, _ |- _ ] => rewrite H in *
            end; intuition idtac);
    try match goal with
          | [ |- _ \/ _ ] => right; intuition idtac
        end;
    repeat match goal with
             | [ H : forall p : W * W, _ |- _ ] => rewrite H in *
           end; auto; try (discriminate || omega).

Hint Extern 5 (_ %= _) => bags.
Hint Extern 5 (_ %in _) => bags.
Hint Extern 5 (~ _ %in _) => bags.
Hint Extern 5 (_ \is _) => bags.


Section adt.
  Variable P : bag -> W -> HProp.
  (* Abstract predicate for the data structure *)

  Variable res : nat.
  (* How many reserved stack slots? *)

  Definition initS : spec := SPEC reserving res
    PRE[_] mallocHeap
    POST[R] P empty R * mallocHeap.

  Definition isEmptyS : spec := SPEC("b") reserving res
    Al b,
    PRE[V] P b (V "b") * mallocHeap
    POST[R] [| (b %= empty) \is R |] * P b (V "b") * mallocHeap.

  Definition enqueueS : spec := SPEC("b", "v1", "v2") reserving res
    Al b,
    PRE[V] P b (V "b") * mallocHeap
    POST[_] P (b %+ (V "v1", V "v2")) (V "b") * mallocHeap.

  Definition dequeueS : spec := SPEC("b", "r") reserving res
    Al b,
    PRE[V] [| ~(b %= empty) |] * P b (V "b") * V "r" =?> 2 * mallocHeap
    POST[_] Ex v1, Ex v2, P (b %- (v1, v2)) (V "b") * (V "r" ==*> v1, v2) * mallocHeap.
End adt.
