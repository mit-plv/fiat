Require Import Bedrock.Examples.AutoSep Bedrock.Examples.Malloc.


(** Theory of sets, with tactics and hints *)

Definition set := W -> Prop.

Definition mem (w : W) (s : set) := s w.
Infix "%in" := mem (at level 70, no associativity).

Definition empty : set := fun _ => False.

Definition equiv (s1 s2 : set) := forall w, s1 w <-> s2 w.
Infix "%=" := equiv (at level 70, no associativity).

Definition add (s : set) (w : W) : set := fun w' => w' = w \/ s w'.
Infix "%+" := add (at level 50, left associativity).

Definition del (s : set) (w : W) : set := fun w' => w' <> w /\ s w'.
Infix "%-" := del (at level 50, left associativity).

Definition less (s : set) (w : W) : set := fun w' => w' < w /\ s w'.
Definition greater (s : set) (w : W) : set := fun w' => w' > w /\ s w'.
Infix "%<" := less (at level 40, left associativity).
Infix "%>" := greater (at level 40, left associativity).

Ltac sets := subst;
  repeat match goal with
           | [ H : _ %= _ |- _ ] => generalize dependent H
           | [ H : _ %in _ |- _ ] => generalize dependent H
           | [ H : ~ _ %in _ |- _ ] => generalize dependent H
           | [ H : _ < _ |- _ ] => generalize dependent H
           | [ H : _ <= _ |- _ ] => generalize dependent H
           | [ H : @eq W _ _ |- _ ] => generalize dependent H
           | [ H : not (@eq W _ _) |- _ ] => generalize dependent H
           | [ H : _ \is _ |- _ ] => generalize dependent H
         end; clear;
  unfold equiv, empty, mem, add, del, less, greater, propToWord, IF_then_else; intros;
    try match goal with
          | [ |- context[?s ?w] ] =>
            match type of s with
              | set => repeat match goal with
                                | [ H : forall x : W, _ |- _ ] => specialize (H w)
                              end
            end
        end; intuition; subst;
    try match goal with
          | [ |- ~(_ = _) ] => intro; try subst
        end;
    try (nomega || (elimtype False; nomega)).

Hint Extern 5 (_ %= _) => sets.
Hint Extern 5 (_ %in _) => sets.
Hint Extern 5 (~ _ %in _) => sets.
Hint Extern 5 (_ <-> _) => sets.

Lemma wlt_trans : forall a b c : W, a < b -> b < c -> a < c.
  intros; nomega.
Qed.

Hint Extern 1 (_ < _) => eapply wlt_trans; eassumption.


(** * The finite set ADT *)

Section adt.
  Variable P : set -> W -> HProp.
  (* Abstract predicate for the data structure *)

  Variable res : nat.
  (* How many reserved stack slots? *)

  Definition initS : spec := SPEC reserving res
    PRE[_] mallocHeap
    POST[R] P empty R * mallocHeap.

  Definition lookupS : spec := SPEC("s", "k") reserving res
    Al s,
    PRE[V] P s (V "s") * mallocHeap
    POST[R] [| (V "k" %in s) \is R |] * P s (V "s") * mallocHeap.

  Definition addS : spec := SPEC("s", "k") reserving res
    Al s,
    PRE[V] P s (V "s") * mallocHeap
    POST[_] P (s %+ V "k") (V "s") * mallocHeap.

  Definition removeS : spec := SPEC("s", "k") reserving res
    Al s,
    PRE[V] P s (V "s") * mallocHeap
    POST[_] P (s %- V "k") (V "s") * mallocHeap.
End adt.
