(** Useful list operations *)
Require Import Coq.Lists.List.

Set Implicit Arguments.

Fixpoint drop {A} (n : nat) (ls : list A) : list A
  := match n, ls with
       | 0, _ => ls
       | S n', nil => nil
       | S n', x::xs => drop n' xs
     end.

Fixpoint take {A} (n : nat) (ls : list A) : list A
  := match n, ls with
       | 0, _ => nil
       | _, nil => nil
       | S n', x::xs => x::take n' xs
     end.
