Require Import Examples.BinaryOperationSpec.

Section BinOpImpl.
  (* Implementation of comparisions over a collection implemented as a list. *)

  Require Import List.

  Variable op : nat -> nat -> nat.
  Variable defaultValue : nat.

  Definition add_impl : mutatorMethodType (list nat) nat
    := fun m x => ret (x :: m).

  Arguments add_impl / .

  Definition bin_op_impl : observerMethodType (list nat) nat nat
    := fun m _ => ret (match m with
                    | [] => defaultValue  (* Only return default if collection is empty *)
                    | a :: m' => (fold_left op m' a)
                  end).

  Arguments bin_op_impl / .

  Program Definition NatBinOpImpl
  : ADT NatBinOpSig
    := {| Rep := list nat;
          MutatorMethods idx := add_impl;
          ObserverMethods idx := bin_op_impl
       |}.

End BinOpImpl.
