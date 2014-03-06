Require Import Omega.
Require Export ADT ADTRefinement.Specs ADTRefinement.Pick.

Generalizable All Variables.
Set Implicit Arguments.

Section BinOpSpec.
  (** Specification for comparisions over a collection **)

  Definition multiset := nat -> nat.
  Definition add (s : multiset) (n : nat) : multiset
    := fun m => if eq_nat_dec n m
                then S (s m)
                else s m.

  Global Arguments add s n / m.

  (* Specification for adding an element *)
  Definition add_spec : mutatorMethodSpec multiset nat
    := fun m x m' => forall k, m' k = (add m x) k.

  Arguments add_spec m x m' / .

  Variable opSpec : nat -> nat -> Prop.
  Variable defaultSpec : nat -> Prop.

  (* Specification for calculating op. *)
  (* If the set [m] is empty, the default spec should hold for [n]. *)
  Definition empty_spec (m : multiset) n :=
    defaultSpec n /\ forall n', m n' = 0.

  (* If the set [m] is not empty, [n] is the op-est thing in [m] *)
  Definition nonempty_spec (m : multiset) n :=
    m n > 0 /\ forall n', m n' > 0 -> opSpec n n'.

  (* The observer must satisfy one of the above two behaviors,
     depending on whether the set is empty or not. *)
  Definition bin_op_spec
  : observerMethodSpec multiset nat nat
    := fun m _ n => empty_spec m n \/ nonempty_spec m n .

  Arguments empty_spec m n / .
  Arguments nonempty_spec m n / .
  Arguments bin_op_spec / .

  Definition NatBinOpSig : ADTSig :=
    {| MutatorIndex := unit;
       ObserverIndex := unit;
       MutatorDom idx := nat;
       ObserverDom idx := nat;
       ObserverCod idx := nat
    |}.

  Definition NatBinOpSpec
  : ADT NatBinOpSig
    := pickImpl NatBinOpSig
                (fun _ => add_spec)
                (fun _ => bin_op_spec).

End BinOpSpec.

Definition NatLower : ADT NatBinOpSig
  := NatBinOpSpec le (fun n => True).  (* Spec for collection with lower bound. *)

Definition NatUpper
: ADT NatBinOpSig := NatBinOpSpec ge (fun n => True).  (* Spec for collection with upper bound. *)
