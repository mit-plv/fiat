Require Import Coq.Strings.String Coq.NArith.NArith.

(* Basic block labels *)
Inductive label' :=
| Global : string -> label'
| Local : N -> label'.

(* An overall label is a pair of a module name and a sub-label. *)
Definition label := prod string label'.
