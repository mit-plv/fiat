(** Depend on the compatibility file, so when we switch versions of Coq, all the relevant notations files get rebuilt. *)
Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Global Set Asymmetric Patterns.

Reserved Infix "∪" (at level 60, right associativity).
Reserved Infix "∩" (at level 60, right associativity).
Reserved Infix "\" (at level 50, left associativity).
Reserved Infix "≅" (at level 70, right associativity).
Reserved Infix "∈" (at level 40, no associativity).
Reserved Notation "{{ x }}".
Reserved Notation "∅".
