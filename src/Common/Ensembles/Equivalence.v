Require Export Coq.Sets.Ensembles.
Require Import Fiat.Common.

Set Implicit Arguments.

Global Instance Same_set_refl {T} : Reflexive (Same_set T).
Proof.
  repeat (intro || split); auto.
Qed.

Global Instance Same_set_sym {T} : Symmetric (Same_set T).
Proof.
  repeat (intro || split); destruct_head_hnf and; eauto.
Qed.

Global Instance Same_set_trans {T} : Transitive (Same_set T).
Proof.
  repeat (intro || split); destruct_head_hnf and; eauto.
Qed.

Global Instance Included_refl {T} : Reflexive (Included T).
Proof.
  repeat (intro || split); auto.
Qed.

Global Instance Included_trans {T} : Transitive (Included T).
Proof.
  repeat (intro || split); destruct_head_hnf and; eauto.
Qed.
