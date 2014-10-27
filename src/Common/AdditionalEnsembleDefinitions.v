(** * Miscellaneous definitions about ensembles *)
Require Import Coq.Lists.List.
Require Export Coq.Sets.Ensembles.

Definition EnsembleListEquivalence
           {A}
           (ensemble : Ensemble A)
           (seq : list A) :=
  NoDup seq /\
  forall x, Ensembles.In _ ensemble x <-> List.In x seq.

(** Coq's [cardinal] is stupid, and not total.  For example, it
    requires [Extensionality_Ensembles] to prove [cardinal _ (fun _ =>
    False) 0].  So we define a better one. *)
Definition cardinal U (A : Ensemble U) (n : nat) : Prop :=
  exists ls, EnsembleListEquivalence A ls /\ Datatypes.length ls = n.
(** To mimic the arguments of the built-in [cardinal]. *)
Arguments cardinal : clear implicits.
