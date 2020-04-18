Require Import CertifiedExtraction.FMapUtils.
Require Export Bedrock.Memory Bedrock.Platform.Facade.DFacade.
Require Export Bedrock.Platform.Cito.StringMap Bedrock.Platform.Cito.StringMapFacts.

Module Export MoreStringMapFacts := WMoreFacts_fun (StringMap.E) (StringMap).

Global Open Scope map_scope.

Lemma urgh : (subrelation eq (Basics.flip Basics.impl)).
Proof.
  repeat red; intros; subst; assumption.
Qed.

(* NOTE: Why is this needed? *)
Hint Resolve urgh : typeclass_instances.

(* Lemma Bug: *)
(*   forall k1 k2 (st: StringMap.t nat) (x : nat), *)
(*     StringMap.MapsTo k1 x st -> *)
(*     match StringMap.find k2 (StringMap.add k2 x (StringMap.add k1 x st)) with *)
(*     | Some _ => True *)
(*     | None => True *)
(*     end. *)
(* Proof. *)
(*   intros ** H. *)
(*   setoid_rewrite <- (StringMapUtils.add_redundant_cancel H). *)
(*   (* Inifinite loop unless `urgh' is added as a hint *) *)
(* Abort. *)

Require Import Coq.Setoids.Setoid.

Add Parametric Morphism {av} : (@StringMap.find av)
    with signature (eq ==> StringMap.Equal ==> eq)
      as find_Morphism.
Proof.
  intros; erewrite find_m; intuition.
Qed.
