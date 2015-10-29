Require Import CertifiedExtraction.FMapUtils.
Require Export Bedrock.Memory Bedrock.Platform.Facade.DFacade.
Require Export Bedrock.Platform.Cito.StringMap Bedrock.Platform.Cito.StringMapFacts.

Module Export MoreStringMapFacts := WMoreFacts_fun (StringMap.E) (StringMap).

Notation "A ∉ B" := (not (StringMap.In A B)) (at level 10, no associativity).
Notation "A ∈ B" := (StringMap.In A B) (at level 10, no associativity).
Notation "∅" := (StringMap.empty _).

Notation "[ k <-- v ] :: m" :=
  (StringMap.add k v m) (at level 21, right associativity, arguments at next level) : map_scope.

Global Open Scope map_scope.

Lemma urgh : (subrelation eq (Basics.flip Basics.impl)).
Proof.
  repeat red; intros; subst; assumption.
Qed.

(* FIXME: Why is this needed? *)
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

Ltac rewriteP hyp := first [rewrite hyp | setoid_rewrite hyp].
Ltac rewriteP_in hyp target := first [rewrite hyp in target | setoid_rewrite hyp in target].

Ltac rewrite_equalities :=
  match goal with
  | _ => progress subst
  | [ H: Some _ = Some _ |- _ ] => inversion H; subst; clear H

  | [ H: ?a = ?b |- context[?a] ] => rewrite H
  | [ H: ?a = ?b, H': context[?a] |- _ ] => rewrite H in H'

  | [ H: StringMap.Equal ?a ?b |- context[?a] ] => rewriteP H
  | [ H: StringMap.Equal ?a ?b, H': context[?a] |- _ ] => rewriteP_in H H'

  | [ H: forall (k : StringMap.key) (v : _), StringMap.MapsTo k (ADT v) ?y <-> StringMap.MapsTo k (ADT v) ?y'
      |- context[StringMap.MapsTo _ (ADT _) ?y] ] => rewriteP H
  | [ H: forall (k : StringMap.key) (v : _), StringMap.MapsTo k (ADT v) ?y <-> StringMap.MapsTo k (ADT v) ?y',
      H': context[StringMap.MapsTo _ (ADT _) ?y] |- _ ] => rewriteP_in H H'
  end.
