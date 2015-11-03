Require Import
        Computation.Core.
Require Export
        CertifiedExtraction.Core
        CertifiedExtraction.CompUtils
        CertifiedExtraction.HintDBs.
Require Import
        Bedrock.Memory
        Bedrock.Platform.Facade.DFacade.

Transparent computes_to.

(* FIXME this is a special case of below, and should be removed *)

(* Lemma computes_to_match_SCA: *)
(*   forall (av : Type) (compA : Comp W) (v0 : W), *)
(*     compA ↝ v0 -> *)
(*     (fun a : Value av => *)
(*        match a with *)
(*        | SCA aa => compA aa *)
(*        | ADT _ => False *)
(*        end) ↝ SCA av v0. *)
(* Proof. *)
(*   trivial. *)
(* Qed. *)

(* Hint Resolve computes_to_match_SCA : SameValues_Fiat_db. *)

(* Lemma computes_to_match_SCA_inv: *)
(*   forall av (compA : Comp W) x, *)
(*     (fun a : Value av => *)
(*        match a with *)
(*        | SCA aa => compA aa *)
(*        | ADT _ => False *)
(*        end) ↝ x -> *)
(*     exists xx, x = SCA av xx /\ compA xx. *)
(* Proof. *)
(*   intros; destruct x; compute in H; intuition eauto. *)
(* Qed. *)

(* (* </FIXME> *) *)

(* Lemma computes_to_WrapComp_Generic: *)
(*   forall `{FacadeWrapper (Value av) A} (compA : Comp A) (v0 : A) (H : compA ↝ v0), *)
(*     WrapComp_Generic compA ↝ (wrap v0). *)
(* Proof. *)
(*   unfold WrapComp_Generic, computes_to; simpl; intros. *)
(*   rewrite unwrap_wrap. *)
(*   trivial. *)
(* Qed. *)

(* Hint Resolve computes_to_WrapComp_Generic : SameValues_Fiat_db. *)

(* Lemma computes_to_WrapComp_Generic_inv: *)
(*   forall `{FacadeWrapper (Value av) A} (compA : Comp A) x, *)
(*     WrapComp_Generic compA ↝ x -> *)
(*     exists xx, unwrap x = Some xx /\ compA ↝ xx. *)
(* Proof. *)
(*   unfold WrapComp_Generic, computes_to; simpl; intros. *)
(*   destruct (unwrap x) eqn:eq0; intuition eauto. *)
(* Qed. *)

(* Opaque computes_to. *)

Lemma AlwaysComputesToSCA_ret_SCA:
  forall (av : Type) (v : W), AlwaysComputesToSCA (ret (SCA av v)).
Proof.
  red; intros; computes_to_inv; subst; reflexivity.
Qed.

Hint Resolve AlwaysComputesToSCA_ret_SCA : SameValues_db.

(* Lemma AlwaysComputesToSCA_WrapComp_W {av} (cmp: Comp W) : *)
(*   AlwaysComputesToSCA (@WrapComp_W av cmp). *)
(* Proof. *)
(*   Transparent computes_to. *)
(*   red; unfold WrapComp_W, computes_to; intros. *)
(*   destruct vv; simpl; (reflexivity || (exfalso; assumption)). *)
(* Qed. *)

(* Lemma WrapComp_W_computes_to {av} {cmp: Comp W} {v: Value av} : *)
(*   WrapComp_W cmp ↝ v -> *)
(*   { v' | cmp ↝ v' /\ v = SCA _ v' }. *)
(* Proof. *)
(*   intros; destruct v. *)
(*   - exists w; intuition congruence. *)
(*   - exfalso; assumption. *)
(* Qed. *)

(* Lemma WrapComp_W_rewrite: *)
(*   forall (av : Type) (w : Word.word 32), *)
(*     Monad.equiv (WrapComp_W (ret w)) (ret (SCA av w)). *)
(* Proof. *)
(*   unfold WrapComp_W; unfold Monad.equiv. (* SameValues_Fiat_t; *) *)
(*   repeat match goal with *)
(*          | _ => progress subst *)
(*          | _ => progress split *)
(*          | _ => progress intros *)
(*          | _ => progress computes_to_inv *)
(*          | [ H: exists x, _ |- _ ] => destruct H *)
(*          | [ H: _ /\ _ |- _ ] => destruct H *)
(*          | [ H: _ |- _ ] => apply computes_to_match_SCA_inv in H *)
(*          end. *)
(* Qed. *)
