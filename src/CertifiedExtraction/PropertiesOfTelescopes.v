Require Import
        Coq.Classes.Morphisms
        CertifiedExtraction.Core
        CertifiedExtraction.Utils.

Definition TelEq {A} ext (T1 T2: Telescope A) :=
  forall st, st ≲ T1 ∪ ext <->
        st ≲ T2 ∪ ext.

Definition PointWise_TelEq {av T} ext v t1 t2 :=
  forall vv: T, v ↝ vv -> @TelEq av ext (t1 vv) (t2 vv).

Ltac TelEq_rel_t :=
  red; unfold TelEq; intuition;
  repeat match goal with
         | [ H: forall _, _ <-> _ |- _ ] => rewrite H
         | [ H: forall _, _ <-> _, H': _ |- _ ] => rewrite H in H'
         | _ => solve [intuition]
         end.

Require Import Coq.Setoids.Setoid.

Lemma TelEq_refl {A ext}:
  Reflexive (@TelEq A ext).
Proof.
  TelEq_rel_t.
Qed.

Lemma TelEq_sym {A ext}:
  Symmetric (@TelEq A ext).
Proof.
  TelEq_rel_t.
Qed.

Lemma TelEq_trans {A ext}:
  Transitive (@TelEq A ext).
Proof.
  TelEq_rel_t.
Qed.

Add Parametric Relation {A} ext : _ (@TelEq A ext)
    reflexivity proved by TelEq_refl
    symmetry proved by TelEq_sym
    transitivity proved by TelEq_trans
      as TelEqRel.

Add Parametric Morphism {A} ext : (@SameValues A ext)
    with signature (eq ==> (TelEq ext) ==> iff)
      as SameValues_TelEq_morphism.
Proof.
  TelEq_rel_t.
Qed.

Fixpoint NotInTelescope {av} k (tenv: Telescope av) :=
  match tenv with
  | Nil => True
  | Cons _ key val tail => Some k <> (NameTagAsStringOption key) /\ (forall v, val ↝ v -> NotInTelescope k (tail v))
  end.

Lemma NotInTelescope_not_eq_head:
  forall `{FacadeWrapper (Value av) A} (key : string) (val : Comp A)
    (tail : A -> Telescope av) (var : StringMap.key),
    NotInTelescope var ([[` key ~~> val as kk]]::tail kk) ->
    key <> var.
Proof.
  simpl; intros; repeat cleanup; eauto.
Qed.

Lemma NotInTelescope_not_in_tail:
  forall {av A} s (val : Comp A)
    (tail : A -> Telescope av) (var : StringMap.key)
    (v : A),
    val ↝ v ->
    NotInTelescope var ([[ s ~~> val as kk]]::tail kk) ->
    NotInTelescope var (tail v).
Proof.
  simpl; intros.
  intuition eauto.
Qed.

Ltac decide_NotInTelescope :=
  progress repeat match goal with
                  | _ => cleanup
                  | _ => congruence
                  | [  |- NotInTelescope _ Nil ] => reflexivity
                  | [  |- NotInTelescope ?k (Cons _ _ _) ] => unfold NotInTelescope; fold @NotInTelescope
                  end.

Fixpoint DropName {A} k (t: Telescope A) :=
  match t with
  | Nil => Nil
  | Cons T key val tail => Cons (match key with
                                | NTSome _key H => if string_dec _key k then NTNone else key
                                | NTNone => key
                                end) val (fun v => (DropName k (tail v)))
  end.

Definition LiftPropertyToTelescope {av} ext (property: _ -> Prop) : Telescope av -> Prop :=
  fun tenv => forall st, st ≲ tenv ∪ ext -> property st.

Definition Lifted_not_mapsto_adt {av} ext tenv k :=
  @LiftPropertyToTelescope av ext (fun map => not_mapsto_adt k map = true) tenv.

Definition Lifted_MapsTo {av} ext tenv k v :=
  @LiftPropertyToTelescope av ext (StringMap.MapsTo k v) tenv.

Definition Lifted_is_true {av} ext tenv test :=
  @LiftPropertyToTelescope av ext (fun st => is_true st test) tenv.

Definition Lifted_is_false {av} ext tenv test :=
  @LiftPropertyToTelescope av ext (fun st => is_false st test) tenv.

Ltac LiftPropertyToTelescope_t :=
  match goal with
  | [ H: LiftPropertyToTelescope ?ext _ ?tenv, H': ?st ≲ ?tenv ∪ ?ext |- _ ] => learn (H st H')
  | [ H: context[@Lifted_not_mapsto_adt] |- _ ] => unfold Lifted_not_mapsto_adt in H
  | [ H: context[@Lifted_MapsTo] |- _ ] => unfold Lifted_MapsTo in H
  | [ H: context[@Lifted_is_true] |- _ ] => unfold Lifted_is_true in H
  | [ H: context[@Lifted_is_false] |- _ ] => unfold Lifted_is_false in H
  end.

Ltac Lift_morphism_t :=
  match goal with
  | _ => cleanup
  | [ H: forall _, _ -> _, H': _ |- _ ] => learn (H _ H')
  | [ H: forall _, _ <-> _ |- _ ] => rewrite H
  | [ H: forall _, _ <-> _, H': _ |- _ ] => setoid_rewrite H in H'
  end.

Add Parametric Morphism {A} ext : (@LiftPropertyToTelescope A ext)
    with signature (pointwise_relation _ iff ==> TelEq ext ==> iff)
      as LiftPropertyToTelescope_TelEq_morphism.
Proof.
  unfold LiftPropertyToTelescope, pointwise_relation;
  repeat match goal with
         | _ => Lift_morphism_t
         | [ H': TelEq ?ext ?t1 _ |- context[_ ≲ ?t1 ∪ ?ext] ]        => setoid_rewrite H'
         | [ H': TelEq ?ext ?t1 _,  H: context[_ ≲ ?t1 ∪ ?ext] |- _ ] => setoid_rewrite H' in H
         end.
Qed.

Add Parametric Morphism {A} ext : (@Lifted_not_mapsto_adt A ext)
    with signature (TelEq ext ==> eq ==> iff)
      as Lifted_not_mapsto_adt_TelEq_morphism.
Proof.
  eauto using LiftPropertyToTelescope_TelEq_morphism with typeclass_instances.
Qed.

Add Parametric Morphism {A} ext : (@Lifted_MapsTo A ext)
    with signature (TelEq ext ==> eq ==> eq ==> iff)
      as Lifted_MapsTo_TelEq_morphism.
Proof.
  eauto using LiftPropertyToTelescope_TelEq_morphism with typeclass_instances.
Qed.

Add Parametric Morphism {A} ext : (@Lifted_is_true A ext)
    with signature (TelEq ext ==> eq ==> iff)
      as Lifted_is_true_TelEq_morphism.
Proof.
  eauto using LiftPropertyToTelescope_TelEq_morphism with typeclass_instances.
Qed.

Add Parametric Morphism {A} ext : (@Lifted_is_false A ext)
    with signature (TelEq ext ==> eq ==> iff)
      as Lifted_is_false_TelEq_morphism.
Proof.
  eauto using LiftPropertyToTelescope_TelEq_morphism with typeclass_instances.
Qed.

Inductive TelStrongEq {av} : (Telescope av) -> (Telescope av) -> Prop :=
| StrongEqNil : TelStrongEq Nil Nil
| StrongEqCons : forall {A} k (v1 v2: Comp A) t1 t2,
    Monad.equiv v1 v2 ->
    (forall vv, v1 ↝ vv -> TelStrongEq (t1 vv) (t2 vv)) ->
    TelStrongEq (@Cons av A k v1 t1) (@Cons av A k v2 t2).

Ltac inversion' H :=
  inversion H; subst; clear H.

Require Import Eqdep.

Ltac TelStrongEq_t :=
  match goal with
  | [ H: Monad.equiv ?b _ |- ?b ↝ ?B ] => apply (proj2 (H B))
  | [ H: Monad.equiv ?a _, H': ?a ↝ _ |- _ ] => learn (proj1 (H _) H')
  | [ H: Monad.equiv _ ?a, H': ?a ↝ _ |- _ ] => learn (proj2 (H _) H')
  | [ H: TelStrongEq _ _ |- _ ] => first [ inversion' H; fail | inversion' H; [idtac] ]
  | [ H: existT ?P ?x _ = existT ?P ?x _ |- _ ] => apply inj_pair2 in H; subst
  end.

Ltac TelStrongEq_morphism_t :=
  repeat match goal with
         | _ => constructor
         | _ => progress intros
         | _ => TelStrongEq_t
         | _ => eauto with typeclass_instances
         end.

Lemma TelStrongEq_refl {A} :
  Reflexive (@TelStrongEq A).
Proof.
  red; intros tel; induction tel; TelStrongEq_morphism_t.
Qed.

Lemma TelStrongEq_sym {A} :
  Symmetric (@TelStrongEq A).
Proof.
  red; intros tel tel' eq; induction eq;
  TelStrongEq_morphism_t.
Qed.

(* Fixpoint Telescope_code {av} (t1 t2: Telescope av) : Prop := *)
(*   match t1, t2 with *)
(*   | Nil, Nil => True *)
(*   | Nil, _ => False *)
(*   | _, Nil => False *)
(*   | Cons T H key val tail, Cons T' H' key' val' tail' =>  *)
(*     exists (eqT: T = T'), (match eqT in _ = T' return FacadeWrapper _ T' *)
(*                       with eq_refl => H end = H') /\ key = key' *)
(*                      /\ Monad.equiv (match eqT in _ = T' return Comp T' *)
(*                                     with eq_refl => val end) val' *)
(*                      /\ (forall vv, val ↝ vv -> Telescope_code (tail vv) *)
(*                                                         (tail' (match eqT in _ = T' return T' *)
(*                                                                 with eq_refl => vv end))) *)
(*   end. *)

Lemma TelStrongEq_trans {A} :
  Transitive (@TelStrongEq A).
Proof.
  red; intros tel; induction tel;
    TelStrongEq_morphism_t.
Qed.

Add Parametric Relation {A} : _ (@TelStrongEq A)
    reflexivity proved by TelStrongEq_refl
    symmetry proved by TelStrongEq_sym
    transitivity proved by TelStrongEq_trans
      as TelStrongEqRel.

Add Parametric Morphism {av T} : (@Cons av T)
    with signature (eq ==> Monad.equiv ==> pointwise_relation _ (TelStrongEq) ==> (TelStrongEq))
      as Cons_MonadEquiv_TelStrongEq_morphism.
Proof.
  unfold pointwise_relation; intros.
  constructor; eauto.
Qed.

Lemma Propagate_ret :
  forall {av A} k (v: A) (tail: A -> Telescope av),
    TelStrongEq
      (Cons k (ret v) tail)
      (Cons k (ret v) (fun _ => tail v)).
Proof.
  constructor.
  - reflexivity.
  - intros; computes_to_inv; subst; reflexivity.
Qed.

