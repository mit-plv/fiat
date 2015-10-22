(* Require Import Bedrock.Platform.Facade.Examples.FiatADTs. *)
(* Require Export Bedrock.Platform.Facade.Notations. *)
Require Export Bedrock.Platform.Cito.StringMap Bedrock.Platform.Cito.StringMapFacts Bedrock.Platform.Cito.SyntaxExpr Bedrock.Memory.
Require Export Bedrock.Platform.Facade.DFacade.

Require Import Computation.Core.
Require Import ADTRefinement.
Require Import ADTRefinement.GeneralRefinements.

Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Import Coq.Program.Program Coq.Lists.List.

Require Import Coq.Strings.String.
Local Open Scope string.

Require Import CertifiedExtraction.Utils.
Require Import CertifiedExtraction.FMapUtils.

Module StringMapUtils := WUtils_fun (StringMap.E) (StringMap).

Inductive Telescope av : Type :=
| Nil : Telescope av
| Cons : forall (key: option string)
           (val: Comp (Value av))
           (tail: Value av -> Telescope av),
    Telescope av.

Arguments Nil {av}.

Definition SameADTs {av} m1 m2 :=
  (forall k v, StringMap.MapsTo k (@ADT av v) m1 <-> StringMap.MapsTo k (@ADT av v) m2).

Definition SameSCAs {av} m1 m2 :=
  (forall k v, StringMap.MapsTo k (@SCA av v) m1 -> StringMap.MapsTo k (@SCA av v) m2).

Definition WeakEq {av} m1 m2 :=
  @SameADTs av m1 m2 /\ @SameSCAs av m1 m2.

Fixpoint SameValues {av} ext fmap (tenv: Telescope av) :=
  match tenv with
  | Nil => WeakEq ext fmap
  | Cons key val tail =>
    match key with
      | Some k => match StringMap.find k fmap with
                 | Some v => val ↝ v /\ SameValues ext (StringMap.remove k fmap) (tail v)
                 | None => False
                 end
      | None => exists v', val ↝ v' /\ SameValues ext fmap (tail v')
    end
  end.

Notation "ENV ≲ TENV ∪ EXT" := (SameValues EXT ENV TENV) (at level 50).

Definition ProgOk {av} ext env prog (initial_tstate final_tstate: Telescope av) :=
  forall initial_state: State av,
    (initial_state ≲ initial_tstate ∪ ext) ->
    Safe env prog initial_state /\
    forall final_state: State av,
      @RunsTo _ env prog initial_state final_state ->
      (final_state ≲ final_tstate ∪ ext).

(* Arguments Scope ProgOk [type_scope _ facade_scope _ _ _ _]. *)

(* Require Export ADTSynthesis.Computation.Core ADTSynthesis.Common. *)

Notation "{{ A }} P {{ B }} ∪ {{ ext }} // EV" :=
  (ProgOk ext EV P A B)
    (at level 60, format "'[v' '{{'  A  '}}' '/'    P '/' '{{'  B  '}}'  ∪  '{{'  ext  '}}'  //  EV ']'").

Check (forall (av : Type) vars (ev : Env av) (p : Stmt) (a b : Telescope av)
  (ext : StringMap.t (Value av)), {{ a }} p {{ b }} ∪ {{ext}} // ev).

Notation "A ∉ B" := (not (StringMap.In A B)) (at level 10, no associativity).
Notation "A ∈ B" := (StringMap.In A B) (at level 10, no associativity).

Ltac exact_after_rewrite :=
  match goal with
  | [ H: ?rel ?a ?b, H': context f [?a] |- context f [?b] ] => rewrite <- H; exact H'
  | [ H: ?rel ?a ?b, H': context f [?b] |- context f [?a] ] => rewrite H; exact H'
  end.

Ltac destruct_find k s :=
  let eq0 := fresh "eqn" in
  destruct (StringMap.find k s) eqn:eq0;
    [ rewrite <- StringMapFacts.find_mapsto_iff in eq0 |
      rewrite <- StringMapFacts.not_find_in_iff in eq0 ];
    simpl in *.

Ltac destruct_finds :=
  repeat lazymatch goal with
| [ H: context[StringMap.find ?k ?s] |- _ ] => destruct_find k s
| [ |- context[StringMap.find ?k ?s]      ] => destruct_find k s
end.

Open Scope comp.

Notation "[ k <-- v ] :: m" :=
  (StringMap.add k v m) (at level 21, right associativity, arguments at next level) : map_scope.

Local Open Scope map_scope.

Lemma Some_inj : forall A x y, @Some A x = @Some A y <-> x = y.
Proof.
  split; inversion 1; eauto.
Qed.

Ltac rewrite_trivial x y op :=
  let h := fresh in
  assert (op x y) as h by tauto;
    rewrite h; clear h.

Ltac rewrite_trivial_in x y op target :=
  let h := fresh in
  assert (op x y) as h by tauto;
    rewrite h in target; clear h.

(*
Ltac deep_simpl := (* TODO use autorewrite for this *)
  repeat match goal with
         | [ H: context[?a = ?a] |- _ ]              => rewrite_trivial_in (a = a) True iff H
         | [ |- context[?a = ?a] ]                   => rewrite_trivial (a = a) True iff
         | [ H: context[True /\ ?a] |- _ ]               => rewrite_trivial_in (True /\ a) a iff H
         | [ |- context[True /\ ?a] ]                    => rewrite_trivial (True /\ a) a iff
         | [ H: context[True \/ ?a] |- _ ]               => rewrite_trivial_in (True \/ a) True iff H
         | [ |- context[True \/ ?a] ]                    => rewrite_trivial (True \/ a) True iff
         | [ H: context[not True] |- _ ]                => rewrite_trivial_in (not True) False iff H
         | [ |- context[not True] ]                     => rewrite_trivial (not True) False iff
         | [ H0: ?x, H: context[?x] |- _ ]            => rewrite_trivial_in x True iff H
         | [ H0: not ?x, H: context[?x] |- _ ]        => rewrite_trivial_in x False iff H
         | [ |- context[not True] ]                     => rewrite_trivial (not True) False iff
         | [ H: context[False /\ ?a] |- _ ]               => rewrite_trivial_in (False /\ a) False iff H
         | [ |- context[False /\ ?a] ]                    => rewrite_trivial (False /\ a) False iff
         | [ H: context[?a \/ False] |- _ ]               => rewrite_trivial_in (a \/ False) a iff H
         | [ |- context[?a \/ False] ]                    => rewrite_trivial (a \/ False) a iff
         | [ H: context[False \/ ?a] |- _ ]               => rewrite_trivial_in (False \/ a) a iff H
         | [ |- context[False \/ ?a] ]                    => rewrite_trivial (False \/ a) a iff
         | [ H: ?a <> ?b, H': context[?a <> ?b] |- _ ] => rewrite_trivial_in (a <> b) True iff H'
         | [ H: ?a <> ?b |- context[?a <> ?b] ]        => rewrite_trivial (a <> b) True iff
         | [ H: ?a <> ?b, H': context[?a = ?b] |- _ ] => rewrite_trivial_in (a = b) False iff H'
         | [ H: ?a <> ?b |- context[?a = ?b] ]        => rewrite_trivial (a = b) False iff
         end.
 *)

Lemma SameValues_MapsTo:
  forall {av} (key : String.string) (value : Comp (Value av))
    (tail : Value av -> Telescope av)
    (ext state : StringMap.t (Value av)),
    state ≲ Cons (Some key) value tail ∪ ext ->
    exists v : Value av, value ↝ v /\ StringMap.MapsTo key v state.
Proof.
  simpl; intros.
  destruct (StringMap.find _ _) eqn: eq0; try tauto.
  rewrite <- find_mapsto_iff in *.
  eexists; intuition eauto.
Qed.

Ltac step :=
  match goal with
  | _ => progress intros; simpl in *
  | _ => progress split
  | [ H: ?a /\ ?b |- _ ] => destruct H
  | [ H: StringMap.MapsTo ?k ?v ?m |- Some ?v = StringMap.find ?k ?m ] => symmetry; rewrite <- find_mapsto_iff; assumption
  | [ H: StringMap.MapsTo ?k ?v ?m |- context[StringMap.find ?k ?m] ] => replace (StringMap.find k m) with (Some v) in *
  | [ H: context[match StringMap.find ?k ?m with | Some _ => _ | None => _ end] |- _ ] => let eq0 := fresh in progress (destruct (StringMap.find k m) eqn:eq0; deduplicate)
  | [ H: ret _ ↝ _ |- _ ] => inversion H; clear H; subst
  | _ => solve [intuition eauto]
  end.

Ltac t :=
  repeat step.

Lemma SameValues_MapsTo_ret:
  forall {av}
    (key : String.string) (value : Comp (Value av))
    (tail : Value av -> Telescope av)
    (ext state : StringMap.t (Value av)) (x : Value av),
    StringMap.MapsTo key x state ->
    state ≲ Cons (Some key) value tail ∪ ext ->
    state ≲ Cons (Some key) (ret x) tail ∪ ext.
Proof. t. Qed.

Lemma SameValues_MapsTo_ret_inv:
  forall {av}
    (key : String.string) (value : Comp (Value av))
    (tail : Value av -> Telescope av)
    (ext state : StringMap.t (Value av)) (x : Value av),
    value ↝ x ->
    state ≲ Cons (Some key) (ret x) tail ∪ ext ->
    state ≲ Cons (Some key) value tail ∪ ext.
Proof. t. Qed.

Lemma SameValues_MapsTo_ret_ex:
  forall {av}
    (key : String.string) (value : Comp (Value av))
    (tail : Value av -> Telescope av)
    (ext state : StringMap.t (Value av)),
    state ≲ Cons (Some key) value tail ∪ ext ->
    exists v, value ↝ v /\ state ≲ Cons (Some key) (ret v) tail ∪ ext.
Proof. t. Qed.

Example ProkOk_specialize_to_ret :
  forall {av} env key value prog
    (tail1: Value av -> Telescope av)
    (tail2: Value av -> Telescope av)
    ext,
    (forall v, value ↝ v -> {{ Cons (Some key) (ret v) tail1 }} prog {{ Cons (Some key) (ret v) tail2 }} ∪ {{ ext }} // env) ->
    ({{ Cons (Some key) value tail1 }} prog {{ Cons (Some key) value tail2 }} ∪ {{ ext }} // env).
Proof.
  repeat match goal with
         | _ => progress intros
         | [  |- ?a /\ ?b] => split
         | [ H: ?a /\ ?b |- _ ] => destruct H
         | [ |- context[@ProgOk] ] =>
           let h := fresh "init_equiv" in
           intros ? h; destruct (SameValues_MapsTo_ret_ex _ _ _ _ _ h) as (? & ? & ?)
         | [ H: ?st ≲ _ ∪ _, H': forall v, ?val ↝ v -> _, H'': ?val ↝ ?x |- _ ] => progress (destruct (H' x H'' st H); deduplicate)
         | _ => intuition eauto using SameValues_MapsTo_ret_inv
         end.
Qed.

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

Lemma Some_neq :
  forall A (x y: A),
    Some x <> Some y <-> x <> y.
Proof.
  split; red; intros ** H; subst; try inversion H; intuition eauto.
Qed.

Ltac cleanup :=
  match goal with
  | _ => tauto
  | _ => discriminate
  | _ => progress intros
  | _ => progress computes_to_inv
  | [ |- ?a <-> ?b ] => split
  | [  |- ?a /\ ?b ] => split
  | [ H: ?a /\ ?b |- _ ] => destruct H
  | [ H: exists _, _ |- _ ] => destruct H
  | [ H: Some _ <> Some _ |- _ ] => rewrite Some_neq in H
  end.

Ltac t_SameValues_Morphism :=
  repeat match goal with
         | _ => progress intros
         | _ => progress split
         | _ => progress simpl in *
         | [ H: StringMap.Equal ?m1 ?m2, H': StringMap.Equal ?m1 ?ext |- StringMap.Equal ?m2 ?ext ] =>
           symmetry in H
         | [ H: match ?k with _ => _ end |- match ?k with _ => _ end ] => destruct k
         | [ H: match StringMap.find ?k ?m1 with _ => _ end, H': StringMap.Equal ?m1 ?m2 |-
             match StringMap.find ?k ?m2 with _ => _ end ] => rewrite <- H'
         | [ IH: _, H: StringMap.remove ?k ?m1 ≲ (?t ?v) ∪ ?ext, H': StringMap.Equal ?m1 ?m2 |-
             StringMap.remove ?k ?m2 ≲ (?t ?v) ∪ ?ext ] => rewrite (IH v m1 m2 _ H')
         | [ IH: _, H: StringMap.remove ?k ?m1 ≲ (?t ?v) ∪ ?ext, H': StringMap.Equal ?m1 ?m2 |-
             StringMap.remove ?k ?m2 ≲ (?t ?v) ∪ ?ext ] => apply (IH _ _ _ _ (remove_m eq_refl H')); exact H
         | [ H: exists v, _ |- exists v, _ ] => destruct H; eexists
         | _ => progress (intuition eauto)
         end.

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

Ltac t_Morphism_step :=
  match goal with
  | _ => cleanup
  | _ => rewrite_equalities

  | [ |- context[?m ≲ Nil ∪ ?ext] ] => simpl
  | [ H: context[?m ≲ Nil ∪ ?ext] |- _ ] => simpl in H

  | [ |- context[?m ≲ Cons ?k ?v ?t ∪ ?ext] ] => let h := fresh in destruct k eqn:h; simpl
  | [ H: context[?m ≲ Cons ?k ?v ?t ∪ ?ext] |- _ ] => let h := fresh in destruct k eqn:h; simpl in H

  | [ |- context[match StringMap.find ?k ?m with _ => _ end] ] => let h := fresh in destruct (StringMap.find k m) eqn:h; simpl
  | [ H: context[match StringMap.find ?k ?m with _ => _ end] |- _ ] => let h := fresh in destruct (StringMap.find k m) eqn:h; simpl in H

  | [ H: exists v, _ |- exists v, _ ] => destruct H; eexists
  end.

Ltac t_Morphism := repeat t_Morphism_step.

Add Parametric Morphism {av} : (@StringMap.find av)
    with signature (eq ==> StringMap.Equal ==> eq)
      as find_Morphism.
Proof.
  intros; erewrite find_m; intuition.
Qed.

Add Parametric Morphism {av} : (@SameADTs av)
    with signature (StringMap.Equal ==> StringMap.Equal ==> iff)
      as SameADTs_Morphism.
Proof.
  unfold SameADTs in *; t_Morphism.
Qed.

Add Parametric Morphism {av} : (@SameSCAs av)
    with signature (StringMap.Equal ==> StringMap.Equal ==> Basics.impl)
      as SameSCAs_Morphism.
Proof.
  unfold SameSCAs, Basics.impl in *; t_Morphism; eauto.
Qed.

Add Parametric Morphism {av} : (@WeakEq av)
    with signature (StringMap.Equal ==> StringMap.Equal ==> iff)
      as WeakEq_Morphism.
Proof.
  unfold WeakEq; t_Morphism.
Qed.

Lemma SameValues_Equal :
  forall {av} tenv m1 m2 ext,
    @StringMap.Equal (Value av) m1 m2 ->
    (m1 ≲ tenv ∪ ext ->
     m2 ≲ tenv ∪ ext).
Proof.
  induction tenv as [ | ? ? ? IH ];
  repeat match goal with
         | [ IH: _, H: StringMap.remove ?k ?m1 ≲ (?t ?v) ∪ ?ext, H': StringMap.Equal ?m1 ?m2 |-
             StringMap.remove ?k ?m2 ≲ (?t ?v) ∪ ?ext ] => apply (IH _ _ _ _ (remove_m eq_refl H')); exact H
         | _ => t_Morphism_step
         | _ => eauto
         end.
Qed.

Lemma SameValues_Equal_iff :
  forall {av} tenv m1 m2 ext,
    @StringMap.Equal (Value av) m1 m2 ->
    (m1 ≲ tenv ∪ ext <->
     m2 ≲ tenv ∪ ext).
Proof.
  intros * H; split; [ | symmetry in H ]; eauto using SameValues_Equal.
Qed.

Lemma SameValues_Equal_Ext :
  forall {av} tenv state m1 m2,
    @StringMap.Equal (Value av) m1 m2 ->
    (state ≲ tenv ∪ m1 ->
     state ≲ tenv ∪ m2).
Proof.
  induction tenv as [ | ? ? ? IH ];
  repeat match goal with
  | [ H: forall v st m1 m2, StringMap.Equal m1 m2 -> st ≲ ?tail v ∪ m1 -> st ≲ ?tail v ∪ m2, H': StringMap.Equal ?m1 ?m2,
        H'': ?st ≲ ?tail ?v ∪ (StringMap.add ?k ?v ?m1) |- ?st ≲ ?tail ?v ∪ (StringMap.add ?k ?v ?m2) ] =>
    apply (fun pr => IH v st _ _ pr H'')
  | [  |- StringMap.Equal (StringMap.add ?k ?v ?m1) (StringMap.add ?k ?v ?m2) ] => solve [eauto using add_m, Equal_refl]
  | _ => solve [eauto]
  | _ => t_Morphism_step
  end.
Qed.

Lemma SameValues_Equal_Ext_iff :
  forall {av} tenv state m1 m2,
    @StringMap.Equal (Value av) m1 m2 ->
    (state ≲ tenv ∪ m1 <->
     state ≲ tenv ∪ m2).
Proof.
  intros * H; split; [ | symmetry in H ]; eauto using SameValues_Equal_Ext.
Qed.

Lemma SameADTs_Trans:
  forall (av : Type) (m0 m1 m2 : StringMap.t (Value av)),
    SameADTs m0 m1 -> SameADTs m1 m2 -> SameADTs m0 m2.
Proof.
  unfold SameADTs; t_Morphism.
Qed.

Lemma SameSCAs_Trans:
  forall (av : Type) (m0 m1 m2 : StringMap.t (Value av)),
    SameSCAs m0 m1 -> SameSCAs m1 m2 -> SameSCAs m0 m2.
Proof.
  unfold SameSCAs; t_Morphism; eauto.
Qed.

Lemma WeakEq_Trans:
  forall (av : Type) (m0 m1 m2 : StringMap.t (Value av)),
    WeakEq m0 m1 -> WeakEq m1 m2 -> WeakEq m0 m2.
Proof.
  unfold WeakEq; t_Morphism; eauto using SameSCAs_Trans, SameADTs_Trans.
Qed.

Lemma SameADTs_Refl:
  forall (av : Type) (m : StringMap.t (Value av)),
    SameADTs m m.
Proof.
  unfold SameADTs; t_Morphism.
Qed.

Lemma SameSCAs_Refl:
  forall (av : Type) (m : StringMap.t (Value av)),
    SameSCAs m m.
Proof.
  unfold SameSCAs; t_Morphism; eauto.
Qed.

Lemma WeakEq_Refl:
  forall (av : Type) (m : StringMap.t (Value av)),
    WeakEq m m.
Proof.
  unfold WeakEq; t_Morphism; eauto using SameSCAs_Refl, SameADTs_Refl.
Qed.

Import StringMapUtils.

Ltac t_Same :=
  repeat match goal with
  | [  |- context[StringMap.MapsTo _ _ _] ] => progress map_iff
  | [ H: context[StringMap.MapsTo _ _ _] |- _ ] => progress map_iff_in H
  | [ k: StringMap.key, k': StringMap.key |- _ ] => learn (StringMap.E.eq_dec k k')
  | [ H: { _ } + { _ } |- _ ] => destruct H; subst
  | _ => progress t_Morphism
  | _ => solve [intuition]
  end.

Lemma SameADTs_add:
  forall (av : Type) (m1 m2 : StringMap.t (Value av))
    (s0 : StringMap.key) (v : Value av),
    SameADTs m2 m1 -> SameADTs ([s0 <-- v]::m2) ([s0 <-- v]::m1).
Proof.
  unfold SameADTs; t_Same.
Qed.

Lemma SameSCAs_add:
  forall (av : Type) (m1 m2 : StringMap.t (Value av))
    (s0 : string) (v : Value av),
    SameSCAs m2 m1 -> SameSCAs ([s0 <-- v]::m2) ([s0 <-- v]::m1).
Proof.
  unfold SameSCAs; t_Same.
Qed.

Lemma WeakEq_add:
  forall (av : Type) (m1 m2 : StringMap.t (Value av))
    (s0 : string) (v : Value av),
    WeakEq m2 m1 -> WeakEq ([s0 <-- v]::m2) ([s0 <-- v]::m1).
Proof.
  unfold WeakEq; t_Morphism;
  eauto using SameSCAs_add, SameADTs_add.
Qed.

Lemma SameADTs_remove:
  forall (av : Type) (m1 m2 : StringMap.t (Value av))
    (k : StringMap.key),
    SameADTs m2 m1 -> SameADTs (StringMap.remove k m2) (StringMap.remove k m1).
Proof.
  unfold SameADTs; t_Same.
Qed.

Lemma SameSCAs_remove:
  forall (av : Type) (m1 m2 : StringMap.t (Value av))
    (k : StringMap.key),
    SameSCAs m2 m1 -> SameSCAs (StringMap.remove k m2) (StringMap.remove k m1).
Proof.
  unfold SameSCAs; t_Same.
Qed.

Lemma WeakEq_remove:
  forall (av : Type) (m1 m2 : StringMap.t (Value av))
    (k : StringMap.key),
    WeakEq m2 m1 -> WeakEq (StringMap.remove k m2) (StringMap.remove k m1).
Proof.
  unfold WeakEq; t_Morphism;
  eauto using SameSCAs_remove, SameADTs_remove.
Qed.

Lemma SameValues_WeakEq_Ext :
  forall {av} tenv state m1 m2,
    @WeakEq av m2 m1 ->
    (state ≲ tenv ∪ m1 ->
     state ≲ tenv ∪ m2).
Proof.
  induction tenv as [ | ? ? ? IH ];
  repeat match goal with
         | _ => t_Morphism_step
         | _ => solve [eauto using WeakEq_Trans]
         end.
Qed.

Add Parametric Morphism {av} : (@SameValues av)
    with signature (StringMap.Equal ==> StringMap.Equal ==> eq ==> iff)
      as SameValues_Morphism.
Proof.
  split; intros; subst;
  eapply SameValues_Equal; eauto using Equal_sym;
  eapply SameValues_Equal_Ext; eauto using Equal_sym.
Qed.

Lemma WeakEq_Mapsto_MapsTo:
  forall {av : Type} {key : StringMap.key} {ext st : StringMap.t (Value av)} {v : Value av},
    StringMap.MapsTo key v ext ->
    WeakEq ext st ->
    StringMap.MapsTo key v st.
Proof.
  unfold WeakEq, SameSCAs, SameADTs.
  intros ** v ? ?.
  destruct v; firstorder.
Qed.

Lemma SameADTs_impl {av} {m1 m2} :
  SameADTs m1 m2 ->
  (forall k v, StringMap.MapsTo k (@ADT av v) m1 -> StringMap.MapsTo k (@ADT av v) m2).
Proof.
  unfold SameADTs; firstorder.
Qed.

Lemma SameADTs_impl' {av} {m1 m2} :
  SameADTs m1 m2 ->
  (forall k v, StringMap.MapsTo k (@ADT av v) m2 -> StringMap.MapsTo k (@ADT av v) m1).
Proof.
  unfold SameADTs; firstorder.
Qed.

Lemma SameValues_MapsTo_Ext_State:
  forall {av : Type} {tel: Telescope av} (key : StringMap.key)
    {ext st : StringMap.t (Value av)},
    st ≲ tel ∪ ext ->
    forall v, StringMap.MapsTo key v ext ->
         StringMap.MapsTo key v st.
Proof.
  induction tel;
  repeat match goal with
         | _ => progress intros
         | _ => tauto
         | [ H: ?a /\ ?b |- _ ] => destruct H
         | [ H: _ ≲ Nil ∪ _ |- _ ] => simpl in H
         | [ H: StringMap.Equal ?b ?a, H': StringMap.MapsTo ?k _ _ |- StringMap.MapsTo ?k _ _ ] => rewrite H
         | [ H: ?st ≲ Cons ?key ?val ?tail ∪ ?ext |- _ ] => simpl in H; destruct key
         | [ H: forall a key ext st, st ≲ ?tail a ∪ ext -> _,
             H': ?st ≲ ?tail ?v ∪ ?ext,
             H'': StringMap.MapsTo ?key ?v' _  |- _ ] => specialize (H v key ext st H' v' H'')
         | [ H: StringMap.MapsTo ?k ?v (StringMap.remove _ ?s) |- StringMap.MapsTo ?k ?v ?s ] => solve[eauto using MapsTo_remove]
         | [ H: match StringMap.find ?s ?st with _ => _ end |- _ ] => let a := fresh in destruct (StringMap.find s st) eqn:a
         | [ H: exists v, _ |- _ ] => destruct H
         end; eauto using WeakEq_Mapsto_MapsTo. (*! FIXME why does adding the eauto at the end of the match make things slower? *)
Qed.

Lemma SameValues_MapsTo_Ext_State_add:
  forall {av : Type} {tel: Telescope av} (key : StringMap.key)
    {v} {ext st : StringMap.t (Value av)},
    st ≲ tel ∪ [key <-- v]::ext ->
    StringMap.MapsTo key v st.
Proof.
  intros; eauto using SameValues_MapsTo_Ext_State, StringMap.add_1.
Qed.

Lemma SameValues_In_Ext_State:
  forall {av : Type} {tel: Telescope av} (key : StringMap.key)
    {ext st : StringMap.t (Value av)},
    st ≲ tel ∪ ext ->
    StringMap.In key ext ->
    StringMap.In key st.
Proof.
  intros ** h.
  apply In_MapsTo in h; destruct h.
  eapply MapsTo_In; eauto using SameValues_MapsTo_Ext_State.
Qed.

Lemma SameValues_In_Ext_State_add:
  forall {av : Type} {tel: Telescope av} (key : StringMap.key) v
    {ext st : StringMap.t (Value av)},
    st ≲ tel ∪ [key <-- v]::ext ->
    StringMap.In key st.
Proof.
  intros; eapply MapsTo_In; eauto using SameValues_MapsTo_Ext_State_add.
Qed.

Add Parametric Relation {A} : _ (@WeakEq A)
    reflexivity proved by (@WeakEq_Refl A)
    transitivity proved by (@WeakEq_Trans A)
      as WeakEq_Rel.

(*************************)
(** Telescope notations **)
(*************************)

Notation "[[ k <~~ v 'as' kk ]] :: t" :=
  (Cons k v (fun kk => t)) (at level 21, right associativity, arguments at next level) : map_scope.

Notation "[[ ` k <~~ v 'as' kk ]] :: t" :=
  ([[ Some k <~~ v as kk ]] :: t) (at level 21, right associativity, arguments at next level) : map_scope.

Notation "[[ k <-- v 'as' kk ]] :: t" :=
  ([[ `k <~~ (ret v) as kk ]] :: t) (at level 21, right associativity, arguments at next level) : map_scope.

Notation "[[ v 'as' kk ]] :: t" :=
  ([[ None <~~ v as kk ]] :: t) (at level 21, right associativity, arguments at next level) : map_scope.

Create HintDb SameValues_Fiat_db discriminated.

Lemma computes_to_match_SCA:
  forall (av : Type) (compA : Comp W) (v0 : W),
    compA ↝ v0 ->
    (fun a : Value av =>
       match a with
       | SCA aa => compA aa
       | ADT _ => False
       end) ↝ SCA av v0.
Proof.
  trivial.
Qed.
Hint Resolve computes_to_match_SCA : SameValues_Fiat_db.

Lemma computes_to_match_SCA_inv:
  forall av (compA : Comp W) x,
    (fun a : Value av =>
       match a with
       | SCA aa => compA aa
       | ADT _ => False
       end) ↝ x ->
    exists xx, x = SCA av xx /\ compA xx.
Proof.
  intros; destruct x; vm_compute in H; intuition eauto.
Qed.

Definition TelEq {A} ext (T1 T2: Telescope A) :=
  forall st, st ≲ T1 ∪ ext <->
        st ≲ T2 ∪ ext.

Ltac TelEq_rel_t :=
  red; unfold TelEq; intuition;
  repeat match goal with
  | [ H: forall _, _ <-> _ |- _ ] => rewrite H
  | [ H: forall _, _ <-> _, H': _ |- _ ] => rewrite H in H'
  | _ => solve [intuition]
  end.

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

Ltac SameValues_Fiat_t :=
  repeat (idtac "step";
           match goal with
           | _ => cleanup

           | [  |- _ ≲ Cons _ _ _ ∪ _ ] => simpl
           | [ H: _ ≲ Cons _ _ _ ∪ _ |- _ ] => simpl in H

           | [ H: match ?k with _ => _ end |- _ ] => let eqn := fresh in destruct k eqn:eqn
           | [  |- context[match SCA _ _ with _ => _ end] ] => simpl
           | [ H: _ ↝ _ |- _ ] => apply computes_to_match_SCA_inv in H

           | [ H: ?a = ?b |- context[?a] ] => rewrite H
           | [ H: ?a = ?b, H': context[?a] |- _ ] => rewrite H in H'
           | [ H: forall a, TelEq _ (?x a) (?y a) |- _ ≲ (?x _) ∪ _ ] => red in H; rewrite H
           | [ H: forall a, TelEq _ (?x a) (?y a), H': _ ≲ (?x _) ∪ _ |- _ ] => red in H; rewrite H in H'
           | [ H: forall a, ?v ↝ a -> TelEq _ (?x a) (?y a), H'': ?v ↝ _ |- _ ≲ (?x _) ∪ _ ] => unfold TelEq in H; rewrite (H _ H'')
           | [ H: forall a, ?v ↝ a -> TelEq _ (?x a) (?y a), H'': ?v ↝ _, H': _ ≲ (?x _) ∪ _ |- _ ] => unfold TelEq in H; rewrite (H _ H'') in H'
           | [ H: Monad.equiv ?b ?a |- ?b ↝ ?A ] => red in H; rewrite H
           | [ H: Monad.equiv ?a ?b, H': ?a ↝ ?A |- _ ] => red in H; rewrite H in H'

           | [  |- exists _, _ ] => eexists
           | _ => eauto with SameValues_Fiat_db
           end).

Lemma Cons_PopAnonymous:
  forall {av : Type} val tail (ext : StringMap.t (Value av)) (state : StringMap.t (Value av)),
    state ≲ [[val as _]]::tail ∪ ext ->
    state ≲ tail ∪ ext.
Proof.
  SameValues_Fiat_t.
Qed.

Lemma Cons_PushAnonymous:
  forall {av : Type} val tail (ext : StringMap.t (Value av)) (state : StringMap.t (Value av)),
    (exists v, val ↝ v) ->
    state ≲ tail ∪ ext ->
    state ≲ [[val as _]]::tail ∪ ext.
Proof.
  SameValues_Fiat_t.
Qed.

Create HintDb SameValues discriminated.

Hint Resolve Cons_PopAnonymous : SameValues_db.
Hint Resolve Cons_PushAnonymous : SameValues_db.

Lemma SameValues_Nil:
  forall {A} state ext,
    state ≲ (@Nil A) ∪ ext ->
    WeakEq ext state.
Proof.
  simpl; intros; assumption.
Qed.

Lemma SameValues_Nil_always:
  forall {A} state,
    state ≲ (@Nil A) ∪ state.
Proof.
  simpl; firstorder.
Qed.

Add Parametric Morphism {av} {env} {prog} : (@Safe av env prog)
    with signature (StringMap.Equal ==> iff)
      as Safe_Morphism.
Proof.
Admitted.

Add Parametric Morphism {av} {env} {prog} : (@RunsTo av env prog)
    with signature (StringMap.Equal ==> StringMap.Equal ==> iff)
      as RunsTo_Morphism.
Proof.
Admitted.

Add Parametric Morphism {av} : (@eval av)
    with signature (StringMap.Equal ==> eq ==> eq)
      as eval_Morphism.
Proof.
  intros;
  match goal with
  | [ e: Expr |- _ ] => induction e
  end; simpl; repeat rewrite_equalities; try reflexivity.
Qed.

Ltac isDeterministicStmtConstructor stmt :=
  match stmt with
  | Skip => idtac
  | Seq _ _ => idtac
  | Assign _ _ => idtac
  | _ => fail 1 "This statement has multiple RunsTo and Safe constructors"
  end.

Ltac isSafelyInvertibleStmtConstructor stmt :=
  match stmt with
  | Skip => idtac
  | Seq _ _ => idtac
  | If _ _ _ => idtac
  | Call _ _ _ => idtac
  | Assign _ _ => idtac
  | _ => fail 1 "Not a safely invertible constructor"
  end.

Lemma SameSCAs_refl:
  forall (av : Type) (t : StringMap.t (Value av)), SameADTs t t.
Proof.
  firstorder.
Qed.

Lemma SameADTs_refl:
  forall (av : Type) (t : StringMap.t (Value av)), SameSCAs t t.
Proof.
  firstorder.
Qed.

Lemma WeakEq_refl:
  forall (av : Type) (t : StringMap.t (Value av)), WeakEq t t.
Proof.
  firstorder.
Qed.

Lemma NotIn_not_mapsto_adt :
  forall {av} var (state: StringMap.t (Value av)),
    var ∉ state ->
    not_mapsto_adt var state = true.
Proof.
  unfold not_mapsto_adt, is_mapsto_adt, is_some_p; intros.
  rewrite not_in_find; tauto.
Qed.

Hint Resolve NotIn_not_mapsto_adt : SameValues_db.

Lemma MapsTo_SCA_not_mapsto_adt :
  forall {av} k w fmap,
    StringMap.MapsTo k (SCA av w) fmap ->
    not_mapsto_adt k fmap = true.
Proof.
  intros; unfold not_mapsto_adt, is_mapsto_adt, is_some_p.
  StringMapUtils.normalize; reflexivity.
Qed.

Hint Resolve MapsTo_SCA_not_mapsto_adt : SameValues_db.

Lemma SameValues_Fiat_Bind_TelEq :
  forall {av} key compA compB tail ext,
    TelEq ext
          (Cons key (@Bind (Value av) (Value av) compA compB) tail)
          (Cons None compA (fun a => Cons key (compB a) tail)).
Proof.
  unfold TelEq; SameValues_Fiat_t.
Qed.

Definition WrapComp_W {av} (cmp: Comp W) :=
  fun (a: Value av) => match a with
                    | SCA a => cmp ↝ a
                    | _ => False
                    end.

Definition WrapCons_W {av} key (cmp: W -> Comp (Value av)) tail :=
  fun (a: Value av) => match a with
                    | SCA a => Cons key (cmp a) tail
                    | _ => Nil
                    end.

Definition WrappedCons {av A} Wrapper (key: option string) (cmp: A -> Comp (Value av)) (tail: Value av -> Telescope av)
  : Value av -> Telescope av :=
  Wrapper key cmp tail.

Lemma SameValues_Fiat_Bind_TelEq_W :
  forall {av} key (compA: Comp W) (compB: W -> Comp (Value av)) tail ext,
    @TelEq av ext
           (Cons key (@Bind _ _ compA compB) tail)
           (Cons None (WrapComp_W compA) (WrappedCons WrapCons_W key compB tail)).
Proof.
  unfold TelEq, WrappedCons, WrapCons_W; SameValues_Fiat_t.
Qed.

Add Parametric Morphism {av} : (@is_mapsto_adt av)
    with signature (eq ==> StringMap.Equal ==> eq)
      as is_mapsto_adt_morphism.
Proof.
  intros * H; unfold is_mapsto_adt; rewrite H; reflexivity.
Qed.

Add Parametric Morphism {av} : (@not_mapsto_adt av)
    with signature (eq ==> StringMap.Equal ==> eq)
      as not_mapsto_adt_morphism.
Proof.
  intros * H; unfold not_mapsto_adt; rewrite H; reflexivity.
Qed.

Lemma eval_AssignVar_MapsTo:
  forall (av : Type) (var : StringMap.key) (val : W) (state : State av),
    StringMap.MapsTo var (SCA av val) state ->
    eval state (Var var) = Some (SCA av val).
Proof.
  (*! eauto using? *)
  intros; apply find_mapsto_iff; assumption.
Qed.

Hint Resolve eval_AssignVar_MapsTo : SameValues_db.

Lemma eval_Binop_Some:
  forall (av : Type) (var1 var2 : StringMap.key) (val1 val2 : W)
    (ext : StringMap.t (Value av)) op
    (H1 : StringMap.MapsTo var2 (SCA av val2) ext)
    (H0 : StringMap.MapsTo var1 (SCA av val1) ext),
    eval ext (Binop op (Var var1) (Var var2)) = Some (SCA av (eval_binop (inl op) val1 val2)).
Proof.
  intros;
  rewrite find_mapsto_iff in *;
  unfold eval, eval_binop_m;
  repeat match goal with
         | [ H: ?a = ?b |- context[?a] ] => rewrite H
         end;
  reflexivity.
Qed.

Hint Resolve eval_Binop_Some : SameValues_db.

Lemma not_mapsto_adt_add:
  forall av (k k' : StringMap.key) v (fmap: _ (_ av)),
    k <> k' ->
    not_mapsto_adt k (StringMap.add k' v fmap) =
    not_mapsto_adt k fmap.
Proof.
  intros.
  unfold not_mapsto_adt, is_mapsto_adt, is_some_p.
  rewrite add_neq_o by congruence.
  reflexivity.
Qed.

Ltac facade_cleanup :=
  progress match goal with
  | [  |- eval _ _ = Some _ ] => first [ reflexivity | progress simpl ]
  | [ H: eval _ _ = Some _ |- _ ] => simpl in H
  | [ H: eval_binop_m _ _ _ = Some _ |- _ ] => simpl in H
  | [ H: context[match Some _ with _ => _ end] |- _ ] => simpl in H
  | [ H: ?k <> ?k' |- context[not_mapsto_adt ?k (StringMap.add ?k' _ _)] ] => rewrite not_mapsto_adt_add by congruence
  | [ H: ?k' <> ?k |- context[not_mapsto_adt ?k (StringMap.add ?k' _ _)] ] => rewrite not_mapsto_adt_add by congruence
  | [ H: ?k ∉ ?m |- context[not_mapsto_adt ?k ?m] ] => rewrite NotIn_not_mapsto_adt by assumption
  end.

Ltac unfold_and_subst :=       (* Work around https://coq.inria.fr/bugs/show_bug.cgi?id=3259 *)
  repeat match goal with
         | [ H := _ |- _ ] => progress (unfold H in *; clear H)
         end; subst.

Ltac facade_inversion :=
  (*! TODO Why does inversion_clear just delete RunsTo Skip a b? !*)
  progress match goal with
  | [ H: Safe _ ?p _ |- _ ]     => isSafelyInvertibleStmtConstructor p; inversion H; unfold_and_subst; clear H
  | [ H: RunsTo _ ?p _ _ |- _ ] => isSafelyInvertibleStmtConstructor p; inversion H; unfold_and_subst; clear H
  | [ H: Some _ = Some _ |- _ ] => inversion H; unfold_and_subst; clear H
  | [ H: SCA _ _ = SCA _ _ |- _ ] => inversion H; unfold_and_subst; clear H
  end.

Definition dec2bool {P Q} (dec: {P} + {Q}) :=
  if dec then true else false.

Lemma dec2bool_correct {P Q A} :
  forall (dec: {P} + {Q}) (tp fp: A),
    (if dec then tp else fp) = if (dec2bool dec) then tp else fp.
Proof.
  intros; destruct dec; reflexivity.
Qed.

Definition bool2w b :=
  match b with
  | true => (Word.natToWord 32 1)
  | false => (Word.natToWord 32 0)
  end.

Definition bool2val {av} b :=
  SCA av (bool2w b).

Definition isTrueExpr var :=
  TestE IL.Eq (Const (bool2w true)) (Var var).

Require Import GLabelMap.
Module GLabelMapUtils := WUtils_fun (GLabelMap.E) (GLabelMap).

Ltac facade_construction_if_helper test trueLemma falseLemma :=
  match test with
  | true => apply trueLemma
  | false => apply falseLemma
  | _ => destruct test
  end.

Ltac facade_construction :=
  progress match goal with
           | [  |- Safe _ ?p _]          => isDeterministicStmtConstructor p; econstructor
           | [  |- RunsTo _ ?p _ _ ]     => isDeterministicStmtConstructor p; econstructor
           | [ H: GLabelMap.MapsTo ?fname (@Axiomatic _ ?spec) ?env |- Safe ?env (Call ?retv ?fname ?args) ?st ] =>
             eapply (@SafeCallAx _ env retv fname args st spec)
           | [ H: GLabelMap.MapsTo ?fname (@Operational _ ?spec) ?env |- Safe ?env (Call ?retv ?fname ?args) ?st ] =>
             eapply (@SafeCallOp _ env retv fname args st spec)
           | [ H: StringMap.MapsTo ?k (bool2val ?test) ?st |- Safe _ (If (isTrueExpr ?k) _ _) ?st ] =>
             facade_construction_if_helper test SafeIfTrue SafeIfFalse
           | [ H: StringMap.MapsTo ?k (bool2val ?test) ?st |- RunsTo _ (If (isTrueExpr ?k) _ _) ?st ] =>
             facade_construction_if_helper test RunsToIfTrue RunsToIfFalse
           end.

Ltac StringMap_t :=
  match goal with
  | _ => progress StringMapUtils.normalize
  | [ H: StringMap.MapsTo ?k (ADT ?v) ?st, H': SameADTs ?st _ |- _ ] => learn (SameADTs_impl H' H)
  | [ H: StringMap.MapsTo ?k (ADT ?v) ?st, H': SameADTs _ ?st |- _ ] => learn (SameADTs_impl' H' H)
  | [ H: StringMap.MapsTo ?k ?v ?m, H': WeakEq ?m ?m' |- _ ] => learn (WeakEq_Mapsto_MapsTo H H')
  end.

Lemma SameValues_WeakEq :
  forall {av} tenv st1 st2 m,
    @WeakEq av st1 st2 ->
    (st1 ≲ tenv ∪ m ->
     st2 ≲ tenv ∪ m).
Proof.
  induction tenv as [ | ? ? ? IH ];
  repeat match goal with
         | _ => t_Morphism_step
         | _ => StringMap_t
         | _ => solve [eauto using WeakEq_Trans, WeakEq_remove]
         end.
Qed.

Add Parametric Morphism {av} : (@SameValues av)
    with signature (WeakEq --> WeakEq ==> eq ==> Basics.impl)
      as SameValues_WeakMorphism.
Proof.
  unfold Basics.impl; intros; subst;
  eapply SameValues_WeakEq; eauto;
  eapply SameValues_WeakEq_Ext; eauto using Equal_sym.
Qed.

Ltac push_pop IH :=
  repeat match goal with
         | _ => eassumption
         | _ => apply IH
         | [ H: ?a /\ ?b |- _ ] => destruct H
         | [  |- ?a /\ ?b ] => split
         | [ H: context[StringMap.find ?k (StringMap.remove ?k' ?st)] |- context[StringMap.find ?k ?st] ] =>
           let _eq := fresh in destruct (StringMap.find k (StringMap.remove k' st)) eqn:_eq; [ | tauto]
         | [ H: (StringMap.find ?k (StringMap.remove ?k' ?st)) = Some _ |- _ ] =>
           rewrite <- find_mapsto_iff in H; rewrite remove_mapsto_iff in H
         | [ H: context[StringMap.find ?k ?st] |- context[StringMap.find ?k (StringMap.remove ?k' ?st)] ] =>
           let _eq := fresh in destruct (StringMap.find k st) eqn:_eq; [| tauto]
         | [ H: StringMap.MapsTo ?k ?v ?m |- context[StringMap.find ?k ?m] ] => rewrite find_mapsto_iff in H; rewrite H
         | [ H: StringMap.MapsTo ?k ?v ?s, H': ?k <> ?k' |- StringMap.MapsTo ?k ?v (StringMap.remove ?k' ?s)] =>
           rewrite remove_neq_mapsto_iff by congruence
         | [ H: StringMap.remove ?k (StringMap.remove ?k' ?s) ≲ _ ∪ _ |- StringMap.remove ?k' (StringMap.remove ?k ?s) ≲ _ ∪ _ ] =>
           rewrite remove_remove_comm
         | [ H: exists v, _ |- exists v, _ ] => destruct H; eexists
         | _ => rewrite SameValues_Equal_iff; eauto using remove_remove_comm
         | [ H: StringMap.find ?k ?m = _ |- match StringMap.find ?k ?m with _ => _ end ] => rewrite H
         | [ H: StringMap.remove ?k ?st ≲ ?tel ∪ [?k' <-- ?v]::?ext |- _ ] =>
           assert (k' ∈ (StringMap.remove k st)) by eauto using SameValues_In_Ext_State_add; no_duplicates;
           assert (k' <> k) by eauto using In_remove_neq;
           rewrite remove_neq_o by eassumption
         | _ => eauto using remove_remove_comm
         end.

Lemma SameValues_PushExt:
  forall (av : Type) (key : StringMap.key)
    (tail : Value av -> Telescope av) (v0 : Value av)
    (ext initial_state : StringMap.t (Value av)),
    StringMap.MapsTo key v0 initial_state ->
    StringMap.remove key initial_state ≲ tail v0 ∪ ext ->
    initial_state ≲ tail v0 ∪ [key <-- v0]::ext.
Proof.
  intros until v0.
  induction (tail v0) as [ | k ? ? IH ]; intros.

  - simpl in *;
    lazymatch goal with
    | [ H: StringMap.MapsTo _ _ _ |- _ ] => rewrite (MapsTo_add_remove H)
    end; eauto using WeakEq_add.
  - simpl in *. destruct k; push_pop IH.
Qed.

Lemma Cons_PushExt:
  forall (av : Type) (key : StringMap.key) (tail : Value av -> Telescope av)
    (ext : StringMap.t (Value av)) (v : Value av)
    (initial_state : StringMap.t (Value av)),
    initial_state ≲ Cons (Some key) (ret v) tail ∪ ext ->
    initial_state ≲ tail v ∪ [key <-- v]::ext.
Proof.
  t; apply SameValues_PushExt; try rewrite find_mapsto_iff; eauto.
Qed.

Lemma SameValues_PopExt:
  forall (av : Type) (key : StringMap.key)
    (tail : Value av -> Telescope av) (v0 : Value av)
    (ext initial_state : StringMap.t (Value av)),
    (* StringMap.MapsTo key v0 initial_state -> *)
    key ∉ ext ->
    initial_state ≲ tail v0 ∪ [key <-- v0]::ext ->
    StringMap.remove key initial_state ≲ tail v0 ∪ ext.
Proof.
  intros until v0.
  induction (tail v0) as [ | k ? ? IH ]; intros.

  - simpl in *;
    lazymatch goal with
    | [ H: ?k ∉ ?ext |- _ ] => rewrite <- (fun x => remove_add_cancel x H eq_refl)
    end; eauto using WeakEq_remove.
  - simpl in *. destruct k; push_pop IH.
Qed.

Lemma Cons_PopExt:
  forall (av : Type) (key : StringMap.key) (tail : Value av -> Telescope av)
    (ext : StringMap.t (Value av)) (v : Value av)
    (initial_state : StringMap.t (Value av)),
    key ∉ ext ->
    initial_state ≲ tail v ∪ [key <-- v]::ext ->
    initial_state ≲ Cons (Some key) (ret v) tail ∪ ext.
Proof.
  t.
  repeat match goal with
         | [ H: ?st ≲ ?tel ∪ [?k <-- ?v]::ext |- _ ] =>
           let h := fresh in pose proof H0 as h; apply SameValues_MapsTo_Ext_State_add in h; no_duplicates
         | [ H: StringMap.MapsTo ?k ?v ?m |- match StringMap.find ?k ?m with _ => _ end] =>
           rewrite find_mapsto_iff in H; rewrite H
         end.
  t.

  eauto using SameValues_PopExt.
Qed.

Lemma SameValues_Add_Cons:
  forall (av : Type) (key : StringMap.key) value (ext state : StringMap.t (Value av)),
    key ∉ ext -> WeakEq ext state -> [key <-- value]::state ≲ [[ key <-- value as _]]::Nil ∪ ext.
Proof.
  intros; apply Cons_PopExt; simpl; eauto using WeakEq_refl, WeakEq_add.
Qed.

Hint Resolve SameValues_Add_Cons : SameValues_db.
Hint Resolve WeakEq_add : SameValues_db.

Set Implicit Arguments.

Fixpoint NotInTelescope {av} k (tenv: Telescope av) :=
  match tenv with
  | Nil => True
  | Cons key val tail => Some k <> key /\ (forall v, val ↝ v -> NotInTelescope k (tail v))
  end.

Lemma NotInTelescope_not_eq_head:
  forall (av : Type) (key : string) (val : Comp (Value av))
    (tail : Value av -> Telescope av) (var : StringMap.key),
    NotInTelescope var ([[` key <~~ val as kk]]::tail kk) ->
    key <> var.
Proof.
  simpl; intros; repeat cleanup; eauto.
Qed.

Lemma NotInTelescope_not_in_tail:
  forall (av : Type) s (val : Comp (Value av))
    (tail : Value av -> Telescope av) (var : StringMap.key)
    (v : Value av),
    val ↝ v ->
    NotInTelescope var ([[ s <~~ val as kk]]::tail kk) ->
    NotInTelescope var (tail v).
Proof.
  simpl; intros.
  intuition eauto.
Qed.

Lemma SameValues_Cons_unfold_Some :
  forall av k (st: State av) val ext tail,
    st ≲ (Cons (Some k) val tail) ∪ ext ->
    exists v, StringMap.MapsTo k v st /\ val ↝ v /\ StringMap.remove k st ≲ tail v ∪ ext.
Proof.
  simpl; intros;
  repeat match goal with
         | _ => exfalso; assumption
         | [ H: match ?x with Some _ => _ | None => False end |- _ ] => destruct x eqn:eq
         | _ => intuition eauto using StringMap.find_2
         end.
Qed.

Lemma SameValues_Cons_unfold_None :
  forall av (st: State av) val ext tail,
    st ≲ (Cons None val tail) ∪ ext ->
    exists v, val ↝ v /\ st ≲ tail v ∪ ext.
Proof.
  simpl; intros; assumption.
Qed.

Inductive Learnt_FromWeakEq {A} (F1 F2: StringMap.t A) :=
| LearntFromWeakEq: Learnt_FromWeakEq F1 F2.

Ltac learn_from_WeakEq_internal HWeakEq fmap1 fmap2 :=
  match fmap1 with
  | StringMap.add ?k ?v ?map =>
    assert (StringMap.MapsTo k v fmap2);
      [ apply (fun mp => WeakEq_Mapsto_MapsTo mp HWeakEq); decide_mapsto | ];
      learn_from_WeakEq_internal HWeakEq map fmap2
  | _ => idtac
  end.

Ltac learn_from_WeakEq HWeakEq fmap1 fmap2 :=
  lazymatch goal with
  | [ H: Learnt_FromWeakEq fmap1 fmap2 |- _ ] => fail
  | _ => pose proof (LearntFromWeakEq fmap1 fmap2); learn_from_WeakEq_internal HWeakEq fmap1 fmap2
  end.


Add Parametric Morphism {av} : (@is_mapsto_adt av)
    with signature (eq ++> WeakEq ==> eq)
      as is_mapsto_adt_weak_morphism.
Proof.
  intros * H; unfold not_mapsto_adt, is_mapsto_adt, is_some_p, is_adt in *.
  destruct (StringMap.find y x) eqn:eq0.
  - rewrite <- find_mapsto_iff in eq0;
    pose proof (WeakEq_Mapsto_MapsTo eq0 H) as eq1;
    rewrite find_mapsto_iff in eq1; rewrite eq1; reflexivity.
  - destruct (StringMap.find y y0) eqn:eq1; try reflexivity.
    destruct v; try reflexivity.
    destruct H as [H _]; unfold SameADTs in H.
    rewrite <- find_mapsto_iff, <- H, find_mapsto_iff in eq1.
    congruence.
Qed.

Add Parametric Morphism {av} : (@not_mapsto_adt av)
    with signature (eq ++> WeakEq ==> eq)
      as not_mapsto_adt_weak_morphism.
Proof.
  intros * H; unfold not_mapsto_adt; rewrite H; reflexivity.
Qed.


Ltac not_mapsto_adt_t :=
  unfold not_mapsto_adt, is_mapsto_adt, is_some_p, is_adt;
  repeat match goal with
         | _ => cleanup
         | _ => reflexivity
         | _ => congruence
         | _ => StringMap_t
         | [  |- context[match ?a with _ => _ end] ] => let h := fresh in destruct a eqn:h; subst
         | [ H: context[match ?a with _ => _ end]  |- _ ] => let h := fresh in destruct a eqn:h; subst
         end.

Lemma not_in_SameADTs_not_mapsto_adt:
  forall {av : Type} (name : StringMap.key) (ext : StringMap.t (Value av))
    (initial_state : State av),
    name ∉ ext ->
    SameADTs ext initial_state ->
    not_mapsto_adt name initial_state = true.
Proof.
  not_mapsto_adt_t.
Qed.

Lemma not_mapsto_adt_not_MapsTo_ADT :
  forall {av k st},
    @not_mapsto_adt av k st = true ->
    forall {v: av}, not (StringMap.MapsTo k (ADT v) st).
Proof.
  not_mapsto_adt_t; red; intros; not_mapsto_adt_t.
Qed.

Lemma MapsTo_ADT_not_mapsto_adt_true:
  forall {av} (k : StringMap.key) (st : StringMap.t (Value av)) (a : av),
    StringMap.MapsTo k (ADT a) st ->
    not_mapsto_adt k st = false.
Proof.
  not_mapsto_adt_t.
Qed.

Lemma not_mapsto_adt_remove :
  forall (av : Type) (s : string) (k : StringMap.key)
    (st : StringMap.t (Value av)),
    not_mapsto_adt k st = true ->
    not_mapsto_adt k (StringMap.remove s st) = true.
Proof.
  intros.
  not_mapsto_adt_t.
  match goal with
  | [ H: StringMap.MapsTo ?k (ADT ?v) ?m |- _ ] =>  learn (MapsTo_ADT_not_mapsto_adt_true H2)
  end.
  congruence.
Qed.

Lemma not_mapsto_adt_neq_remove' :
  forall {av} (s : string) (k : StringMap.key) v (st : StringMap.t (Value av)),
    k <> s ->
    not_mapsto_adt k st = true ->
    not_mapsto_adt k (StringMap.add s v st) = true.
Proof.
  not_mapsto_adt_t.
Qed.

Ltac SameValues_Facade_t_step :=
  match goal with
  | _ => cleanup
  | _ => facade_cleanup
  | _ => facade_inversion
  | _ => facade_construction

  | [ |- @ProgOk _ _ _ _ _ _ ] => red

  | _ => StringMap_t
  | _ => progress subst

  | [ H: TelEq _ ?x _ |- context[?st ≲ ?x ∪ _] ] => rewrite (H st)
  | [ H: TelEq _ ?x _, H': context[?st ≲ ?x ∪ _] |- _ ] => rewrite_in (H st) H'

  (* Specialize ProgOk *)
  | [ H: ProgOk ?ext _ _ ?tel _, H': ?st ≲ ?tel ∪ ?ext |- _ ] => learn (H st H')
  | [ H: forall st : State _, RunsTo ?env ?p ?ext st -> _, H': RunsTo ?env ?p ?ext ?st |- _ ] => learn (H st H')
  (* Cleanup Cons *)
  | [ H: ?st ≲ Cons (Some _) _ _ ∪ _ |- _ ] => learn (Cons_PushExt _ _ _ _ _ H)
  | [ H: ?st ≲ Cons None _ _ ∪ _ |- _ ] => learn (Cons_PopAnonymous H)
  | [ H: ?st ≲ (fun _ => _) _ ∪ _ |- _ ] => progress cbv beta in H
  | [ H: ?st ≲ (Cons (Some ?k) ?val ?tail) ∪ ?ext |- _ ] => learn (SameValues_Cons_unfold_Some k st val ext tail H)
  | [ H: ?st ≲ (Cons None ?val ?tail) ∪ ?ext |- _ ] => learn (SameValues_Cons_unfold_None H)
  | [ H: StringMap.MapsTo ?k ?v ?ext, H': ?st ≲ ?tenv ∪ ?ext |- _ ] => learn (SameValues_MapsTo_Ext_State H' H)
  (* Cleanup NotInTelescope *)
  | [ H: NotInTelescope ?k (Cons None _ _) |- _ ] => simpl in H
  | [ H: NotInTelescope ?k (Cons (Some ?k') ?v ?tail) |- _ ] => learn (NotInTelescope_not_eq_head _ H)
  | [ H: NotInTelescope ?k (Cons (Some ?k') ?v ?tail), H': ?v ↝ _ |- _ ] => learn (NotInTelescope_not_in_tail _ _ H' H)
  (* Learn MapsTo instances from WeakEqs *)
  | [ H: ?st ≲ Nil ∪ ?ext |- _ ] => learn (SameValues_Nil H)
  | [ H: WeakEq _ ?st |- not_mapsto_adt _ ?st = _ ] => rewrite <- H
  | [ H: WeakEq ?st1 ?st2 |- _ ] => learn_from_WeakEq H st1 st2

  (* Cleanup not_mapsto_adt *)
  | [ H: ?k <> ?s |- not_mapsto_adt ?k (StringMap.add ?s _ _) = true ] => apply not_mapsto_adt_neq_remove'; [ congruence | ]
  | [ H: ?s <> ?k |- not_mapsto_adt ?k (StringMap.add ?s _ _) = true ] => apply not_mapsto_adt_neq_remove'; [ congruence | ]

  | [ H: ?a -> _, H': ?a |- _ ] => match type of a with Prop => specialize (H H') end
  end.

Ltac SameValues_Facade_t :=
  repeat SameValues_Facade_t_step;
  try solve [eauto 4 with SameValues_db].

Add Parametric Morphism {A} ext : (@Cons A)
    with signature (eq ==> Monad.equiv ==> pointwise_relation _ (TelEq ext) ==> (TelEq ext))
      as Cons_MonadEquiv_morphism.
Proof.
  unfold pointwise_relation; intros; unfold TelEq;
  SameValues_Fiat_t.
Qed.

Definition PointWise_TelEq {A} ext v t1 t2 :=
  forall vv: Value A, v ↝ vv -> @TelEq A ext (t1 vv) (t2 vv).

Add Parametric Morphism {A} ext k cmp : (@Cons A k cmp)
    with signature ((PointWise_TelEq ext cmp) ==> (TelEq ext))
      as Cons_TelEq_pointwise_morphism.
Proof.
  unfold PointWise_TelEq; intros; unfold TelEq;
  SameValues_Fiat_t.
Qed.

Add Parametric Morphism {A} ext : (fun x y z t => @ProgOk A ext x y z t)
    with signature (eq ==> eq ==> (TelEq ext) ==> (TelEq ext) ==> iff)
      as ProgOk_TelEq_morphism.
Proof.
  unfold ProgOk; repeat match goal with
                        | [ H: ?a -> _, H': ?a |- _ ] => learn (H H')
                        | _ => SameValues_Facade_t_step
                        end.
Qed.

Lemma SameADTs_find_iff {av} m1 m2 :
  SameADTs m1 m2 <->
  (forall k v, StringMap.find k m1 = Some (@ADT av v) <-> StringMap.find k m2 = Some (@ADT av v)).
Proof.
  unfold SameADTs; setoid_rewrite find_mapsto_iff; reflexivity.
Qed.

Lemma SameSCAs_find_iff {av} m1 m2 :
  SameSCAs m1 m2 <->
  (forall k v, StringMap.find k m1 = Some (@SCA av v) -> StringMap.find k m2 = Some (@SCA av v)).
Proof.
  unfold SameSCAs; setoid_rewrite find_mapsto_iff; reflexivity.
Qed.

Lemma ProgOk_Chomp_lemma :
  forall {av} env key prog
    (tail1 tail2: Value av -> Telescope av)
    ext v,
    key ∉ ext ->
    ({{ tail1 v }} prog {{ tail2 v }} ∪ {{ [key <-- v] :: ext }} // env <->
     {{ Cons (Some key) (ret v) tail1 }} prog {{ Cons (Some key) (ret v) tail2 }} ∪ {{ ext }} // env).
Proof.
  repeat match goal with
         | _ => progress intros
         | _ => progress split
         | _ => tauto
         | [ H: ?a /\ ?b |- _ ] => destruct H
         | [ H: ?a ≲ Cons _ _ _ ∪ _ |- _ ] => learn (Cons_PushExt _ _ _ _ _ H)
         | [ H: ProgOk ?fmap _ _ ?t1 ?t2, H': _ ≲ ?t1 ∪ ?fmap |- _ ] => destruct (H _ H'); no_duplicates
         | [ H: RunsTo _ _ ?from ?to, H': forall st, RunsTo _ _ ?from st -> _ |- _ ] => specialize (H' _ H)
         | [ H: _ ≲ _ ∪ [_ <-- _] :: _ |- _ ] => apply Cons_PopExt in H1
         | _ => solve [eauto using Cons_PopExt]
         end.
Qed.

Lemma ProgOk_Chomp_Some :
  forall {av} env key value prog
    (tail1: Value av -> Telescope av)
    (tail2: Value av -> Telescope av)
    ext,
    key ∉ ext ->
    (forall v, value ↝ v -> {{ tail1 v }} prog {{ tail2 v }} ∪ {{ [key <-- v] :: ext }} // env) ->
    ({{ Cons (Some key) value tail1 }} prog {{ Cons (Some key) value tail2 }} ∪ {{ ext }} // env).
Proof.
  intros; apply ProkOk_specialize_to_ret; intros; apply ProgOk_Chomp_lemma; eauto.
Qed.

Lemma ProgOk_Chomp_None :
  forall {av} env value prog
    (tail1: Value av -> Telescope av)
    (tail2: Value av -> Telescope av) ext,
    (forall v, value ↝ v -> {{ tail1 v }} prog {{ tail2 v }} ∪ {{ ext }} // env) ->
    ({{ Cons None value tail1 }} prog {{ Cons None value tail2 }} ∪ {{ ext }} // env).
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => progress SameValues_Fiat_t
         | [ H: forall v, ?val ↝ v -> _, H': ?val ↝ ?v |- _ ] => learn (H _ H')
         end.
Qed.

Lemma SameADTs_pop_SCA_util:
  forall (av : Type) (st : StringMap.t (Value av))
    (k : StringMap.key)
    (v : W),
    not_mapsto_adt k st = true ->
    SameADTs st ([k <-- SCA av v]::st).
Proof.
  intros ** k' v; destruct (StringMap.E.eq_dec k k'); subst; split; intros;
  repeat match goal with
         | _ => progress map_iff
         | _ => progress not_mapsto_adt_t
         | [ H: not_mapsto_adt ?k ?st = true, H': StringMap.MapsTo ?k (ADT ?v) ?st |- _ ] => destruct (not_mapsto_adt_not_MapsTo_ADT H H')
         | [ H: context[@StringMap.MapsTo] |- _ ] => progress map_iff_in H
         end.
Qed.

Lemma SameADTs_pop_SCA:
  forall (av : Type) (st : StringMap.t (Value av))
    (k : StringMap.key) (v : W) ext,
    not_mapsto_adt k st = true ->
    SameADTs ext st ->
    SameADTs ext ([k <-- SCA av v]::st).
Proof.
  eauto using SameADTs_Trans, SameADTs_pop_SCA_util.
Qed.

Lemma SameSCAs_pop_SCA_util:
  forall (av : Type) (st : StringMap.t (Value av))
    (k : StringMap.key) (v : W),
    k ∉ st ->
    SameSCAs st ([k <-- SCA av v]::st).
Proof.
  unfold SameSCAs; intros; map_iff;
  match goal with
  | [ k: StringMap.key, k': StringMap.key |- _ ] => destruct (StringMap.E.eq_dec k k'); subst
  end; SameValues_Facade_t.
Qed.

Lemma SameSCAs_pop_SCA:
  forall (av : Type) (st : StringMap.t (Value av))
    (k : StringMap.key) (ext : StringMap.t (Value av))
    (v : W),
    k ∉ st ->
    SameSCAs ext st ->
    SameSCAs ext ([k <-- SCA av v]::st).
Proof.
  eauto using SameSCAs_Trans, SameSCAs_pop_SCA_util.
Qed.

Lemma WeakEq_pop_SCA:
  forall (av : Type) (st : StringMap.t (Value av))
    (k : StringMap.key) (ext : StringMap.t (Value av))
    (v : W),
    k ∉ st ->
    WeakEq ext st ->
    WeakEq ext ([k <-- SCA av v]::st).
Proof.
  unfold WeakEq;
  intuition eauto using SameSCAs_pop_SCA, SameADTs_pop_SCA, NotIn_not_mapsto_adt.
Qed.

Lemma SameADTs_pop_SCA':
  forall (av : Type) (st : StringMap.t (Value av))
    (k : StringMap.key) (v : W) ext,
    k ∉ ext ->
    SameADTs ext st ->
    SameADTs ext ([k <-- SCA av v]::st).
Proof.
  unfold SameADTs; split; map_iff; intros;
  repeat match goal with
         | [ H: ?k ∉ ?m, H': StringMap.MapsTo ?k' _ ?m |- _ ] => learn (MapsTo_NotIn_inv H H')
         | [ H: forall _ _ , _ <-> _, H': _ |- _ ] => rewrite_in H H'
         | [ H: forall _ _ , _ <-> _ |- _ ] => rewrite H
         | _ => solve [intuition discriminate]
         end.
Qed.

Lemma SameSCAs_pop_SCA':
  forall (av : Type) (st : StringMap.t (Value av))
    (k : StringMap.key) (ext : StringMap.t (Value av))
    (v : W),
    k ∉ ext ->
    SameSCAs ext st ->
    SameSCAs ext ([k <-- SCA av v]::st).
Proof.
  unfold SameSCAs; map_iff; intros;
  repeat match goal with
         | [ H: ?k ∉ ?m, H': StringMap.MapsTo ?k' _ ?m |- _ ] => learn (MapsTo_NotIn_inv H H')
         | [ H: forall _ _ , _ <-> _, H': _ |- _ ] => rewrite_in H H'
         | [ H: forall _ _ , _ <-> _ |- _ ] => rewrite H
         | _ => solve [intuition discriminate]
         end.
  eauto using StringMap.add_2.
Qed.

Lemma WeakEq_pop_SCA':
  forall (av : Type) (st : StringMap.t (Value av))
    (k : StringMap.key) (ext : StringMap.t (Value av))
    (v : W),
    k ∉ ext ->
    WeakEq ext st ->
    WeakEq ext ([k <-- SCA av v]::st).
Proof.
  unfold WeakEq;
  intuition eauto using SameSCAs_pop_SCA', SameADTs_pop_SCA'.
Qed.

Hint Resolve WeakEq_pop_SCA' : call_helpers_db.

Lemma SameSCAs_pop_SCA_left :
  forall {av} k v m1 m2,
    k ∉ m1 ->
    SameSCAs (StringMap.add k (SCA av v) m1) m2 ->
    SameSCAs m1 m2.
Proof.
  unfold SameSCAs; intros; eauto using MapsTo_NotIn_inv, StringMap.add_2.
Qed.

Lemma SameADTs_pop_SCA_left :
  forall {av} k v m1 m2,
    k ∉ m1 ->
    SameADTs (StringMap.add k (SCA av v) m1) m2 ->
    SameADTs m1 m2.
Proof.
  unfold SameADTs; split; intros; rewrite <- H0 in *.
  - eauto using MapsTo_NotIn_inv, StringMap.add_2.
  - destruct (StringMap.E.eq_dec k k0); subst;
    StringMap_t; congruence.
Qed.

Lemma WeakEq_pop_SCA_left :
  forall {av} k v m1 m2,
    k ∉ m1 ->
    WeakEq (StringMap.add k (SCA av v) m1) m2 ->
    WeakEq m1 m2.
Proof.
  unfold WeakEq; intuition eauto using SameADTs_pop_SCA_left, SameSCAs_pop_SCA_left.
Qed.

Hint Resolve SameADTs_pop_SCA : SameValues_db.
Hint Resolve SameSCAs_pop_SCA : SameValues_db.
Hint Resolve WeakEq_pop_SCA : SameValues_db.

Lemma not_mapsto_adt_neq_remove:
  forall (av : Type) (s : string) (k : StringMap.key)
    (st : StringMap.t (Value av)),
    k <> s ->
    not_mapsto_adt k (StringMap.remove (elt:=Value av) s st) = true ->
    not_mapsto_adt k st = true.
Proof.
  not_mapsto_adt_t; SameValues_Facade_t.
Qed.

Hint Resolve not_mapsto_adt_neq_remove : SameValues_db.

Lemma not_In_Telescope_not_in_Ext_not_mapsto_adt :
  forall {av} tenv k st ext,
    k ∉ ext ->
    @NotInTelescope av k tenv ->
    st ≲ tenv ∪ ext ->
    not_mapsto_adt k st = true.
Proof.
  induction tenv; SameValues_Facade_t.
  destruct key; SameValues_Facade_t.
Qed.

Unset Printing Implicit Defensive.

Lemma WeakEq_remove_notIn:
  forall av (k : StringMap.key) (st1 st2 : State av),
    k ∉ st1 ->
    WeakEq st1 st2 ->
    WeakEq st1 (StringMap.remove k st2).
Proof.
  intros. rewrite <- (remove_notIn_Equal (k := k)  (m := st1)) by assumption.
  eauto using WeakEq_remove.
Qed.

Hint Resolve WeakEq_remove_notIn : SameValues_db.

Lemma SameValues_not_In_Telescope_not_in_Ext_remove:
  forall {av} (tenv : Telescope av) (var : StringMap.key)
    (ext : StringMap.t (Value av)) (initial_state : State av),
    var ∉ ext ->
    NotInTelescope var tenv ->
    initial_state ≲ tenv ∪ ext ->
    StringMap.remove var initial_state ≲ tenv ∪ ext.
Proof.
  induction tenv; intros;
  simpl in *; SameValues_Fiat_t; SameValues_Facade_t.
  rewrite remove_remove_comm by congruence; SameValues_Facade_t.
Qed.

Lemma SameValues_forget_Ext_helper:
  forall {av} (k : string) (cmp : Comp (Value av)) val
    (tmp : StringMap.key) (ext : StringMap.t (Value av))
    (final_state : State av),
    tmp ∉ ext ->
    final_state ≲ [[ ` k <~~ cmp as _]]::Nil ∪ [tmp <-- SCA _ val]::ext ->
    final_state ≲ [[ ` k <~~ cmp as _]]::Nil ∪ ext.
Proof.
  simpl; intros. SameValues_Fiat_t.
  eauto using WeakEq_pop_SCA, WeakEq_refl, WeakEq_Trans.
Qed.

Hint Resolve not_In_Telescope_not_in_Ext_not_mapsto_adt : SameValues_db.
Hint Resolve SameValues_not_In_Telescope_not_in_Ext_remove : SameValues_db.
Hint Resolve SameValues_forget_Ext_helper : SameValues_db.

Lemma SameValues_add_SCA:
  forall av tel st k ext v,
    k ∉ st ->
    st ≲ tel ∪ ext ->
    (StringMap.add k (SCA av v) st) ≲ tel ∪ ext.
Proof.
  induction tel;
  repeat (t_Morphism || SameValues_Facade_t).
  apply H; repeat (t_Morphism || SameValues_Facade_t).
Qed.

Lemma SameValues_Nil_inv :
  forall (A : Type) (state ext : StringMap.t (Value A)),
    WeakEq ext state -> state ≲ Nil ∪ ext.
Proof.
  intros; assumption.
Qed.

Hint Resolve SameValues_Nil_inv : SameValues_db.
Hint Resolve WeakEq_pop_SCA_left : SameValues_db.

Lemma SameValues_forget_Ext:
  forall (av : Type) (tenv : Telescope av) (var : StringMap.key) (val2 : W)
    (ext : StringMap.t (Value av)) (st' : State av),
    var ∉ ext ->
    st' ≲ tenv ∪ [var <-- SCA av val2] :: ext ->
    st' ≲ tenv ∪ ext.
Proof.
  induction tenv; SameValues_Facade_t.
  SameValues_Fiat_t.
Qed.

Hint Resolve SameValues_forget_Ext : SameValues_db.

Definition AlwaysComputesToSCA {av} (v: Comp (Value av)) :=
  forall vv, v ↝ vv -> is_adt vv = false.

Lemma SameValues_Dealloc_SCA_Some :
  forall {av} st k (v: Comp (Value av)) tail ext,
    AlwaysComputesToSCA v ->
    st ≲ Cons (Some k) v tail ∪ ext ->
    st ≲ Cons None v tail ∪ ext.
Proof.
  SameValues_Fiat_t.
  StringMap_t.
  repeat match goal with
         | [ H: StringMap.MapsTo _ _ ?st |- ?st ≲ _ ∪ _ ] => rewrite (MapsTo_add_remove H)
         | [ H: ?v ↝ ?vv, H': AlwaysComputesToSCA ?v |- _ ] => specialize (H' _ H)
         | [ H: is_adt ?v = false |- _ ] => destruct v; simpl in H; try congruence
         end.
  apply SameValues_add_SCA; eauto using StringMap.remove_1.
Qed.

Lemma SameValues_Dealloc_SCA :
  forall {av} st k (v: Comp (Value av)) tail ext,
    AlwaysComputesToSCA v ->
    st ≲ Cons k v tail ∪ ext ->
    st ≲ Cons None v tail ∪ ext.
Proof.
  intros; destruct k; eauto using SameValues_Dealloc_SCA_Some.
Qed.

Lemma not_in_WeakEq_not_mapsto_adt:
  forall {av : Type} (name : StringMap.key) (ext : StringMap.t (Value av))
    (initial_state : State av),
    name ∉ ext ->
    WeakEq ext initial_state ->
    not_mapsto_adt name initial_state = true.
Proof.
  unfold WeakEq; intros; intuition (eauto using not_in_SameADTs_not_mapsto_adt).
Qed.

Hint Resolve not_in_WeakEq_not_mapsto_adt : SameValues_db.

Ltac empty_remove_t :=
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | [ H: StringMap.MapsTo ?k _ (StringMap.empty _) |- _ ] => learn (StringMap.empty_1 H)
         | [ H: StringMap.MapsTo ?k ?v (StringMap.remove ?k' ?m) |- _ ] => learn (StringMap.remove_3 H)
         | [ H: forall k v, StringMap.MapsTo _ _ ?m <-> _ |- StringMap.MapsTo _ _ ?m ] => rewrite H
         end.

Notation "∅" := (StringMap.empty _).

(* Lemma SameSCAs_empty_remove: *)
(*   forall av (var : string) (initial_state : State av), *)
(*     SameSCAs ∅ initial_state -> *)
(*     SameSCAs ∅ (StringMap.remove var initial_state). *)
(* Proof. *)
(*   unfold SameSCAs; empty_remove_t. *)
(* Qed. *)

(* Lemma SameADTs_empty_remove: *)
(*   forall av (var : string) (initial_state : State av), *)
(*     SameADTs ∅ initial_state -> *)
(*     SameADTs ∅ (StringMap.remove var initial_state). *)
(* Proof. *)
(*   unfold SameADTs; empty_remove_t. *)
(* Qed. *)

(* Lemma WeakEq_empty_remove: *)
(*   forall av (var : string) (initial_state : State av), *)
(*     WeakEq ∅ initial_state -> *)
(*     WeakEq ∅ (StringMap.remove var initial_state). *)
(* Proof. *)
(*   unfold WeakEq; intuition eauto using SameADTs_empty_remove, SameSCAs_empty_remove. *)
(* Qed. *)

(* Lemma SameSCAs_remove_SCA: *)
(*   forall av (var : StringMap.key) (initial_state : State av), *)
(*     var ∉ initial_state -> *)
(*     SameSCAs initial_state (StringMap.remove var initial_state). *)
(* Proof. *)
(*   unfold SameSCAs; intros; rewrite remove_notIn_Equal; eauto. *)
(* Qed. *)

(* Lemma SameADTs_remove_SCA: *)
(*   forall av (var : StringMap.key) (initial_state : State av), *)
(*     var ∉ initial_state -> *)
(*     SameADTs initial_state (StringMap.remove var initial_state). *)
(* Proof. *)
(*   unfold SameADTs; intros; rewrite remove_notIn_Equal; eauto using iff_refl. *)
(* Qed. *)

(* Lemma WeakEq_remove_SCA: *)
(*   forall av (var : StringMap.key) (initial_state : State av), *)
(*     var ∉ initial_state -> *)
(*     WeakEq initial_state (StringMap.remove var initial_state). *)
(* Proof. *)
(*   unfold WeakEq; intuition (eauto using SameADTs_remove_SCA, SameSCAs_remove_SCA). *)
(* Qed. *)

Lemma SameValues_Pop_Both:
  forall {av} k ext tenv (st : State av) cmp v,
    cmp ↝ v ->
    StringMap.remove k st ≲ tenv ∪ ext ->
    [k <-- v] :: st ≲ [[`k <~~ cmp as _]] :: tenv ∪ ext.
Proof.
  intros; simpl; repeat StringMap_t; eauto.
Qed.

Hint Resolve SameValues_Pop_Both : SameValues_db.

Lemma CompileConstant:
  forall {av} name env w ext tenv,
    name ∉ ext ->
    NotInTelescope name tenv ->
    {{ tenv }}
      (Assign name (Const w))
    {{ [[name <-- (SCA av w) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma CompileRead:
  forall {av} name var (val: W) ext tenv,
    name ∉ ext ->
    NotInTelescope name tenv ->
    StringMap.MapsTo var (SCA av val) ext ->
    forall env,
    {{ tenv }}
      (Assign name (Var var))
    {{ [[name <-- (SCA _ val) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma CompileSkip:
  forall {av} (ext : StringMap.t (Value av)) env tenv,
    {{ tenv }}
      Skip
    {{ tenv }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

(* Lemma CompileBinop: *)
(*   forall {av} name var1 var2 (val1 val2: W) ext op tenv, *)
(*     name ∉ ext -> *)
(*     NotInTelescope name tenv -> *)
(*     StringMap.MapsTo var1 (SCA av val1) ext -> *)
(*     StringMap.MapsTo var2 (SCA av val2) ext -> *)
(*     forall env, *)
(*     {{ tenv }} *)
(*       Assign name (Binop op (Var var1) (Var var2)) *)
(*     {{ [[name <-- (SCA _ (eval_binop (inl op) val1 val2)) as _]]::tenv }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   SameValues_Facade_t. *)
(* Qed. *)

Definition WrapOpInExpr op :=
  match op with
  | inl o => Binop o
  | inr t => TestE t
  end.

Lemma CompileBinopOrTest:
  forall {av} name var1 var2 (val1 val2: W) ext op tenv,
    name ∉ ext ->
    NotInTelescope name tenv ->
    StringMap.MapsTo var1 (SCA av val1) ext ->
    StringMap.MapsTo var2 (SCA av val2) ext ->
    forall env,
    {{ tenv }}
      Assign name (WrapOpInExpr op (Var var1) (Var var2))
    {{ [[name <-- (SCA _ (eval_binop op val1 val2)) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  destruct op;
  SameValues_Facade_t.
Qed.

(* Lemma CompileBinopB_util: *)
(*   forall {T} k1 k2 k3 {v1 v2 v3} (fmap: StringMap.t T), *)
(*     k1 <> k2 -> k2 <> k3 -> k1 <> k3 -> *)
(*     StringMap.Equal ([k3 <-- v3] ::[k2 <-- v2]::[k1 <-- v1]::fmap) *)
(*                     ([k1 <-- v1] ::[k2 <-- v2]::[k3 <-- v3]::fmap). *)
(* Proof. *)
(*   unfold StringMap.Equal; intros; *)
(*   destruct (StringMap.E.eq_dec y k1); *)
(*   destruct (StringMap.E.eq_dec y k2); *)
(*   destruct (StringMap.E.eq_dec y k3); *)
(*   SameValues_Facade_t. *)
(* Qed. *)

(* Lemma CompileBinopB_util2: *)
(*   forall {av : Type} (var1 var2 var3 : StringMap.key) *)
(*     (val1 val2 val3 : _) (ext : StringMap.t (Value av)), *)
(*     var1 <> var2 -> *)
(*     var2 <> var3 -> *)
(*     var1 <> var3 -> *)
(*     var1 ∉ ext -> *)
(*     var2 ∉ ext -> *)
(*     var3 ∉ ext -> *)
(*     [var1 <-- val1] *)
(*       ::[var2 <-- val2] *)
(*       ::[var3 <-- val3]::ext *)
(*       ≲ [[var1 <-- val1 as _]] *)
(*       ::[[var2 <-- val2 as _]] *)
(*       ::[[var3 <-- val3 as _]]::Nil ∪ ext. *)
(* Proof. *)
(*   intros. *)
(*   repeat apply Cons_PopExt; try decide_not_in. *)
(*   rewrite CompileBinopB_util by assumption. *)
(*   apply SameValues_Nil_always. *)
(* Qed. *)

(* Lemma CompileBinop_with_dealloc_USELESS: *)
(*   forall {av} name var1 var2 (val1 val2: W) env ext op p1 p2 p3, *)
(*     name ∉ ext -> *)
(*     var1 ∉ ext -> *)
(*     var2 ∉ ext -> *)
(*     var1 <> var2 -> *)
(*     var1 <> name -> *)
(*     var2 <> name -> *)
(*     {{ Nil }} *)
(*       p1 *)
(*     {{ [[var1 <-- SCA _ val1 as _]]::Nil }} ∪ {{ ext }} // env -> *)
(*     {{ [[var1 <-- SCA _ val1 as _]]::Nil }} *)
(*       p2 *)
(*     {{ [[var1 <-- SCA _ val1 as _]]::[[var2 <-- SCA _ val2 as _]]::Nil }} ∪ {{ ext }} // env -> *)
(*     {{ [[var1 <-- SCA _ val1 as _]]::[[var2 <-- SCA _ val2 as _]]::[[name <-- (SCA av (eval_binop (inl op) val1 val2)) as _]]::Nil }} *)
(*       p3 *)
(*     {{ [[ret (SCA _ val1) as _]]::[[ret (SCA _ val2) as _]]::[[name <-- (SCA av (eval_binop (inl op) val1 val2)) as _]]::Nil }} ∪ {{ ext }} // env -> *)
(*     {{ Nil }} *)
(*       (Seq p1 (Seq p2 (Seq (Assign name (Binop op (Var var1) (Var var2))) p3))) *)
(*     {{ [[name <-- (SCA av (eval_binop (inl op) val1 val2)) as _]]::Nil }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   Time SameValues_Facade_t; *)
(*  *)
(*   assert ([name <-- SCA av (IL.evalBinop op val1 val2)]::st'0 *)
(*         ≲ [[var1 <-- SCA av val1 as _]] *)
(*           ::[[var2 <-- SCA av val2 as _]] *)
(*             ::[[name <-- SCA av (eval_binop (inl op) val1 val2) as _]]::Nil *)
(*             ∪ ext) by (repeat apply Cons_PopExt; *)
(*                         try decide_not_in; *)
(*                         simpl; *)
(*                         SameValues_Facade_t); *)
(*  *)
(*   SameValues_Facade_t. *)
(* Qed. *)

(* Lemma CompileBinop_left: *)
(*   forall {av} name var1 var2 (val1 val2: W) env ext op p2, *)
(*     name ∉ ext -> *)
(*     StringMap.MapsTo var1 (SCA av val1) ext -> *)
(*     var2 ∉ ext -> *)
(*     var1 <> var2 -> *)
(*     var2 <> name -> *)
(*     {{ Nil }} *)
(*       p2 *)
(*     {{ [[var2 <-- SCA _ val2 as _]]::Nil }} ∪ {{ ext }} // env -> *)
(*     {{ Nil }} *)
(*       (Seq p2 (Assign name (Binop op (Var var1) (Var var2)))) *)
(*     {{ [[name <-- (SCA av (eval_binop (inl op) val1 val2)) as _]]::Nil }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   Time SameValues_Facade_t. *)
(*  *)
(*   rewrite (add_redundant_cancel H0) in H19; SameValues_Facade_t. *)
(*   apply Cons_PopExt; [ SameValues_Facade_t | ]. *)
(*  *)
(*   cut (st' ≲ Nil ∪ ext); *)
(*   repeat match goal with *)
(*          | _ => reflexivity *)
(*          | _ => solve [simpl; SameValues_Facade_t] *)
(*          | _ => apply WeakEq_pop_SCA; [decide_not_in|] *)
(*          | [ H: WeakEq ?a ?st |- ?st ≲ _ ∪ _ ] => rewrite <- H *)
(*          | _ => progress simpl *)
(*          end. *)
(* Qed. *)

Lemma CompileBinopOrTest_left:
  forall {av} name var1 var2 (val1 val2: W) env ext op p2 tenv,
    name ∉ ext ->
    NotInTelescope name tenv ->
    StringMap.MapsTo var1 (SCA av val1) ext ->
    var2 ∉ ext ->
    var1 <> var2 ->
    var2 <> name ->
    {{ tenv }}
      p2
    {{ [[var2 <-- SCA _ val2 as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq p2 (Assign name (WrapOpInExpr op (Var var1) (Var var2))))
    {{ [[name <-- (SCA av (eval_binop op val1 val2)) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t;
  destruct op; SameValues_Facade_t.
Qed.

(* Lemma CompileBinop_right: *)
(*   forall {av} name var1 var2 (val1 val2: W) env ext op p2, *)
(*     name ∉ ext -> *)
(*     var1 ∉ ext -> *)
(*     StringMap.MapsTo var2 (SCA av val2) ext -> *)
(*     var1 <> var2 -> *)
(*     var1 <> name -> *)
(*     {{ Nil }} *)
(*       p2 *)
(*     {{ [[var1 <-- SCA _ val1 as _]]::Nil }} ∪ {{ ext }} // env -> *)
(*     {{ Nil }} *)
(*       (Seq p2 (Assign name (Binop op (Var var1) (Var var2)))) *)
(*     {{ [[name <-- (SCA av (eval_binop (inl op) val1 val2)) as _]]::Nil }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   Time SameValues_Facade_t. *)
(*  *)
(*   rewrite (add_redundant_cancel H1) in H19; SameValues_Facade_t. *)
(*   apply Cons_PopExt; [ SameValues_Facade_t | ]. *)
(*  *)
(*   cut (st' ≲ Nil ∪ ext); *)
(*   repeat match goal with *)
(*          | _ => reflexivity *)
(*          | _ => solve [simpl; SameValues_Facade_t] *)
(*          | _ => apply WeakEq_pop_SCA; [decide_not_in|] *)
(*          | [ H: WeakEq ?a ?st |- ?st ≲ _ ∪ _ ] => rewrite <- H *)
(*          | _ => progress simpl *)
(*          end. *)
(* Qed. *)

Lemma CompileBinopOrTest_right:
  forall {av} name var1 var2 (val1 val2: W) env ext op p2 tenv,
    name ∉ ext ->
    NotInTelescope name tenv ->
    StringMap.MapsTo var2 (SCA av val2) ext ->
    var1 ∉ ext ->
    var1 <> var2 ->
    var1 <> name ->
    {{ tenv }}
      p2
    {{ [[var1 <-- SCA _ val1 as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq p2 (Assign name (WrapOpInExpr op (Var var1) (Var var2))))
    {{ [[name <-- (SCA av (eval_binop op val1 val2)) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  Time SameValues_Facade_t;
  destruct op; SameValues_Facade_t.
Qed.

(* Lemma CompileBinop_full: *)
(*   forall {av} name var1 var2 (val1 val2: W) env ext op p1 p2, *)
(*     name ∉ ext -> *)
(*     var1 ∉ ext -> *)
(*     var2 ∉ ext -> *)
(*     var1 <> var2 -> *)
(*     var1 <> name -> *)
(*     var2 <> name -> *)
(*     {{ Nil }} *)
(*       p1 *)
(*     {{ [[var1 <-- SCA _ val1 as _]]::Nil }} ∪ {{ ext }} // env -> *)
(*     {{ [[var1 <-- SCA _ val1 as _]]::Nil }} *)
(*       p2 *)
(*     {{ [[var1 <-- SCA _ val1 as _]]::[[var2 <-- SCA _ val2 as _]]::Nil }} ∪ {{ ext }} // env -> *)
(*     {{ Nil }} *)
(*       (Seq p1 (Seq p2 (Assign name (Binop op (Var var1) (Var var2))))) *)
(*     {{ [[name <-- (SCA av (eval_binop (inl op) val1 val2)) as _]]::Nil }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   Time SameValues_Facade_t. *)
(*   apply Cons_PopExt; [ SameValues_Facade_t | ]. *)
(*  *)
(*   cut (st'0 ≲ Nil ∪ ext); *)
(*   repeat match goal with *)
(*          | _ => reflexivity *)
(*          | _ => solve [simpl; SameValues_Facade_t] *)
(*          | _ => apply WeakEq_pop_SCA; [decide_not_in|] *)
(*          | [ H: WeakEq ?a ?st |- ?st ≲ _ ∪ _ ] => rewrite <- H *)
(*          | _ => progress simpl *)
(*          end. *)
(* Qed. *)

Opaque Word.natToWord.

Lemma CompileBinopOrTest_full:
  forall {av} name var1 var2 (val1 val2: W) env ext op p1 p2 tenv,
    name ∉ ext ->
    NotInTelescope name tenv ->
    var1 ∉ ext ->
    var2 ∉ ext ->
    var1 <> var2 ->
    var1 <> name ->
    var2 <> name ->
    {{ tenv }}
      p1
    {{ [[var1 <-- SCA _ val1 as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ [[var1 <-- SCA _ val1 as _]]::tenv }}
      p2
    {{ [[var1 <-- SCA _ val1 as _]]::[[var2 <-- SCA _ val2 as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq p1 (Seq p2 (Assign name ((match op with inl o => Binop o | inr o => TestE o end) (Var var1) (Var var2)))))
    {{ [[name <-- (SCA av (eval_binop op val1 val2)) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  Time SameValues_Facade_t;
  destruct op;
  repeat SameValues_Facade_t_step.

  Hint Extern 3 (_ ∉ _) => decide_not_in : SameValues_db.

  apply SameValues_Pop_Both; eauto 2.
  apply SameValues_not_In_Telescope_not_in_Ext_remove; eauto 2.
  eapply SameValues_forget_Ext.
  2:eapply SameValues_forget_Ext; try eassumption.
  eauto with SameValues_db.
  eauto with SameValues_db.

  apply SameValues_Pop_Both; eauto 2.
  apply SameValues_not_In_Telescope_not_in_Ext_remove; eauto 2.
  eapply SameValues_forget_Ext.
  2:eapply SameValues_forget_Ext; try eassumption.
  eauto with SameValues_db.
  eauto with SameValues_db.
Qed.                               (* FIXME why doesn't eauto suffice here? *)

Set Implicit Arguments.

Lemma isTrueExpr_is_true:
  forall {av} (tmp : string) (st' : State av),
    StringMap.MapsTo tmp (bool2val true) st' -> is_true st' (isTrueExpr tmp).
Proof.
  unfold isTrueExpr, bool2val, is_true, is_false, eval_bool; simpl;
  SameValues_Facade_t.
Qed.

Lemma isTrueExpr_is_false:
  forall {av} (tmp : string) (st' : State av),
    StringMap.MapsTo tmp (bool2val false) st' -> is_false st' (isTrueExpr tmp).
Proof.
  unfold isTrueExpr, bool2val, is_true, is_false, eval_bool; simpl;
  SameValues_Facade_t.
Qed.

Lemma is_true_isTrueExpr:
  forall {av} (gallinaTest : bool) (tmp : StringMap.key) (st' : State av),
    is_true st' (isTrueExpr tmp) ->
    StringMap.MapsTo tmp (bool2val gallinaTest) st' ->
    gallinaTest = true.
Proof.
  unfold isTrueExpr, bool2val, bool2w, is_true, is_false, eval_bool; simpl;
  destruct gallinaTest; SameValues_Facade_t.
Qed.

Lemma is_false_isTrueExpr:
  forall {av} (gallinaTest : bool) (tmp : StringMap.key) (st' : State av),
    is_false st' (isTrueExpr tmp) ->
    StringMap.MapsTo tmp (bool2val gallinaTest) st' ->
    gallinaTest = false.
Proof.
  unfold isTrueExpr, bool2val, bool2w, is_true, is_false, eval_bool; simpl;
  destruct gallinaTest; SameValues_Facade_t.
Qed.

Ltac facade_if_helper :=
  match goal with
  | [ H: is_true ?st (isTrueExpr ?k), H': StringMap.MapsTo ?k (bool2val ?test) ?st |- _ ] => learn (is_true_isTrueExpr H H')
  | [ H: is_false ?st (isTrueExpr ?k), H': StringMap.MapsTo ?k (bool2val ?test) ?st |- _ ] => learn (is_false_isTrueExpr H H')
  | _ => solve [eauto using isTrueExpr_is_false, isTrueExpr_is_true with SameValues_db]
  end.

Lemma CompileIf :
  forall {av} k (gallinaTest: bool) gallinaT gallinaF tmp facadeTest facadeT facadeF env (ext: StringMap.t (Value av)) tenv,
    tmp ∉ ext ->
    NotInTelescope tmp tenv ->
    {{ tenv }}
      facadeTest
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::tenv }}
      facadeT
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::[[`k <~~ gallinaT as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::tenv }}
      facadeF
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::[[`k <~~ gallinaF as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq facadeTest (If (isTrueExpr tmp) facadeT facadeF))
    {{ [[`k <~~ if gallinaTest then gallinaT else gallinaF as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_if_helper
         end.
Qed.


Lemma CompileIf_InPlace :
  forall {av} k (gallinaTest: bool) oldK gallinaT gallinaF tmp facadeTest facadeT facadeF env (ext: StringMap.t (Value av)) tenv,
    tmp ∉ ext ->
    NotInTelescope tmp tenv ->
    {{ [[`k <~~ oldK as kk]] :: tenv }}
      facadeTest
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::[[`k <~~ oldK as _]] :: tenv }} ∪ {{ ext }} // env ->
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::[[`k <~~ oldK as _]] :: tenv }}
      facadeT
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::[[`k <~~ gallinaT as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::[[`k <~~ oldK as _]] :: tenv }}
      facadeF
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::[[`k <~~ gallinaF as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ [[`k <~~ oldK as _]] :: tenv }}
      (Seq facadeTest (DFacade.If (isTrueExpr tmp) facadeT facadeF))
    {{ [[`k <~~ if gallinaTest then gallinaT else gallinaF as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_if_helper
         end.
Qed.

Ltac spec_t :=
  abstract (repeat match goal with
                   | _ => red
                   | _ => progress intros
                   | _ => progress subst
                   | [ H: exists t, _ |- _ ] => destruct H
                   end; intuition).

Ltac learn_all_WeakEq_remove hyp lhs :=
  match lhs with
  | StringMap.add ?k _ ?lhs' => try learn (WeakEq_remove k hyp); learn_all_WeakEq_remove hyp lhs'
  | _ => idtac
  end.

Lemma combine_inv :
  forall A B input output combined,
    List.length input = List.length output ->
    @combine A B input output = combined ->
    input = fst (split combined) /\ output = snd (split combined).
Proof.
  intros; subst; rewrite combine_split; intuition eauto.
Qed.

Hint Resolve SameValues_Pop_Both : call_helpers_db.

(* Hint Extern 1 (_ ≲ Nil ∪ _) => simpl : call_helpers_db. *)
Hint Resolve SameValues_Nil_inv : call_helpers_db.

Ltac may_touch H :=
  match type of H with
  | context[@Learnt] => fail 1
  | _ => idtac
  end.

Ltac facade_cleanup_call :=
  match goal with
  | _ => progress cbv beta iota delta [add_remove_many] in *
  | _ => progress cbv beta iota delta [sel] in *
  | [ H: Axiomatic ?s = Axiomatic ?s' |- _ ] => inversion H; subst; clear H
  | [ H: PreCond ?f _ |- _ ] => let hd := head_constant f in unfold hd in H; cbv beta iota delta [PreCond] in H
  | [ H: PostCond ?f _ _ |- _ ] => let hd := head_constant f in unfold hd in H; cbv beta iota delta [PostCond] in H
  | [  |- PreCond ?f _ ] => let hd := head_constant f in unfold hd; cbv beta iota delta [PreCond]
  | [  |- PostCond ?f _ _ ] => let hd := head_constant f in unfold hd; cbv beta iota delta [PostCond]
  | [ H: WeakEq ?lhs _ |- _ ] => progress learn_all_WeakEq_remove H lhs
  | [ |- context[ListFacts4.mapM] ] => progress simpl ListFacts4.mapM
  | [ H: context[ListFacts4.mapM] |- _ ] => progress simpl ListFacts4.mapM in H
  | [ H: combine ?a ?b = _, H': List.length ?a = List.length ?b |- _ ] => learn (combine_inv a b H' H)
  | [ |-  context[split (cons _ _)] ] => simpl
  | [ H: context[split (cons _ _)] |- _ ] => may_touch H; simpl in H
  (* | [ H: match ?output with | nil => _ | cons _ _ => _ end = _ |- _ ] => let a := fresh in destruct output eqn:a *)
  | [ H: List.cons _ _ = List.cons _ _ |- _ ] => inversion H; try subst; clear H
  | _ => GLabelMapUtils.normalize
  | _ => solve [GLabelMapUtils.decide_mapsto_maybe_instantiate]
  (* | _ => progress simpl *)
  (* | _ => solve [eauto with call_helpers_db SameValues_db] *)
  end.

Ltac facade_eauto :=
  eauto 3 with call_helpers_db SameValues_db;
  eauto with call_helpers_db SameValues_db.

Hint Resolve WeakEq_Refl : call_helpers_db.
(* Hint Resolve WeakEq_Trans : call_helpers_db. *)
Hint Resolve WeakEq_remove_notIn : call_helpers_db.
Hint Resolve WeakEq_pop_SCA : call_helpers_db.
Hint Resolve WeakEq_pop_SCA_left : call_helpers_db.

Definition FacadeImplementationWW av (fWW: W -> W) : AxiomaticSpec av.
  refine {|
      PreCond := fun args => exists x, args = (SCA av x) :: nil;
      PostCond := fun args ret => exists x, args = (SCA av x, None) :: nil /\ ret = SCA av (fWW x)
    |}; spec_t.
Defined.

Lemma CompileCallFacadeImplementationWW:
  forall {av} {env} fWW,
  forall fpointer varg (arg: W) tenv,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationWW av fWW)) env ->
    forall vret ext,
      vret ∉ ext ->
      NotInTelescope vret tenv ->
      StringMap.MapsTo varg (SCA av arg) ext ->
      {{ tenv }}
        Call vret fpointer (varg :: nil)
      {{ [[ vret <-- SCA av (fWW arg) as _]]:: tenv }} ∪ {{ ext }} // env.
Proof.
  Time repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.

Lemma CompileCallFacadeImplementationWW_full:
  forall {av} {env} fWW,
  forall fpointer varg (arg: W) tenv,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationWW av fWW)) env ->
    forall vret ext p,
      vret ∉ ext ->
      varg ∉ ext ->
      NotInTelescope vret tenv ->
      NotInTelescope varg tenv ->
      vret <> varg ->
      {{ tenv }}
        p
      {{ [[ varg <-- SCA av arg as _]]:: tenv }} ∪ {{ ext }} // env ->
      {{ tenv }}
        Seq p (Call vret fpointer (varg :: nil))
      {{ [[ vret <-- SCA av (fWW arg) as _]]:: tenv }} ∪ {{ ext }} // env.
Proof.
  Time repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.

Lemma CompileDeallocSCA:
  forall {av} (env : Env av) k compSCA tail tail' ext prog,
    AlwaysComputesToSCA compSCA ->
    {{ [[compSCA as kk]]::(tail kk)}}
      prog
    {{ [[compSCA as kk]]::(tail' kk) }} ∪ {{ ext }} // env ->
    {{ [[k <~~ compSCA as kk]]::(tail kk)}}
      prog
    {{ [[compSCA as kk]]::(tail' kk) }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t;
  apply SameValues_Dealloc_SCA in H1;
  SameValues_Facade_t.
Qed.

Lemma AlwaysComputesToSCA_ret_SCA:
  forall (av : Type) (v : W), AlwaysComputesToSCA (ret (SCA av v)).
Proof.
  red; intros; computes_to_inv; subst; reflexivity.
Qed.

Hint Resolve AlwaysComputesToSCA_ret_SCA : SameValues_db.

Lemma AlwaysComputesToSCA_WrapComp_W {av} (cmp: Comp W) :
  AlwaysComputesToSCA (@WrapComp_W av cmp).
Proof.
  Transparent computes_to.
  red; unfold WrapComp_W, computes_to; intros.
  destruct vv; simpl; (reflexivity || (exfalso; assumption)).
Qed.

Lemma CompileDeallocSCA_ret:
  forall {av} (env : Env av) k v tail tail' ext
    prog,
    {{ [[(ret (SCA _ v)) as kk]]::(tail kk)}}
      prog
    {{ [[(ret (SCA _ v)) as kk]]::(tail' kk) }} ∪ {{ ext }} // env ->
    {{ [[k <~~ ret (SCA _ v) as kk]]::(tail kk)}}
      prog
    {{ [[ret (SCA _ v) as kk]]::(tail' kk) }} ∪ {{ ext }} // env.
Proof.
  intros; apply CompileDeallocSCA;
  SameValues_Facade_t.
Qed.

Lemma ProgOk_Transitivity_Cons :
  forall {av} env ext t1 t2 prog1 prog2 k (v: Comp (Value av)),
    {{ t1 }}                        prog1      {{ [[k <~~ v as _]]::t1 }}     ∪ {{ ext }} // env ->
    {{ [[k <~~ v as _]]::t1 }}       prog2      {{ [[k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ t1 }}                   Seq prog1 prog2 {{ [[k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Unset Implicit Arguments.

Lemma ProgOk_Transitivity_Name :
  forall {av} k env ext t1 t2 prog1 prog2 (v: Comp (Value av)),
    {{ t1 }}                             prog1       {{ [[`k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ [[`k <~~ v as kk]]::t2 kk }}       prog2       {{ [[v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ t1 }}                       Seq prog1 prog2  {{ [[v as kk]]::t2 kk }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Require Import Fiat.CertifiedExtraction.Gensym.

Tactic Notation "debug" constr(msg) :=
  idtac msg.

Tactic Notation "debug" constr(m1) constr(m2) :=
  idtac m1 m2.

Ltac compile_do_bind k compA compB tl :=
  debug "Transforming Fiat-level bind into telescope-level Cons";
  first [rewrite (SameValues_Fiat_Bind_TelEq k compA compB tl) | (* FIXME use a smarter procedure for rewriting here *)
         rewrite (SameValues_Fiat_Bind_TelEq_W k compA compB tl)].

Ltac compile_do_alloc cmp tail :=
  let name := gensym "v" in
  debug "Naming nameless head variable";
  apply (ProgOk_Transitivity_Name name).

Hint Resolve AlwaysComputesToSCA_ret_SCA : dealloc_db.
Hint Resolve AlwaysComputesToSCA_WrapComp_W : dealloc_db.

Ltac compile_dealloc key cmp :=
  debug "Deallocating head binding" key;
  match cmp with
  | _ => apply CompileDeallocSCA; [ solve [eauto with dealloc_db] | ]
  | ret (@ADT _ ?x) => fail
  end.

Ltac compile_do_cons :=
  debug "Moving head of Cons to separate goal";
  apply ProgOk_Transitivity_Cons.

Ltac compile_do_chomp key :=
  debug "Applying chomp rule";
  match key with
  | @Some _ _ => apply ProgOk_Chomp_Some
  | @None _   => apply ProgOk_Chomp_None
  end; intros; computes_to_inv.

Ltac compile_constant value :=
  debug "-> constant value";
  apply CompileConstant.

Ltac compile_read value ext :=
  debug "-> read from the environment";
  let location := find_fast value ext in
  match location with
  | Some ?k => apply (CompileRead (var := k))
  end.

Ltac translate_op gallina_op :=
  let hd := head_constant gallina_op in
  match hd with
  | @Word.wplus => constr:(@inl IL.binop IL.test IL.Plus)
  | @Word.wminus => constr:(@inl IL.binop IL.test IL.Minus)
  | @Word.wmult => constr:(@inl IL.binop IL.test IL.Times)
  | @Word.weqb => constr:(@inr IL.binop IL.test IL.Eq)
  | @IL.weqb => constr:(@inr IL.binop IL.test IL.Eq)
  | @IL.wneb => constr:(@inr IL.binop IL.test IL.Ne)
  | @IL.wltb => constr:(@inr IL.binop IL.test IL.Lt)
  | @IL.wleb => constr:(@inr IL.binop IL.test IL.Le)
  | @Word.wlt_dec => constr:(@inr IL.binop IL.test IL.Lt)
  | _ => fail 1 "Unknown operator" gallina_op
  end.

Ltac compile_binop av facade_op lhs rhs ext :=
  let vlhs := find_fast (SCA av lhs) ext in
  let vrhs := find_fast (SCA av rhs) ext in
  lazymatch constr:(vlhs, vrhs) with
  | (Some ?vlhs, Some ?vrhs) =>
    apply (CompileBinopOrTest (var1 := vlhs) (var2 := vrhs) facade_op)
  | (Some ?vlhs, None) =>
    let vrhs := gensym "r" in
    apply (CompileBinopOrTest_left (var1 := vlhs) (var2 := vrhs) facade_op)
  | (None, Some ?vrhs) =>
    let vlhs := gensym "l" in
    apply (CompileBinopOrTest_right (var1 := vlhs) (var2 := vrhs) facade_op)
  | (None, None) =>
    let vlhs := gensym "l" in
    let vrhs := gensym "r" in
    apply (CompileBinopOrTest_full (var1 := vlhs) (var2 := vrhs) facade_op)
  end.

Ltac decide_NotInTelescope :=
  repeat match goal with
         | _ => cleanup
         | _ => congruence
         | [  |- NotInTelescope _ Nil ] => reflexivity
         | [  |- NotInTelescope ?k (Cons _ _ _) ] => simpl
         end.

Ltac compile_do_side_conditions :=
  match goal with
  | _ => abstract decide_not_in
  | _ => abstract decide_NotInTelescope
  | [  |- StringMap.find _ _ = Some _ ] => solve [decide_mapsto_maybe_instantiate]
  | [  |- StringMap.MapsTo _ _ _ ] => solve [decide_mapsto_maybe_instantiate]
  | [  |- GLabelMap.MapsTo _ _ _ ] => solve [GLabelMapUtils.decide_mapsto_maybe_instantiate]
  end.

Lemma WrapComp_W_rewrite:
  forall (av : Type) (w : Word.word 32),
    Monad.equiv (WrapComp_W (ret w)) (ret (SCA av w)).
Proof.
  unfold WrapComp_W; unfold Monad.equiv; SameValues_Fiat_t;
  repeat match goal with
         | [ H: ret ?a0 ?a |- _ ] => replace (ret a0 a) with (ret a0 ↝ a) in H by reflexivity
         | [ |- context[ret ?a0 ?a] ] => replace (ret a0 a) with (ret a0 ↝ a) by reflexivity
         end; computes_to_inv; SameValues_Fiat_t.
  Transparent computes_to.
  unfold computes_to; subst; SameValues_Fiat_t; reflexivity.
  Opaque computes_to.
Qed.

Hint Rewrite WrapComp_W_rewrite : compile_simple_db.

Ltac is_comp c :=
  match type of c with
  | @Comp _ => idtac
  | _ => fail 1
  end.

Ltac compile_if t tp fp :=
  is_comp tp; is_comp fp;
  let test_var := gensym "test" in
  apply (CompileIf (tmp := test_var)).

Ltac compile_if_in_place t tp fp :=
  is_comp tp; is_comp fp;
  let test_var := gensym "test" in
  apply (CompileIf_InPlace (tmp := test_var)).

Ltac find_function_in_env function env :=
  match goal with
  | [ H: GLabelMap.MapsTo ?k function env |- _ ] => constr:(k)
  | _ => let key := GLabelMapUtils.find_fast function env in
        match key with
        | Some ?k => k
        end
  end.

Ltac compile_external_call_SCA av env fWW arg ext :=
  let fpointer := find_function_in_env (Axiomatic (FacadeImplementationWW av fWW)) env in
  let varg := find_fast arg ext in
  match varg with
  | Some ?varg =>
    apply (CompileCallFacadeImplementationWW (fpointer := fpointer) (varg := varg))
  | None =>
    let varg := gensym "arg" in
    apply (CompileCallFacadeImplementationWW_full (fpointer := fpointer) (varg := varg))
  end.

Ltac match_ProgOk continuation :=
  lazymatch goal with
  | [  |- {{ ?pre }} ?prog {{ ?post }} ∪ {{ ?ext }} // ?env ] => first [continuation prog pre post ext env | fail]
  | _ => fail "Goal does not look like a ProgOk statement"
  end.

Ltac compile_simple_internal env cmp ext :=
  match cmp with
  | ret (SCA ?av (?op ?lhs ?rhs)) => let facade_op := translate_op op in compile_binop av facade_op lhs rhs ext
  | ret (@bool2val ?av (?op ?lhs ?rhs)) => let facade_op := translate_op op in compile_binop av facade_op lhs rhs ext
  | ret (@bool2val ?av (@dec2bool _ _ (?op ?lhs ?rhs))) => let facade_op := translate_op op in compile_binop av facade_op lhs rhs ext
  | ret (SCA _ ?w) => compile_constant w; compile_do_side_conditions
  | ret (SCA ?av ?w) => compile_read (SCA av w) ext; compile_do_side_conditions
  | ret (SCA ?av (?f ?w)) => compile_external_call_SCA av env f w ext
  | (if ?t then ?tp else ?fp) => compile_if t tp fp
  end.

Ltac compile_simple name cmp :=
  debug "Compiling simple pattern";
  autorewrite with compile_simple_db;  (* Rewrite using user-provided lemmas *)
  match_ProgOk ltac:(fun prog pre post ext env => (* Recapture cmp after rewriting *)
                       match constr:(pre, post) with
                       | (?tenv, Cons ?s ?cmp (fun _ => ?tenv)) => compile_simple_internal env cmp ext
                       end).

Ltac compile_simple_in_place_internal env cmp cmp' tenv ext :=
  match cmp' with
  | (if ?t then ?tp else ?fp) => compile_if_in_place t tp fp
  | _ => fail "compile_simple_internal can't compile this:" cmp cmp' tenv ext
  end.

Ltac compile_simple_in_place name cmp cmp' :=
  debug "Compiling simple pattern";
  autorewrite with compile_simple_db;  (* Rewrite using user-provided lemmas *)
  match_ProgOk ltac:(fun prog pre post ext env => (* Recapture cmp after rewriting *)
                       match constr:(pre, post) with
                       | ([[`?k <~~ ?cmp as _]] :: ?tenv, [[`?k <~~ ?cmp' as _]] :: ?tenv) => compile_simple_in_place_internal env cmp cmp' tenv ext
                       end).

Ltac compile_skip :=
  debug "Compiling empty program";
  apply CompileSkip.

Lemma WrapComp_W_computes_to {av} {cmp: Comp W} {v: Value av} :
  WrapComp_W cmp ↝ v ->
  { v' | cmp ↝ v' /\ v = SCA _ v' }.
Proof.
  intros; destruct v.
  - exists w; intuition congruence.
  - exfalso; assumption.
Qed.

Ltac compile_do_unwrap_W val :=
  progress repeat match goal with
  | [ H: WrapComp_W _ ↝ val |- _ ] =>
    let eqn := fresh in
    destruct (WrapComp_W_computes_to H) as [? (? & eqn)];
      rewrite eqn in *; clear eqn H
  end.

Ltac compile_do_unwrap type wrapper key cmp tail val :=
  lazymatch type with
  | W => compile_do_unwrap_W val
  | _ => fail 1 "Don't know how to unwrap" type
  end;
  let wrapper_head := head_constant wrapper in
  cbv beta iota delta [WrappedCons wrapper_head].

(*! FIXME: Why is this first [ ... | fail] thing needed? If it's removed then the lazy match falls through *)
Ltac compile_ProgOk p pre post ext env :=
  is_evar p;
  lazymatch constr:(pre, post, ext) with
  | (_,                           (@WrappedCons _ ?T ?wrapper ?k ?cmp ?tl) ?v, _) => first [compile_do_unwrap T wrapper k cmp tl v | fail ]
  | (Cons ?k ?cmp _,              Cons ?k ?cmp _,                              _) => first [compile_do_chomp k | fail ]
  | (Cons (Some ?k) ?cmp _,       Cons None ?cmp _,                            _) => first [compile_dealloc k cmp | fail ]
  | (_,                           Cons None ?cmp ?tl,                          _) => first [compile_do_alloc cmp tl | fail ]
  | (_,                           Cons ?k (Bind ?compA ?compB) ?tl,            _) => first [compile_do_bind k compA compB tl | fail ]
  | (?tenv,                       Cons (Some ?k) ?cmp (fun _ => ?tenv),           _) => first [compile_simple k cmp | fail ]
  | ([[`?k <~~ ?cmp as _]] :: ?tenv, [[`?k <~~ ?cmp' as _]] :: ?tenv,                _) => first [compile_simple_in_place k cmp cmp' | fail ]
  | (?tenv,                       Cons ?k ?cmp ?tl,                            _) => first [compile_do_cons | fail ] (* FIXME *)
  | (?tenv,                       ?tenv,                                       _) => first [compile_skip | fail ]
  end.

(* Ltac debug_match_ProgOk := *)
(*   lazymatch goal with *)
(*   | [  |- {{ ?pre }} ?prog {{ ?post }} ∪ {{ ?ext }} // ?env ] => *)
(*     pose prog as debug_prog; pose post as debug_post; pose ext as debug_ext; pose env as debug_env; pose pre as debug_pre *)
(*   | _ => fail "Goal does not look like a ProgOk statement" *)
(*   end. *)

Lemma push_if :
  forall {A B} (f: A -> B) (x y: A) (b: bool),
    f (if b then x else y) = (if b then f x else f y).
Proof.
  intros; destruct b; reflexivity.
Qed.

Ltac is_pushable_head_constant f :=
  let hd := head_constant f in
  match hd with
  | Cons => fail 1
  | _ => idtac
  end.

Ltac is_dec term :=
  match type of term with
  | {?p} + {?q}  => idtac
  end.

Ltac compile_rewrite :=
  match goal with
  (*! FIXME Why is setoid needed here? !*)
  | [  |- appcontext[if ?b then ?x else ?y] ] => is_dec b; setoid_rewrite (dec2bool_correct b x y)
  | [  |- appcontext[?f (if ?b then ?x else ?y)] ] => is_pushable_head_constant f; setoid_rewrite (push_if f x y b)
  end.

Definition IsFacadeProgramImplementing {av} cmp env prog :=
  {{ @Nil av }}
    prog
  {{ [[`"ret" <~~ cmp as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // env.

Definition FacadeProgramImplementing {av} cmp env :=
  sigT (@IsFacadeProgramImplementing av cmp env).

Notation "'Facade' 'program' 'implementing' cmp 'with' env" :=
  (FacadeProgramImplementing cmp env) (at level 0).

Ltac start_compiling :=
  match goal with
  | [  |- FacadeProgramImplementing _ ?env ] =>
    unfold FacadeProgramImplementing, IsFacadeProgramImplementing; econstructor
  end.

Ltac compile_step :=
  idtac;
  match goal with
  | _ => start_compiling
  | _ => compile_rewrite
  | _ => compile_do_side_conditions
  | _ => match_ProgOk compile_ProgOk
  end.

Set Implicit Arguments.

(* Weak version: should talk about injecting in and projecting out of the main type *)
Definition FacadeImplementationOfMutation av (fAA: W -> av -> av) : AxiomaticSpec av.
  refine {|
      PreCond := fun args => exists w x, args = (ADT x) :: (SCA _ w) :: nil;
      PostCond := fun args ret => exists w x, args = (ADT x, Some (fAA w x)) :: (SCA _ w, None) :: nil /\ ret = SCA _ (Word.natToWord 32 0)
    |}; spec_t.
Defined.

Definition FacadeImplementationOfConstructor av (fAA: av) : AxiomaticSpec av.
  refine {|
      PreCond := fun args => args = nil;
      PostCond := fun args ret => args = nil /\ ret = (ADT fAA)
    |}; spec_t.
Defined.

Definition FacadeImplementationOfCopy av : AxiomaticSpec av.
  refine {|
      PreCond := fun args => exists x, args = (ADT x) :: nil;
      PostCond := fun args ret => exists x, args = (ADT x, Some x) :: nil /\ ret = (ADT x)
    |}; spec_t.
Defined.

Definition FacadeImplementationOfDestructor av (fAA: av) : AxiomaticSpec av.
  refine {|
      PreCond := fun args => exists x, args = (ADT x) :: nil;
      PostCond := fun args ret => exists x, args = (ADT x, None) :: nil /\ ret = SCA _ (Word.natToWord 32 0)
    |}; spec_t.
Defined.

Lemma SameValues_Mutation_helper:
  forall (av : Type) (vsrc vret : StringMap.key)
    (ext : StringMap.t (Value av)) (tenv : Telescope av)
    (initial_state : State av) (x : av),
    vret <> vsrc ->
    vret ∉ ext ->
    NotInTelescope vret tenv ->
    StringMap.MapsTo vsrc (ADT x) initial_state ->
    initial_state ≲ tenv ∪ ext ->
    [vsrc <-- ADT x]::M.remove vret initial_state ≲ tenv ∪ ext.
Proof.
  intros.
  repeat match goal with
         | _ => rewrite <- remove_add_comm by congruence
         | [ H: StringMap.MapsTo ?k ?v ?st |- context[StringMap.add ?k ?v ?st] ] => rewrite <- (add_redundant_cancel H)
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.

Hint Resolve SameValues_Mutation_helper : call_helpers_db.

Lemma CompileCallFacadeImplementationOfCopy:
  forall {av} {env},
  forall fpointer vsrc,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfCopy av)) env ->
    forall vret adt ext tenv,
      vret <> vsrc ->
      vret ∉ ext ->
      NotInTelescope vret tenv ->
      StringMap.MapsTo vsrc (ADT adt) ext ->
      {{ tenv }}
        (Call vret fpointer (vsrc :: nil))
      {{ [[ vret <-- ADT adt as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.

Lemma Cons_PushExt':
  forall {av} key tenv ext v (st: State av),
    st ≲ Cons (Some key) (ret v) (fun _ => tenv) ∪ ext ->
    st ≲ tenv ∪ [key <-- v] :: ext.
Proof.
  intros; change tenv with ((fun _ => tenv) v); eauto using Cons_PushExt.
Qed.

Hint Resolve Cons_PushExt' : SameValues_db.

Lemma SameValues_add_SCA_notIn_ext :
  forall {av} k v st tenv ext,
    k ∉ ext ->
    NotInTelescope k tenv ->
    st ≲ tenv ∪ ext ->
    StringMap.add k (SCA av v) st ≲ tenv ∪ ext.
Proof.
  eauto with SameValues_db.
Qed.

Hint Resolve SameValues_add_SCA_notIn_ext : SameValues_db.

Lemma CompileCallFacadeImplementationOfMutation_Alloc:
  forall {av} {env} fADT,
  forall fpointer varg vtmp (SCAarg: W) ADTarg tenv,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation fADT)) env ->
    forall vret ext pSCA pADT,
      vret <> varg ->
      vtmp <> varg ->
      vtmp <> vret ->
      vret ∉ ext ->
      vtmp ∉ ext ->
      varg ∉ ext ->
      @NotInTelescope av vret tenv ->
      @NotInTelescope av vtmp tenv ->
      @NotInTelescope av varg tenv ->
      {{ tenv }}
        pSCA
      {{ [[ varg <-- SCA _ SCAarg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[ varg <-- SCA _ SCAarg as _]] :: tenv }}
        pADT
      {{ [[ varg <-- SCA _ SCAarg as _]] :: [[ vret <-- ADT ADTarg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ tenv }}
        Seq pSCA (Seq pADT (Call vtmp fpointer (vret :: varg :: nil)))
      {{ [[ vret <-- ADT (fADT SCAarg ADTarg) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.

Ltac wipe :=
  repeat match goal with
         | [ H: ?a = ?a |- _ ] => clear dependent H
         | [ H: forall _: State _, _ |- _ ] => clear dependent H
         | [ H: ?h |- _ ] =>
           let hd := head_constant h in
           match hd with
           | @Learnt => clear dependent H
           | @Safe => clear dependent H
           | @ProgOk => clear dependent H
           end
         end.

(* Lemma CompileCallFacadeImplementationOfMutationB: *)
(*   forall {av} {env} fADT, *)
(*   forall fpointer varg vtmp (SCAarg: W) (ADTarg: av) tenv, *)
(*     GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation fADT)) env -> *)
(*     forall vret ext pSCA, *)
(*       vret <> varg -> *)
(*       vtmp <> varg -> *)
(*       vtmp <> vret -> *)
(*       vret ∉ ext -> *)
(*       vtmp ∉ ext -> *)
(*       varg ∉ ext -> *)
(*       NotInTelescope vret tenv -> *)
(*       NotInTelescope vtmp tenv -> *)
(*       NotInTelescope varg tenv -> *)
(*       {{ [[ vret <-- ADT ADTarg as _]] :: tenv }} *)
(*         pSCA *)
(*       {{ [[ vret <-- ADT ADTarg as _]] :: [[ varg <-- SCA _ SCAarg as _]] :: tenv }} ∪ {{ ext }} // env -> *)
(*       {{ [[ vret <-- ADT ADTarg as _]] :: tenv }} *)
(*         Seq pSCA (Call vtmp fpointer (vret :: varg :: nil)) *)
(*       {{ [[ vret <-- ADT (fADT SCAarg ADTarg) as _]] :: [[ varg <-- SCA _ SCAarg as _]] :: tenv }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   repeat match goal with *)
(*          | _ => SameValues_Facade_t_step *)
(*          | _ => facade_cleanup_call *)
(*          end. *)
(* Qed. *)

Lemma CompileCallFacadeImplementationOfMutation_Replace:
  forall {av} {env} fADT,
  forall fpointer varg vtmp (SCAarg: W) (ADTarg: av) tenv,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation fADT)) env ->
    forall vret ext pSCA,
      vret <> varg ->
      vtmp <> varg ->
      vtmp <> vret ->
      vret ∉ ext ->
      vtmp ∉ ext ->
      varg ∉ ext ->
      NotInTelescope vret tenv ->
      NotInTelescope vtmp tenv ->
      NotInTelescope varg tenv ->
      {{ [[ vret <-- ADT ADTarg as _]] :: tenv }}
        pSCA
      {{ [[ vret <-- ADT ADTarg as _]] :: [[ varg <-- SCA _ SCAarg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[ vret <-- ADT ADTarg as _]] :: tenv }}
        Seq pSCA (Call vtmp fpointer (vret :: varg :: nil))
      {{ [[ vret <-- ADT (fADT SCAarg ADTarg) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.

Lemma CompileCallFacadeImplementationOfConstructor:
  forall {av} {env} adt tenv,
  forall fpointer,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfConstructor adt)) env ->
    forall vret ext,
      vret ∉ ext ->
      NotInTelescope vret tenv ->
      {{ tenv }}
        (Call vret fpointer nil)
      {{ [[ vret <-- @ADT av adt as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.

Lemma WeakEq_add_MapsTo :
  forall {av} k v m1 m2,
    StringMap.MapsTo k v m1 ->
    WeakEq (StringMap.add k v m1) m2 ->
    @WeakEq av m1 m2.
Proof.
  intros; rewrite add_redundant_cancel; eassumption.
Qed.

Hint Resolve WeakEq_add_MapsTo : call_helpers_db.
Hint Resolve WeakEq_add : call_helpers_db.

Require Import Fiat.CertifiedExtraction.FacadeNotations.
Hint Unfold DummyArgument : MapUtils_unfold_db.

Definition extract_facade := proj1_sig.

Opaque Word.natToWord.

Definition EmptyEnv : Env unit := (GLabelMap.GLabelMap.empty (FuncSpec unit)).

Example simple :
  Facade program implementing ( x <- ret (SCA unit (Word.natToWord 32 1));
                                y <- ret (SCA unit (Word.natToWord 32 5));
                                ret (SCA _ (Word.wplus (Word.natToWord 32 1) (Word.natToWord 32 5)))) with EmptyEnv.
Proof.
  repeat compile_step.
Defined.

Eval simpl in (extract_facade simple).

(******************************************************************************)
(*+ First example: sum two constants! *)

Example simple_binop :
  Facade program implementing ( x <- ret (Word.natToWord 32 1);
                                y <- ret (Word.natToWord 32 5);
                                ret (SCA _ (Word.wplus x y))) with EmptyEnv.
Proof.
  repeat compile_step.
Defined.

Eval simpl in (extract_facade simple_binop).

(******************************************************************************)
(*+ More constants! *)

Example harder_binop :
  Facade program implementing
         ( x <- ret (Word.natToWord 32 1);
           y <- ret (Word.natToWord 32 5);
           z <- ret (Word.natToWord 32 8);
           t <- ret (Word.natToWord 32 12);
           ret (SCA _ (Word.wplus x (Word.wplus z (Word.wminus y t)))))
with EmptyEnv.
Proof.
  repeat compile_step.
Defined.

Eval simpl in (extract_facade harder_binop).

(******************************************************************************)
(*+ We can extend the engine to call
    external functions *)

Definition Random := { x: W | True }%comp.

Definition FRandom {av} : AxiomaticSpec av.
Proof. refine {|
      PreCond := fun args => args = nil;
      PostCond := fun args ret => args = nil /\ exists w, ret = SCA av w
    |}; spec_t. Defined.

Lemma Random_characterization {av}:
  forall x : W, WrapComp_W Random ↝ SCA av x.
Proof. constructor. Qed.

Hint Immediate Random_characterization : call_helpers_db.

Lemma CompileCallRandom:
  forall {av} (env : GLabelMap.t (FuncSpec av)),
  forall fpointer tenv,
    GLabelMap.MapsTo fpointer (Axiomatic FRandom) env ->
    forall var ext,
      var ∉ ext ->
      NotInTelescope var tenv ->
      {{ tenv }}
        Call var fpointer []
      {{ [[ ` var <~~ WrapComp_W Random as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.

Ltac compile_random :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | (?tenv, Cons ?s (@WrapComp_W ?av Random) (fun _ => ?tenv)) =>
              let fpointer := find_function_in_env
                               (Axiomatic (@FRandom av)) env in
              apply (CompileCallRandom (fpointer := fpointer))
            end).

(*! We then tell compiler that the definition is available: *)

Definition BasicEnv :=
  (GLabelMap.add ("std", "rand") (Axiomatic FRandom))
    (GLabelMap.empty (FuncSpec unit)).

(*! And we can now compile programs using that function! *)

Example random_sample :
  Facade program implementing ( x <- Random;
                                y <- Random;
                                ret (SCA _ (Word.wminus (Word.wplus x x)
                                                        (Word.wplus y y))))
with BasicEnv.
Proof.
  repeat (compile_step || compile_random).
Defined.

Eval simpl in (extract_facade random_sample).

(******************************************************************************)
(*+ We also have support for conditionals,
    and external scalar functions *)

Definition Square x :=
  @Word.wmult 32 x x.

Definition EnvWithSquare {av} :=
  (GLabelMap.add ("std", "rand") (Axiomatic FRandom))
    ((GLabelMap.add ("mylib", "square") (Axiomatic (FacadeImplementationWW av Square)))
       (GLabelMap.empty (FuncSpec av))).

Example random_test :
  Facade program implementing ( x <- Random;
                                y <- Random;
                                z <- Random;
                                ret (SCA unit (if IL.weqb x y then
                                                 (Word.wplus z z)
                                               else
                                                 if IL.wltb x y then
                                                   z
                                                 else
                                                   (Square z)))) with EnvWithSquare.
Proof.
  repeat (compile_step || compile_random).
Defined.

Eval simpl in (extract_facade random_test).

(******************************************************************************)
(*+ And we can easily add more functions *)

Definition Cube (x: W) := (Word.wmult x (Word.wmult x x)).

Definition EnvWithCubeAsWell {av} :=
  (GLabelMap.add ("std", "rand") (Axiomatic FRandom))
    ((GLabelMap.add ("mylib", "square") (Axiomatic (FacadeImplementationWW av Square)))
       ((GLabelMap.add ("mylib", "cube") (Axiomatic (FacadeImplementationWW av Cube)))
          (GLabelMap.empty (FuncSpec av)))).

Example random_test_with_cube :
  Facade program implementing ( x <- Random;
                                y <- Random;
                                z <- Random;
                                ret (SCA unit (if IL.weqb x y then
                                                 (Word.wplus z z)
                                               else
                                                 if IL.wltb x y then
                                                   z
                                                 else
                                                   (Cube z)))) with EnvWithCubeAsWell.
Proof.
  repeat (compile_step || compile_random).
Defined.

Eval simpl in (extract_facade random_test_with_cube).

(******************************************************************************)
(*+ To conclude, a bit of ADT stuff: *)

Definition MyEnvW :=
  (GLabelMap.add ("std", "rand") (Axiomatic FRandom))
    ((GLabelMap.add ("std", "nil") (Axiomatic (FacadeImplementationOfConstructor nil)))
       ((GLabelMap.add ("std", "push") (Axiomatic (FacadeImplementationOfMutation cons)))
          (GLabelMap.empty _))).

Ltac compile_mutation_alloc :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       match constr:(pre, post) with
                       | (?tenv, Cons ?s (ret (ADT (?f _ _))) (fun _ => ?tenv)) =>
                         let fpointer := find_function_in_env
                                          (Axiomatic (FacadeImplementationOfMutation f)) env in
                         let arg := gensym "arg" in
                         let tmp := gensym "tmp" in
                         apply (CompileCallFacadeImplementationOfMutation_Alloc
                                  (fpointer := fpointer) (varg := arg) (vtmp := (DummyArgument tmp)))
                       end).

Ltac compile_mutation_replace :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       match constr:(pre, post) with
                       | ([[?s <-- ADT ?adt as _]] :: ?tenv, [[?s <-- ADT (?f _ ?adt) as _]] :: ?tenv) =>
                         let fpointer := find_function_in_env
                                          (Axiomatic (FacadeImplementationOfMutation f)) env in
                         let arg := gensym "arg" in
                         let tmp := gensym "tmp" in
                         apply (CompileCallFacadeImplementationOfMutation_Replace
                                  (fpointer := fpointer) (varg := arg) (vtmp := (DummyArgument tmp)))
                       end).

Ltac compile_constructor :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       match constr:(pre, post) with
                       | (?tenv, Cons ?s (ret (ADT ?adt)) (fun _ => ?tenv)) =>
                         let fpointer := find_function_in_env
                                          (Axiomatic (FacadeImplementationOfConstructor adt)) env in
                         apply (CompileCallFacadeImplementationOfConstructor
                                  tenv (fpointer := fpointer))
                       end).

(******************************************************************************)
(*+ This example returns a list containing
    a semi-random number > 0 *)

Example random_test_with_adt :
  Facade program implementing ( x <- Random;
                                ret (ADT (if IL.weqb x 0 then
                                            (Word.natToWord 32 1 : W) :: nil
                                          else
                                            x :: nil))) with MyEnvW.
Proof.
  repeat (compile_step || compile_random || compile_constructor || compile_mutation_alloc).
Defined.

Eval simpl in (extract_facade random_test_with_adt).

(******************************************************************************)

Example test_with_adt :
    sigT (fun prog => forall tail, {{ [[`"ret"  <~~  ret (ADT tail) as _ ]] :: Nil }}
                             prog
                           {{ [[`"ret"  <~~  ( x <- Random;
                                             ret (ADT (x :: tail))) as _]] :: Nil }} ∪ {{ ∅ }}
                           // MyEnvW).
Proof.
  econstructor; intros.
  repeat (compile_random || compile_mutation_replace || compile_step).
Defined.

Eval simpl in (extract_facade test_with_adt).

(******************************************************************************)
(*+ Most exciting example yet:
    - Sample two numbers,
    - take the smallest one,
    - push it into a list *)

Example other_test_with_adt :
    sigT (fun prog => forall seq, {{ [[`"ret" <~~ ret (ADT seq) as _ ]] :: Nil }}
                            prog
                          {{ [[`"ret" <~~ ( x <- Random;
                                          y <- Random;
                                          ret (ADT ((if IL.wltb x y then x else y) :: seq))) as _]] :: Nil }} ∪ {{ ∅ }} // MyEnvW).
Proof.
  econstructor; intros.
  repeat (compile_random || compile_mutation_replace || compile_step).
Defined.

Eval simpl in (extract_facade other_test_with_adt).

(******************************************************************************)
Example other_test_with_adt' :
    sigT (fun prog => forall seq, {{ [[`"ret" <~~ ret (ADT seq) as _ ]] :: Nil }}
                            prog
                          {{ [[`"ret" <~~ ( x <- Random;
                                          y <- Random;
                                          ret (ADT (if IL.wltb x y then x :: seq else y :: seq))) as _]] :: Nil }} ∪ {{ ∅ }} // MyEnvW).
Proof.
  econstructor; intros.
  repeat (compile_random || compile_mutation_replace || compile_step).
Defined.

Eval simpl in (extract_facade other_test_with_adt').

(* FIXME: The tricky part here is the dependency on the order of the lemmas *)

Lemma CompileSeq :
  forall {av} (tenv1 tenv1' tenv2: Telescope av) ext env p1 p2,
    {{ tenv1 }}
      p1
    {{ tenv1' }} ∪ {{ ext }} // env ->
    {{ tenv1' }}
      p2
    {{ tenv2 }} ∪ {{ ext }} // env ->
    {{ tenv1 }}
      (Seq p1 p2)
    {{ tenv2 }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Definition List_pop : AxiomaticSpec (list W).
  refine {|
      PreCond := fun args =>
                   exists h t,
                     args = (ADT (cons h t)) :: nil;
      PostCond := fun args ret =>
                    exists h t,
                      args = (ADT (cons h t), Some t) :: nil /\
                      ret = SCA (list W) h
    |}; spec_t.
Defined.

Definition List_empty : AxiomaticSpec (list W).
  refine {|
      PreCond := fun args =>
                   exists l,
                     args = (ADT l) :: nil;
      PostCond := fun args ret =>
                    exists l,
                      args = (ADT l, Some l) :: nil /\
                      exists w, ret = SCA _ w /\ w = bool2w (match l with
                                                       | nil => true
                                                       | _ => false
                                                       end)
    |}; spec_t.
Defined.

Lemma SameValues_PopExt':
  forall (av : Type) (key : StringMap.key) (tail : Telescope av)
    (v0 : Value av) (ext initial_state : StringMap.t (Value av)),
    key ∉ ext ->
    initial_state ≲ tail ∪ [key <-- v0]::ext ->
    StringMap.remove key initial_state ≲ tail ∪ ext.
Proof.
  intros.
  change tail with ((fun (_: Value av) => tail) v0).
  eauto using SameValues_PopExt.
Qed.

Hint Resolve SameValues_PopExt' : SameValues_db.

Lemma CompileCallEmpty:
  forall (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec (list W))) tenv ext
    (fempty : GLabelMap.key) (lst : list W),
    vlst <> vtest ->
    vtest ∉ ext ->
    NotInTelescope vtest tenv ->
    vlst ∉ ext ->
    NotInTelescope vlst tenv ->
    GLabelMap.MapsTo fempty (Axiomatic List_empty) env ->
    {{ [[vlst <-- ADT lst as _]]::tenv }}
      Call vtest fempty [vlst]
      {{ [[vtest <-- SCA (list W) (bool2w match lst with
                                        | nil => true
                                        | _ :: _ => false
                                        end) as _]]::[[vlst <-- ADT lst as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call); facade_eauto.
Qed.

Lemma TelEq_swap :
  forall {av} {ext} k k' v v' (tenv: Telescope av),
    k <> k' ->
    k ∉ ext ->
    k' ∉ ext ->
    TelEq ext ([[k <-- v as _]]::[[k' <-- v' as _]]::tenv) ([[k' <-- v' as _]]::[[k <-- v as _]]::tenv).
Proof.
  intros; unfold TelEq; intros; SameValues_Facade_t;
  eapply Cons_PopExt; try decide_not_in;
  eapply Cons_PopExt; try decide_not_in;
  erewrite SameValues_Morphism;
  try rewrite add_add_comm;
  try reflexivity;
  auto.
Qed.

Hint Unfold is_true is_false eval_bool eval eval_binop_m eval_binop IL.evalTest : facade_db.

Lemma is_true_eq_MapsTo :
  forall av st var val,
    is_true st (TestE IL.Eq (Var var) (Const val)) ->
    StringMap.MapsTo var (SCA av val) st.
Proof.
  intros.
  Transparent Word.natToWord.
  repeat autounfold with facade_db in *.

  repeat match goal with
         | _ => cleanup
         | _ => StringMapUtils.normalize
         | [ H: context[StringMap.find ?k ?v] |- _ ] => destruct (StringMap.find k v) eqn:eq0
         | [ H: context[IL.weqb ?a ?b] |- _ ] => destruct (IL.weqb a b) eqn:eq1
         | [ H: Value _ |- _ ] => destruct H
         | [ H: _ = Some _ |- _ ] => compute in H
         end.

  replace val with w by admit; assumption. (* ask Perry *)
  (* replace (IL.weqb val val) with true by admit; reflexivity. *)
  Opaque Word.natToWord.
Qed.

Lemma is_true_is_false_contradiction :
  forall av expr st,
    @is_true av expr st ->
    @is_false av expr st ->
    False.
Proof.
  unfold is_true, is_false; intros; congruence.
Qed.

Lemma CompileDeallocSCA_discretely :
  forall {av} tenv tenv' ext env k v prog,
    k ∉ ext ->
    NotInTelescope k tenv ->
    {{ [[k <-- SCA av v as _]] :: tenv }} prog {{ [[k <-- SCA av v as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[k <-- SCA av v as _]] :: tenv }} prog {{ tenv' }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

(* FIXME CompileDeallocSCA_discretely is enough to get rid of most SKIPs when deallocating SCAs *)

Definition LiftPropertyToTelescope {av} ext (property: _ -> Prop) : Telescope av -> Prop :=
  fun tenv => forall st, st ≲ tenv ∪ ext -> property st.

Ltac LiftPropertyToTelescope_t :=
  match goal with
  | [ H: LiftPropertyToTelescope ?ext _ ?tenv, H': ?st ≲ ?tenv ∪ ?ext |- _ ] => learn (H st H')
  end.

Ltac TelEq_morphism_t :=
  match goal with
  | _ => cleanup
  | [ H: forall _, _ -> _, H': _ |- _ ] => learn (H _ H')
  | [ H: forall _, _ <-> _ |- _ ] => rewrite H
  | [ H: forall _, _ <-> _, H': _ |- _ ] => setoid_rewrite H in H'
  end.

Add Parametric Morphism {A} ext : (@LiftPropertyToTelescope A ext)
    with signature (pointwise_relation _ iff ==> TelEq ext ==> iff)
      as Liftpropertytotelescope_TelEq_morphism.
Proof.
  unfold LiftPropertyToTelescope, pointwise_relation;
  repeat match goal with
         | _ => TelEq_morphism_t
         | [ H': TelEq ?ext ?t1 _ |- context[_ ≲ ?t1 ∪ ?ext] ]        => setoid_rewrite H'
         | [ H': TelEq ?ext ?t1 _,  H: context[_ ≲ ?t1 ∪ ?ext] |- _ ] => setoid_rewrite H' in H
         end.
Qed.

Lemma CompileWhileFalse:
  forall (env : GLabelMap.t (FuncSpec (list W))) (ext : StringMap.t (Value (list W)))
    (tenv : Telescope (list W)) tenv' test body,
    TelEq ext tenv tenv' ->
    (LiftPropertyToTelescope ext (fun st => is_false st test) tenv) ->
    {{ tenv }} (DFacade.While test body) {{ tenv' }} ∪ {{ ext }} // env.
Proof.
  intros * H **.
  rewrite <- H; clear H.
  repeat match goal with
         | [ H: forall st, st ≲ _ ∪ _ -> _, H': ?st ≲ _ ∪ _ |- _ ] => learn (H _ H')
         | [ H: is_true ?t ?st, H': is_false ?t ?st |- _ ] => exfalso; exact (is_true_is_false_contradiction H H')
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         | _ => LiftPropertyToTelescope_t
         | _ => apply SafeWhileFalse
         | [ H: RunsTo _ (DFacade.While _ _) _ _ |- _ ] => inversion H; unfold_and_subst; clear H
         end.
Qed.

Lemma CompileWhileTrue:
  forall (env : GLabelMap.t (FuncSpec (list W))) (ext : StringMap.t (Value (list W)))
    (tenv : Telescope (list W)) tenv' tenv'' test body,
    (LiftPropertyToTelescope ext (fun st => is_true st test) tenv) ->
    {{ tenv }}  body                      {{ tenv' }}  ∪ {{ ext }} // env ->
    {{ tenv' }} (DFacade.While test body) {{ tenv'' }} ∪ {{ ext }} // env ->
    {{ tenv }}  (DFacade.While test body) {{ tenv'' }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | [ H: forall st, st ≲ _ ∪ _ -> _, H': ?st ≲ _ ∪ _ |- _ ] => learn (H _ H')
         | [ H: is_true ?t ?st, H': is_false ?t ?st |- _ ] => exfalso; exact (is_true_is_false_contradiction H H')
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         | _ => LiftPropertyToTelescope_t
         | _ => apply SafeWhileTrue
         | [ H: RunsTo _ (DFacade.While _ _) _ _ |- _ ] => inversion H; unfold_and_subst; clear H
         end.
Qed.

Lemma CompileWhileFalse_Loop:
  forall (vtest : StringMap.key) 
    (env : GLabelMap.t (FuncSpec (list W))) (ext : StringMap.t (Value (list W))) 
    (tenv : Telescope (list W)) tenv' body,
    TelEq ext tenv tenv' ->
    vtest ∉ ext ->
    NotInTelescope vtest tenv ->
    {{ [[vtest <-- SCA (list W) (Word.natToWord 32 1) as _]]::tenv }}
      (DFacade.While (TestE IL.Eq vtest O) body)
    {{ tenv' }} ∪ {{ ext }} // env.
Proof.
  intros * H **.
  rewrite <- H.
  apply CompileDeallocSCA_discretely; eauto.
  apply CompileWhileFalse.
  reflexivity.
  unfold LiftPropertyToTelescope;
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         | _ => progress unfold is_true, is_false, eval_bool, eval; simpl
         end.
Qed.

(* setoid_rewrite (TelEq_swap (k := vhead) (k' := vlst)). *)
(* lazymatch goal with *)
(* | [ |- context[ [[?k <-- _ as _]] :: [[vlst <-- _ as _]] :: _ ] ] => setoid_rewrite (TelEq_swap (k := k) (k' := vlst)) *)
(* end. *)

Add Parametric Morphism {A} ext : (fun key comp tail => @Cons A key comp (fun _ => tail))
    with signature (eq ==> Monad.equiv ==> TelEq ext ==> (TelEq ext))
      as Cons_MonadEquiv_morphism_simple.
Proof.
  intros; apply Cons_MonadEquiv_morphism; try red; eauto.
Qed.

Fixpoint DropName {A} k (t: Telescope A) :=
  match t with
  | Nil => Nil
  | Cons key val tail => Cons (match key with 
                              | Some _key => if string_dec _key k then None else key
                              | None => key
                              end) val (fun v => (DropName k (tail v)))
  end.

Ltac inversion' H :=
  inversion H; subst; clear H.

(* Inductive AlwaysMapsTo {A} (k: StringMap.key) v : (Telescope A) -> Prop := *)
(* | AlwaysMapsToTop : forall cmp tail, (forall vv, cmp ↝ vv -> vv = v) -> AlwaysMapsTo k v (Cons (Some k) cmp tail) *)
(* | AlwaysMapsToRec : forall k' cmp tail, k' <> Some k -> (exists vv, cmp ↝ vv) -> (forall vv, cmp ↝ vv -> AlwaysMapsTo k v (tail vv)) -> AlwaysMapsTo k v (Cons k' cmp tail). *)

(* Ltac AlwaysMapsTo_t := *)
(*   match goal with *)
(*   | [ H: AlwaysMapsTo _ _ Nil |- _ ] => inversion' H *)
(*   | [ H: AlwaysMapsTo _ _ (Cons _ _ _) |- _ ] => inversion' H *)
(*   | [ H: forall vv, ?v ↝ vv -> _, H': ?v ↝ _ |- _ ] => learn (H _ H') *)
(*   end. *)

(* Lemma SameValues_AlwaysMapsTo_MapsTo : *)
(*   forall {av} (tenv: Telescope av) k v ext st, *)
(*     AlwaysMapsTo k v tenv -> *)
(*     st ≲ tenv ∪ ext -> *)
(*     StringMap.MapsTo k v st. *)
(* Proof. *)
(*   Time induction tenv; *)
(*   repeat match goal with *)
(*          | _ => AlwaysMapsTo_t || SameValues_Facade_t_step (* FIXME why is this faster than two empty patterns? *) *)
(*          | [ H: ?key <> Some _ |- _ ] => destruct key *)
(*          end; eauto using MapsTo_remove. *)
(* Qed. *)

Lemma DropName_remove :
  forall {av} (tenv: Telescope av) k ext st,
    k ∉ ext ->
    st ≲ tenv ∪ ext ->
    StringMap.remove k st ≲ (DropName k tenv) ∪ ext.
Proof.
  induction tenv;
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | [ key: option string |- _ ] => destruct key
         | [  |- context[string_dec ?x ?y] ] => destruct (string_dec x y)
         | _ => progress simpl
         | [  |- exists _, _ ] => eexists
         end;
  try solve [simpl; eauto using M.remove_2 with SameValues_db];
  [ rewrite <- remove_remove_redundant | rewrite remove_remove_comm ];
  eauto using M.remove_2.
Qed.

Hint Resolve DropName_remove : SameValues_db.

Lemma CompileCallEmpty':
  forall (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec (list W))) tenv ext
    (fempty : GLabelMap.key) (lst : list W),
    vlst <> vtest ->
    vtest ∉ ext ->
    LiftPropertyToTelescope ext (StringMap.MapsTo vlst (ADT lst)) tenv ->
    LiftPropertyToTelescope ext (fun map => not_mapsto_adt vtest map = true) tenv ->
    GLabelMap.MapsTo fempty (Axiomatic List_empty) env ->
    {{ tenv }}
      Call vtest fempty [vlst]
    {{ [[vtest <-- SCA (list W) (bool2w match lst with
                                      | nil => true
                                      | _ :: _ => false
                                      end) as _]]::(DropName vtest tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ =>  SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t
         end.
  facade_eauto.
  facade_eauto.
  rewrite <- remove_add_comm by congruence.
  apply DropName_remove.
  eauto.
  rewrite <- add_redundant_cancel; eauto.
Qed.

Lemma CompileCallPop':
  forall (vhead vlst : StringMap.key) (env : GLabelMap.t (FuncSpec (list W))) tenv ext
    (fpop : GLabelMap.key) head (tail : list W),
    vlst <> vhead ->
    vhead ∉ ext ->
    vlst ∉ ext ->
    LiftPropertyToTelescope ext (StringMap.MapsTo vlst (ADT (head :: tail))) tenv ->
    LiftPropertyToTelescope ext (fun map => not_mapsto_adt vhead map = true) tenv ->
    GLabelMap.MapsTo fpop (Axiomatic List_pop) env ->
    {{ tenv }}
      Call vhead fpop [vlst]
    {{ [[vhead <-- SCA (list W) head as _]]::[[vlst <-- ADT tail as _]]::(DropName vlst (DropName vhead tenv)) }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ =>  SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t
         end;
  facade_eauto.
Qed.

Lemma DropName_Cons_Some_neq :
  forall {av} k k' v (tail: Value av -> Telescope av),
    k <> k' ->
    (DropName k (Cons (Some k') v tail)) = (Cons (Some k') v (fun vv => DropName k (tail vv))).
Proof.
  intros; simpl.
  destruct (string_dec _ _); (congruence || reflexivity).
Qed.

Lemma DropName_Cons_Some_eq :
  forall {av} k k' v (tail: Value av -> Telescope av),
    k = k' ->
    (DropName k (Cons (Some k') v tail)) = (Cons None v (fun vv => DropName k (tail vv))).
Proof.
  intros; simpl.
  destruct (string_dec _ _); (congruence || reflexivity).
Qed.

Lemma DropName_Cons_None :
  forall {av} k v (tail: Value av -> Telescope av),
    (DropName k (Cons None v tail)) = (Cons None v (fun vv => DropName k (tail vv))).
Proof.
  intros; simpl; reflexivity.
Qed.

Inductive TelStrongEq {A} : (Telescope A) -> (Telescope A) -> Prop :=
| StrongEqNil : TelStrongEq Nil Nil
| StrongEqCons : forall k v1 v2 t1 t2, Monad.equiv v1 v2 ->
                                  (forall vv, v1 ↝ vv -> TelStrongEq (t1 vv) (t2 vv)) ->
                                  TelStrongEq (Cons k v1 t1) (Cons k v2 t2).

Ltac TelStrongEq_t :=
  match goal with
  | [ H: Monad.equiv ?b _ |- ?b ↝ ?B ] => apply (proj2 (H B))
  | [ H: Monad.equiv ?a _, H': ?a ↝ _ |- _ ] => learn (proj1 (H _) H')
  | [ H: Monad.equiv _ ?a, H': ?a ↝ _ |- _ ] => learn (proj2 (H _) H')
  | [ H: TelStrongEq _ _ |- _ ] => first [ inversion' H; fail | inversion' H; [idtac] ]
  end.

Ltac TelStrongEq_morphism_t :=
  red; intro tel; induction tel;
  repeat match goal with
         | _ => constructor
         | _ => progress intros
         | _ => TelStrongEq_t
         end.

Lemma TelStrongEq_refl {A} :
  Reflexive (@TelStrongEq A).
Proof.
  TelStrongEq_morphism_t; eauto with typeclass_instances.
Qed.

Lemma TelStrongEq_sym {A} :
  Symmetric (@TelStrongEq A).
Proof.
  TelStrongEq_morphism_t; eauto.
Qed.

Lemma TelStrongEq_trans {A} :
  Transitive (@TelStrongEq A).
Proof.
  TelStrongEq_morphism_t; eauto.
Qed.

Add Parametric Relation {A} : _ (@TelStrongEq A)
    reflexivity proved by TelStrongEq_refl
    symmetry proved by TelStrongEq_sym
    transitivity proved by TelStrongEq_trans
      as TelStrongEqRel.

Lemma DropName_NotInTelescope :
  forall {av} (tenv: Telescope av) k,
    NotInTelescope k tenv ->
    TelStrongEq (DropName k tenv) tenv.
Proof.
  induction tenv; intros; simpl.
  - reflexivity.
  - destruct key; simpl in *; cleanup;
    [ destruct (string_dec _ _); subst; cleanup | ];
    constructor; eauto with typeclass_instances.
Qed.

Add Parametric Morphism {A} : (@Cons A)
    with signature (eq ==> Monad.equiv ==> pointwise_relation _ (TelStrongEq) ==> (TelStrongEq))
      as Cons_MonadEquiv_TelStrongEq_morphism.
Proof.
  unfold pointwise_relation; intros.
  constructor; eauto.
Qed.

Lemma SameValues_TelStrongEq_1 :
  forall {A} ext (tenv1 tenv2 : Telescope A) st,
    TelStrongEq tenv1 tenv2 ->
    (st ≲ tenv1 ∪ ext <->
     st ≲ tenv2 ∪ ext).
Proof.
  induction tenv1; destruct tenv2;
  repeat match goal with
         | _ => cleanup
         | _ => TelStrongEq_t
         | [ H: Monad.equiv ?a _, H': context[?a] |- _ ] => rewrite H in H'
         | _ => SameValues_Fiat_t
         end.
  rewrite <- H; eauto.
  rewrite <- H; eauto.
  rewrite -> H; eauto.
  rewrite -> H; eauto.
Qed.

Ltac TelStrongEq_SameValue_Morphism_t :=
  repeat match goal with
         | _ => progress TelEq_morphism_t
         | [ H': TelStrongEq ?t1 _ |- context[_ ≲ ?t1 ∪ ?ext] ]        => setoid_rewrite (fun st => SameValues_TelStrongEq_1 ext st H')
         | [ H': TelStrongEq ?t1 _,  H: context[_ ≲ ?t1 ∪ ?ext] |- _ ] => setoid_rewrite (fun st => SameValues_TelStrongEq_1 ext st H') in H
         end.

Add Parametric Morphism {A} ext : (@ProgOk A ext)
    with signature (eq ==> eq ==> (TelStrongEq) ==> (TelStrongEq) ==> iff)
      as ProgOk_TelStrongEq_morphism.
Proof.
  unfold ProgOk; TelStrongEq_SameValue_Morphism_t.
Qed.

Add Parametric Morphism {A} ext : (@TelEq A ext)
    with signature ((TelStrongEq) ==> (TelStrongEq) ==> iff)
      as TelEq_TelStrongEq_morphism.
Proof.
  unfold TelEq; TelStrongEq_SameValue_Morphism_t.
Qed.


Add Parametric Morphism {A} : (@DropName A)
    with signature (eq ==> TelStrongEq ==> TelStrongEq)
      as DropName_TelStrongEq_morphism.
Proof.
  induction x; destruct y0;
  repeat match goal with
         | _ => cleanup
         | _ => TelStrongEq_t
         | _ => SameValues_Fiat_t
         end.
  constructor; eauto.
Qed.

Lemma TelEq_chomp_head :
  forall {av} k v ext tenv tenv',
    @PointWise_TelEq av ext v tenv tenv' ->
    TelEq ext (Cons k v tenv) (Cons k v tenv').
Proof.
  intros * H; rewrite H; reflexivity.
Qed.

Lemma TelEq_chomp_None_right :
  forall {av} v ext tenv tenv',
    (exists vv, v ↝ vv) ->
    @PointWise_TelEq av ext v (fun _ => tenv) tenv' ->
    TelEq ext tenv (Cons None v tenv').
Proof.
  intros * ? H; rewrite <- H; red.
  split; eauto with SameValues_db.
Qed.

Lemma TelEq_chomp_None_left :
  forall {av} v ext tenv tenv',
    (exists vv, v ↝ vv) ->
    @PointWise_TelEq av ext v tenv (fun _ => tenv') ->
    TelEq ext (Cons None v tenv) tenv'.
Proof.
  intros * ? H; rewrite H; red.
  split; eauto with SameValues_db.
Qed.

Lemma TelStrongEq_Stronger :
  forall {A} ext tenv tenv',
    @TelStrongEq A tenv tenv' ->
    TelEq ext tenv tenv'.
Proof.
  induction tenv; destruct tenv';
  repeat match goal with
         | _ => cleanup
         | _ => TelStrongEq_t
         | _ => SameValues_Fiat_t
         end.
  reflexivity.
  rewrite <- H3.
  apply TelEq_chomp_head; red; intros; eauto.
Qed.

Ltac is_dirty_telescope term :=
  match term with
  | appcontext[DropName] => idtac
  | _ => fail 1
  end.

Ltac decide_TelEq_instantiate :=
  repeat match goal with
         | [  |- TelEq _ ?from _ ] =>
           match from with
           | _ => rewrite DropName_Cons_Some_eq by congruence
           | _ => rewrite DropName_Cons_Some_neq by congruence
           | Cons None _ _ => apply TelEq_chomp_None_left; [ eexists; reflexivity | red; intros ]
           | Cons _    _ _ => apply TelEq_chomp_head; red; intros
           | context[DropName ?k ?tenv] => first [is_dirty_telescope tenv; fail 1 | rewrite (@DropName_NotInTelescope _ tenv k) by eauto]
           | _ => apply TelEq_refl
           end
         end; fail.

Ltac clean_telescope tel ext :=
  let clean := fresh in
  let type := type of tel in
  evar (clean: type);
    setoid_replace tel with clean using relation (@TelEq _ ext);
    unfold clean;
    clear clean;
    [ | decide_TelEq_instantiate ].

Ltac clean_DropName_in_ProgOk :=
  match_ProgOk ltac:(fun prog pre post ext env =>
                       try (is_dirty_telescope pre; clean_telescope pre ext);
                       try (is_dirty_telescope post; clean_telescope post ext)).


Lemma CompileLoop :
  forall lst init facadeInit facadeBody vhead vtest vlst vret env (ext: StringMap.t (Value (list W))) tenv fpop fempty,
    GLabelMap.MapsTo fpop (Axiomatic List_pop) env ->
    GLabelMap.MapsTo fempty (Axiomatic List_empty) env ->
    vtest ∉ ext ->
    NotInTelescope vtest tenv ->
    vlst ∉ ext ->
    NotInTelescope vlst tenv ->
    vret ∉ ext ->
    NotInTelescope vret tenv ->
    vhead ∉ ext ->
    NotInTelescope vhead tenv ->
    vtest <> vret ->
    vtest <> vlst ->
    vtest <> vhead ->
    vret <> vlst ->
    vret <> vhead ->
    vlst <> vhead ->
    {{ [[vlst <-- ADT lst as _]] :: tenv }}
      facadeInit
    {{ [[vret <-- SCA _ init as _]] :: [[vlst <-- ADT lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    (forall head acc s,
        {{ [[vhead <-- SCA _ head as _]] :: [[vlst <-- ADT s as _]] :: [[vtest <-- SCA _ (bool2w false) as _]] :: [[vret <-- SCA _ acc as _]] :: tenv }}
          facadeBody
        {{ [[vlst <-- ADT s as _]] :: [[vtest <-- SCA _ (bool2w false) as _]] :: [[vret <-- SCA _ (@Word.wplus 32 acc head) as _]] :: tenv }} ∪ {{ ext }} // env) ->
    {{ [[vlst <-- ADT lst as _]] :: tenv }}
      (Seq facadeInit (Fold vhead vtest vlst fpop fempty facadeBody))
    {{ [[vlst <-- ADT [] as _]] :: [[vret <-- SCA _ (fold_left (@Word.wplus 32) lst init) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  eapply CompileSeq; eauto.

  unfold Fold.
  eapply CompileSeq; eauto.

  rewrite TelEq_swap by congruence.

  Hint Extern 2 (_ ∉ _) => decide_not_in : SameValues_db.
  Hint Extern 2 (NotInTelescope _ _) => decide_NotInTelescope : SameValues_db.

  eapply CompileCallEmpty'; facade_eauto.

  red; intros;
  repeat (SameValues_Facade_t_step || facade_cleanup_call).

  red; intros;
  repeat (SameValues_Facade_t_step || facade_cleanup_call).

  first [ eapply MapsTo_SCA_not_mapsto_adt; eassumption |
          eapply not_In_Telescope_not_in_Ext_not_mapsto_adt;
            [ | | eassumption ];
            [ decide_not_in | decide_NotInTelescope ];
            fail ].
  
  clean_DropName_in_ProgOk.

  clear dependent facadeInit.
  generalize dependent init.
  induction lst; simpl; intros.

  apply CompileWhileFalse_Loop; facade_eauto; reflexivity.

  eapply CompileWhileTrue.

  (* LiftPropertyToTelescope *)
  red; intros;
  unfold is_true, is_false, eval_bool, eval; simpl;
  repeat (SameValues_Facade_t_step || facade_cleanup_call).

  eapply CompileSeq.
  eapply CompileCallPop'; eauto with SameValues_db.

  red; intros;
  repeat (SameValues_Facade_t_step || facade_cleanup_call).

  red; intros;
  repeat (SameValues_Facade_t_step || facade_cleanup_call).

  (* FIXME eauto *)
  
  first [ eapply MapsTo_SCA_not_mapsto_adt; eassumption |
          eapply not_In_Telescope_not_in_Ext_not_mapsto_adt;
            [ | | eassumption ];
            [ decide_not_in | decide_NotInTelescope ];
            fail ].
  
  eapply CompileSeq.

  clean_DropName_in_ProgOk.
  eauto.

  apply CompileCallEmpty'; facade_eauto.

  red; intros;
  repeat (SameValues_Facade_t_step || facade_cleanup_call).

  red; intros;
  repeat (SameValues_Facade_t_step || facade_cleanup_call).

  first [ eapply MapsTo_SCA_not_mapsto_adt; eassumption |
          eapply not_In_Telescope_not_in_Ext_not_mapsto_adt;
            [ | | eassumption ];
            [ decide_not_in | decide_NotInTelescope ];
            fail ].

  (* FIXME eauto *)

  clean_DropName_in_ProgOk.

  eauto.
Qed.

Print Assumptions CompileLoop.

Example other_test_with_adt'' :
    sigT (fun prog => forall seq, {{ [["arg1" <-- ADT seq as _ ]] :: Nil }}
                            prog
                          {{ [["ret" <-- SCA _ (fold_left (@Word.wplus 32) seq (Word.wordToNat 0)) as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvW).
Proof.
  econstructor; intros.


  

Example other_test_with_adt'' :
    sigT (fun prog => forall seq seq', {{ [["arg1" <-- ADT seq as _ ]] :: [["arg2" <--  ADT seq' as _]] :: Nil }}
                                 prog
                               {{ [["arg1" <-- ADT (rev_append seq seq') as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvW).
Proof.
  econstructor; intros.

  compile_step.
  compile_step.
  compile_step.
  compile_random.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_random.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  

  compile_step.
  Fail fail.
Abort.

