Require Export
        CertifiedExtraction.HintDBs
        CertifiedExtraction.Core
        CertifiedExtraction.Utils
        CertifiedExtraction.StringMapUtils.

Require Export Coq.Setoids.Setoid.

Local Open Scope map_scope.
Local Open Scope telescope_scope.

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

Lemma SameSCAs_Refl:
  forall (av : Type) (t : StringMap.t (Value av)), SameADTs t t.
Proof.
  firstorder.
Qed.

Lemma SameADTs_Refl:
  forall (av : Type) (t : StringMap.t (Value av)), SameSCAs t t.
Proof.
  firstorder.
Qed.

Lemma WeakEq_Refl:
  forall (av : Type) (t : StringMap.t (Value av)), WeakEq t t.
Proof.
  firstorder.
Qed.

Ltac rewrite_equalities :=
  match goal with
  | [ H: Some _ = Some _ |- _ ] => inversion H; subst; clear H

  | [ H: ?a = ?b |- context[?a] ] => rewrite H
  | [ H: ?a = ?b, H': context[?a] |- _ ] => rewrite H in H'

  | [ H: StringMap.Equal ?a ?b |- context[?a] ] => setoid_rewrite H
  | [ H: StringMap.Equal ?a ?b, H': context[?a] |- _ ] => setoid_rewrite H in H'

  | [ H: forall (k : StringMap.key) (v : _), StringMap.MapsTo k (ADT v) ?y <-> StringMap.MapsTo k (ADT v) ?y'
      |- context[StringMap.MapsTo _ (ADT _) ?y] ] => rewrite H
  | [ H: forall (k : StringMap.key) (v : _), StringMap.MapsTo k (ADT v) ?y <-> StringMap.MapsTo k (ADT v) ?y',
      H': context[StringMap.MapsTo _ (ADT _) ?y] |- _ ] => rewrite H in H'
  end.

Ltac t_Morphism_step :=
  match goal with
  | _ => cleanup

  | [ |- context[?m ≲ Nil ∪ ?ext] ] => simpl
  | [ H: context[?m ≲ Nil ∪ ?ext] |- _ ] => simpl in H

  | [ |- context[?m ≲ Cons ?k ?v ?t ∪ ?ext] ] => let h := fresh in destruct k eqn:h; simpl
  | [ H: context[?m ≲ Cons ?k ?v ?t ∪ ?ext] |- _ ] => let h := fresh in destruct k eqn:h; simpl in H

  | [ |- context[match StringMap.find ?k ?m with _ => _ end] ] => let h := fresh in destruct (StringMap.find k m) eqn:h; simpl
  | [ H: context[match StringMap.find ?k ?m with _ => _ end] |- _ ] => let h := fresh in destruct (StringMap.find k m) eqn:h; simpl in H

  | [ H: wrap _ = wrap _ |- _ ] => apply wrap_inj in H
  | |- exists _, _ => eexists
  | _ => rewrite_equalities
  end.

Ltac t_Morphism := repeat t_Morphism_step.

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

Add Parametric Relation {A} : _ (@WeakEq A)
    reflexivity proved by (@WeakEq_Refl A)
    transitivity proved by (@WeakEq_Trans A)
      as WeakEq_Rel.

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

Ltac step :=
  match goal with
  | _ => progress simpl in *
  | _ => cleanup
  | [ H: StringMap.MapsTo ?k ?v ?m |- Some ?v = StringMap.find ?k ?m ] => symmetry; rewrite <- find_mapsto_iff; assumption
  | [ H: StringMap.MapsTo ?k ?v ?m |- context[StringMap.find ?k ?m] ] => replace (StringMap.find k m) with (Some v) in *
  | [ H: context[match StringMap.find ?k ?m with | Some _ => _ | None => _ end] |- _ ] => let eq0 := fresh in progress (destruct (StringMap.find k m) eqn:eq0; deduplicate)
  | [ H: ret _ ↝ _ |- _ ] => inversion H; clear H; subst
  | _ => solve [intuition eauto 8]
  end.

Ltac t__ :=
  repeat step.

Lemma SameValues_MapsTo_ret:
  forall `{H: FacadeWrapper (Value av) A}
    (key : String.string) (value : Comp A)
    (tail : A -> Telescope av)
    (ext state : StringMap.t (Value av)) (x : A),
    StringMap.MapsTo key (wrap x) state ->
    state ≲ Cons (NTSome key) value tail ∪ ext ->
    state ≲ Cons (NTSome key) (ret x) tail ∪ ext.
Proof. t__. Qed.

Lemma SameValues_MapsTo_ret_inv:
  forall `{H: FacadeWrapper (Value av) A}
    (key : String.string) (value : Comp A)
    (tail : A -> Telescope av)
    (ext state : StringMap.t (Value av)) (x : A),
    value ↝ x ->
    state ≲ Cons (NTSome key) (ret x) tail ∪ ext ->
    state ≲ Cons (NTSome key) value tail ∪ ext.
Proof. t__. Qed.

Lemma SameValues_MapsTo_ret_ex:
  forall `{H: FacadeWrapper (Value av) A}
    (key : String.string) (value : Comp A)
    (tail : A -> Telescope av)
    (ext state : StringMap.t (Value av)),
    state ≲ Cons (NTSome key) value tail ∪ ext ->
    exists v, value ↝ v /\ state ≲ Cons (NTSome key) (ret v) tail ∪ ext.
Proof. t__. Qed.

Lemma SameValues_Equal :
  forall {av} tenv m1 m2 ext,
    @StringMap.Equal (Value av) m1 m2 ->
    (m1 ≲ tenv ∪ ext ->
     m2 ≲ tenv ∪ ext).
Proof.
  induction tenv;
  repeat match goal with
         | [ IH: _, H: StringMap.remove ?k ?m1 ≲ (?t ?v) ∪ ?ext, H': StringMap.Equal ?m1 ?m2 |-
             StringMap.remove ?k ?m2 ≲ (?t ?v) ∪ ?ext ] => apply (IH _ _ _ _ (remove_m eq_refl H')); exact H
         | _ => solve [eauto]
         | _ => t_Morphism_step
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

Add Parametric Morphism {av} : (@SameValues av)
    with signature (StringMap.Equal ==> StringMap.Equal ==> eq ==> iff)
      as SameValues_Morphism.
Proof.
  split; intros; subst;
  eapply SameValues_Equal; eauto using Equal_sym;
  eapply SameValues_Equal_Ext; eauto using Equal_sym.
Qed.

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
    SameADTs m2 m1 -> SameADTs ([s0 |> v]::m2) ([s0 |> v]::m1).
Proof.
  unfold SameADTs; t_Same.
Qed.

Lemma SameSCAs_add:
  forall (av : Type) (m1 m2 : StringMap.t (Value av))
    (s0 : StringMap.key) (v : Value av),
    SameSCAs m2 m1 -> SameSCAs ([s0 |> v]::m2) ([s0 |> v]::m1).
Proof.
  unfold SameSCAs; t_Same.
Qed.

Lemma WeakEq_add:
  forall (av : Type) (m1 m2 : StringMap.t (Value av))
    (s0 : StringMap.key) (v : Value av),
    WeakEq m2 m1 -> WeakEq ([s0 |> v]::m2) ([s0 |> v]::m1).
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

Ltac StringMap_t :=
  match goal with
  | _ => progress MoreStringMapFacts.normalize
  | [ H: StringMap.MapsTo ?k (ADT ?v) ?st, H': SameADTs ?st _ |- _ ] => learn (SameADTs_impl H' H)
  | [ H: StringMap.MapsTo ?k (ADT ?v) ?st, H': SameADTs _ ?st |- _ ] => learn (SameADTs_impl' H' H)
  | [ H: StringMap.MapsTo ?k ?v ?m, H': WeakEq ?m ?m' |- _ ] => learn (WeakEq_Mapsto_MapsTo H H')
  end.

Lemma SameValues_Pop_Both:
  forall `{FacadeWrapper (Value av) A}
    k ext tenv (st : State av) cmp (v: A),
    cmp ↝ v ->
    StringMap.remove k st ≲ tenv ∪ ext ->
    [k |> wrap v] :: st ≲ [[ `k ~~> cmp as _ ]] :: tenv ∪ ext.
Proof.
  intros; simpl; repeat (StringMap_t || cleanup || eexists); eauto.
Qed.

Hint Resolve @SameValues_Pop_Both : SameValues_db.

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

(* To sort *)

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
             H'': StringMap.MapsTo ?key ?v' _  |- _ ] => specialize (H v key ext st H' v' H''); rename H into IHREC
         | [ H: StringMap.MapsTo ?k ?v (StringMap.remove _ ?s) |- StringMap.MapsTo ?k ?v ?s ] => solve[eauto using MapsTo_remove]
         | [ H: match StringMap.find ?s ?st with _ => _ end |- _ ] => let a := fresh in destruct (StringMap.find s st) eqn:a
         | [ H: exists v, _ |- _ ] => destruct H
         end; eauto using WeakEq_Mapsto_MapsTo. (* NOTE adding the eauto at the end of the match makes things slower *)
Qed.

Lemma SameValues_MapsTo_Ext_State_add:
  forall `{FacadeWrapper (Value av) A} {tel: Telescope av} (key : StringMap.key)
    {v: A} {ext st : StringMap.t (Value av)},
    st ≲ tel ∪ [key |> wrap v]::ext ->
    StringMap.MapsTo key (wrap v) st.
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
  forall `{FacadeWrapper (Value av) A} {tel: Telescope av} (key : StringMap.key) (v: A)
    {ext st : StringMap.t (Value av)},
    st ≲ tel ∪ [key |> wrap v]::ext ->
    StringMap.In key st.
Proof.
  intros; eapply MapsTo_In; eauto using SameValues_MapsTo_Ext_State_add.
Qed.

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

Lemma ProkOk_specialize_to_ret :
  forall `{FacadeWrapper (Value av) A}
    env key value prog
    (tail1: A -> Telescope av)
    (tail2: A -> Telescope av)
    ext,
    (forall v, value ↝ v -> {{ Cons (NTSome key) (ret v) tail1 }} prog {{ Cons (NTSome key) (ret v) tail2 }} ∪ {{ ext }} // env) ->
    ({{ Cons (NTSome key) value tail1 }} prog {{ Cons (NTSome key) value tail2 }} ∪ {{ ext }} // env).
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

Lemma SameValues_MapsTo:
  forall `{FacadeWrapper (Value av) A}
    (key : String.string) (value : Comp A)
    (tail : A -> Telescope av)
    (ext state : StringMap.t (Value av)),
    state ≲ Cons (NTSome key) value tail ∪ ext ->
    exists v : A, value ↝ v /\ StringMap.MapsTo key (wrap v) state.
Proof.
  simpl; intros.
  destruct (StringMap.find _ _) eqn: eq0; try tauto.
  rewrite <- find_mapsto_iff in *.
  repeat cleanup.
  eexists; intuition eauto.
Qed.

Require Import Program.Basics.

Add Parametric Morphism av : (@ProgOk av)
    with signature (StringMap.Equal ==> GLabelMap.Equal ==> eq ==> eq ==> eq ==> impl)
      as Proper_ProgOk.
Proof.
  intros ? ? seq ? ? leq ** ok ? sv; split; intros;
    rewrite <- seq, <- leq in *;
    specialize (ok _ sv);
    intuition.
Qed.
