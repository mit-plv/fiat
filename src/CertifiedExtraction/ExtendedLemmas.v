Require Import
        Coq.Classes.Morphisms.
Require Export
        CertifiedExtraction.CoreLemmas
        CertifiedExtraction.PropertiesOfTelescopes.

Ltac SameValues_Fiat_t_step :=
  match goal with
  | _ => cleanup

  | [  |- _ ≲ Cons _ _ _ ∪ _ ] => simpl
  | [ H: _ ≲ Cons _ _ _ ∪ _ |- _ ] => simpl in H

  | [ H: match ?k with _ => _ end |- _ ] => let eqn := fresh in destruct k eqn:eqn
  | [  |- context[match SCA _ _ with _ => _ end] ] => simpl

  | [ H: ?a = ?b |- context[?a] ] => rewrite H
  | [ H: ?a = ?b, H': context[?a] |- _ ] => may_touch H; rewrite H in H'
  | [ H: forall a, TelEq _ (?x a) (?y a) |- _ ≲ (?x _) ∪ _ ] => red in H; rewrite H
  | [ H: forall a, TelEq _ (?x a) (?y a), H': _ ≲ (?x _) ∪ _ |- _ ] => red in H; rewrite H in H'
  | [ H: forall a, ?v ↝ a -> TelEq _ (?x a) (?y a), H'': ?v ↝ _ |- _ ≲ (?x _) ∪ _ ] => unfold TelEq in H; rewrite (H _ H'')
  | [ H: forall a, ?v ↝ a -> TelEq _ (?x a) (?y a), H'': ?v ↝ _, H': _ ≲ (?x _) ∪ _ |- _ ] => unfold TelEq in H; rewrite (H _ H'') in H'
  | [ H: Monad.equiv ?b ?a |- ?b ↝ ?A ] => red in H; rewrite H
  | [ H: Monad.equiv ?a ?b, H': ?a ↝ ?A |- _ ] => red in H; rewrite H in H'

  | [  |- exists _, _ ] => eexists
  | _ => eauto with SameValues_Fiat_db
  end.

Ltac SameValues_Fiat_t :=
  repeat SameValues_Fiat_t_step.

Add Parametric Morphism {av T} ext : (@Cons av T)
    with signature (eq ==> Monad.equiv ==> pointwise_relation _ (TelEq ext) ==> (TelEq ext))
      as Cons_MonadEquiv_morphism.
Proof.
  unfold pointwise_relation; intros; unfold TelEq;
  SameValues_Fiat_t.
Qed.

Add Parametric Morphism {av T} ext : (fun key comp tail => (@Cons av T key comp (fun _ => tail): Telescope av))
    with signature (eq ==> Monad.equiv ==> TelEq ext ==> (TelEq ext))
      as Cons_MonadEquiv_morphism_simple.
Proof.
  intros; apply Cons_MonadEquiv_morphism; try red; eauto.
Qed.

Add Parametric Morphism {av T} ext k (cmp: Comp T) : (@Cons av T k cmp)
    with signature ((PointWise_TelEq ext cmp) ==> (TelEq ext))
      as Cons_TelEq_pointwise_morphism.
Proof.
  unfold PointWise_TelEq; intros; unfold TelEq;
  SameValues_Fiat_t.
Qed.

Lemma Cons_PopAnonymous:
  forall {av A} (val: Comp A) tail (ext : StringMap.t (Value av)) (state : StringMap.t (Value av)),
    state ≲ [[val as _]]::tail ∪ ext ->
    state ≲ tail ∪ ext.
Proof.
  SameValues_Fiat_t.
Qed.

Lemma Cons_PushAnonymous:
  forall {av A} (val: Comp A) tail (ext : StringMap.t (Value av)) (state : StringMap.t (Value av)),
    (exists v, val ↝ v) ->
    state ≲ tail ∪ ext ->
    state ≲ [[val as _]]::tail ∪ ext.
Proof.
  SameValues_Fiat_t.
Qed.

Hint Resolve @Cons_PopAnonymous : SameValues_db.
Hint Resolve @Cons_PushAnonymous : SameValues_db.

Lemma SameValues_Fiat_Bind_TelEq :
  forall {av A B} (key: NameTag av B) compA compB tail ext,
    TelEq ext
          (Cons key (@Bind A B compA compB) tail)
          (Cons NTNone compA (fun a => Cons key (compB a) tail)).
Proof.
  unfold TelEq; SameValues_Fiat_t.
Qed.

Ltac push_pop_step IH :=
  match goal with
  | _ => eassumption
  | _ => apply IH
  | [ H: ?a /\ ?b |- _ ] => destruct H
  | [  |- ?a /\ ?b ] => split
  | [ H: context[StringMap.find ?k (StringMap.remove ?k' ?st)] |- context[StringMap.find ?k ?st] ] =>
    let _eq := fresh in destruct (StringMap.find k (StringMap.remove k' st)) eqn:_eq; [ | tauto]
  | [ H: (StringMap.find ?k (StringMap.remove ?k' ?st)) = Some _ |- _ ] =>
    rewrite <- find_mapsto_iff in H; rewrite remove_mapsto_iff in H
  | [ H: context[match StringMap.find ?k ?st with _ => _ end] |- context[StringMap.find ?k (StringMap.remove ?k' ?st)] ] =>
    let _eq := fresh in destruct (StringMap.find k st) eqn:_eq; [| tauto]
  | [ H: StringMap.MapsTo ?k ?v ?m |- context[StringMap.find ?k ?m] ] => rewrite find_mapsto_iff in H; rewrite H
  | [ H: StringMap.MapsTo ?k ?v ?s, H': ?k <> ?k' |- StringMap.MapsTo ?k ?v (StringMap.remove ?k' ?s)] =>
    rewrite remove_neq_mapsto_iff by congruence
  | [ H: StringMap.remove ?k (StringMap.remove ?k' ?s) ≲ _ ∪ _ |- StringMap.remove ?k' (StringMap.remove ?k ?s) ≲ _ ∪ _ ] =>
    rewrite remove_remove_comm
  | _ => rewrite SameValues_Equal_iff; eauto using remove_remove_comm
  | [ H: StringMap.find ?k ?m = _ |- match StringMap.find ?k ?m with _ => _ end ] => rewrite H
  | [ H: StringMap.remove _ _ ≲ _ ∪ [_ |> wrap _]::_ |- _ ] => learn (SameValues_In_Ext_State_add _ _ H)
  | [ H: _ ∈ (StringMap.remove _ _) |- _ ] => learn (In_remove_neq H)
  | [ H: ?k <> ?k' |- context[StringMap.find ?k' (StringMap.remove ?k _)] ] => rewrite remove_neq_o by eassumption
  | _ => cleanup
  | [ |- exists v, _ ] => eexists
  | _ => eauto using remove_remove_comm
  end.

Ltac push_pop IH :=
  repeat push_pop_step IH.

Lemma SameValues_PushExt:
  forall `{FacadeWrapper (Value av) A} (key : StringMap.key)
    (tail : A -> Telescope av) (v0 : A)
    (ext initial_state : StringMap.t (Value av)),
    StringMap.MapsTo key (wrap v0) initial_state ->
    StringMap.remove key initial_state ≲ tail v0 ∪ ext ->
    initial_state ≲ tail v0 ∪ [key |> wrap v0]::ext.
Proof.
  intros until v0.
  induction (tail v0) as [ | ? k ? ? IH ]; intros.

  - simpl in *;
    lazymatch goal with
    | [ H: StringMap.MapsTo _ _ _ |- _ ] => rewrite (MapsTo_add_remove H)
    end; eauto using WeakEq_add.
  - simpl in *. destruct k; push_pop IH.
Qed.

Lemma Cons_PushExt:
  forall `{FacadeWrapper (Value av) A} (key : StringMap.key) (tail : A -> Telescope av)
    (ext : StringMap.t (Value av)) (v : A)
    (initial_state : StringMap.t (Value av)),
    initial_state ≲ Cons (NTSome key) (ret v) tail ∪ ext ->
    initial_state ≲ tail v ∪ [key |> wrap v]::ext.
Proof.
  t__; apply SameValues_PushExt; try rewrite find_mapsto_iff; cleanup; eauto.
Qed.

Lemma Cons_PushExt':
  forall `{FacadeWrapper (Value av) A} key tenv ext (v: A) (st: State av),
    st ≲ Cons (NTSome key) (ret v) (fun _ => tenv) ∪ ext ->
    st ≲ tenv ∪ [key |> wrap v] :: ext.
Proof.
  intros; change tenv with ((fun _ => tenv) v); eauto using Cons_PushExt.
Qed.

Hint Resolve @Cons_PushExt' : SameValues_db.

Lemma SameValues_PopExt:
  forall `{FacadeWrapper (Value av) A} (key : StringMap.key)
    (tail : A -> Telescope av) (v0 : A)
    (ext initial_state : StringMap.t (Value av)),
    (* StringMap.MapsTo key v0 initial_state -> *)
    key ∉ ext ->
    initial_state ≲ tail v0 ∪ [key |> wrap v0]::ext ->
    StringMap.remove key initial_state ≲ tail v0 ∪ ext.
Proof.
  intros until v0.
  induction (tail v0) as [ | ? k ? ? IH ]; intros.

  - simpl in *;
    lazymatch goal with
    | [ H: ?k ∉ ?ext |- _ ] => rewrite <- (fun x => remove_add_cancel x H eq_refl)
    end; eauto using WeakEq_remove.
  - simpl in *. destruct k; push_pop IH.
Qed.

Lemma SameValues_PopExt':
  forall `{FacadeWrapper (Value av) A} (key : StringMap.key) (tail : Telescope av)
    (v0 : A) (ext initial_state : StringMap.t (Value av)),
    key ∉ ext ->
    initial_state ≲ tail ∪ [key |> wrap v0]::ext ->
    StringMap.remove key initial_state ≲ tail ∪ ext.
Proof.
  intros.
  change tail with ((fun (_: A) => tail) v0).
  eauto using SameValues_PopExt.
Qed.

Hint Resolve @SameValues_PopExt' : SameValues_db.

Lemma Cons_PopExt:
  forall `{FacadeWrapper (Value av) A} (key : StringMap.key) (tail : A -> Telescope av)
    (ext : StringMap.t (Value av)) (v : A)
    (initial_state : StringMap.t (Value av)),
    key ∉ ext ->
    initial_state ≲ tail v ∪ [key |> wrap v]::ext ->
    initial_state ≲ Cons (NTSome key) (ret v) tail ∪ ext.
Proof.
  t__.
  repeat match goal with
         | [ H: ?st ≲ ?tel ∪ [?k |> wrap ?v]::ext |- _ ] =>
           let h := fresh in pose proof H as h; apply SameValues_MapsTo_Ext_State_add in h; no_duplicates
         | [ H: StringMap.MapsTo ?k ?v ?m |- match StringMap.find ?k ?m with _ => _ end] =>
           rewrite find_mapsto_iff in H; rewrite H
         | _ => cleanup
         end;
  eauto using SameValues_PopExt.
Qed.
Open Scope telescope_scope.

Lemma SameValues_Add_Cons:
  forall `{FacadeWrapper (Value av) A} (key : StringMap.key) (value: A) (ext state : StringMap.t (Value av)),
    key ∉ ext -> WeakEq ext state -> [key |> (wrap value)]::state ≲ ([[ `key ->> value as _ ]] :: Nil) ∪ ext.
Proof.
  intros; apply Cons_PopExt; simpl; eauto using WeakEq_Refl, WeakEq_add.
Qed.

Hint Resolve @SameValues_Add_Cons : SameValues_db.
Hint Resolve @WeakEq_add : SameValues_db.

Require Export CertifiedExtraction.PropertiesOfTelescopes CertifiedExtraction.FacadeLemmas.

Ltac facade_cleanup :=
  progress match goal with
  | [  |- eval _ _ = Some _ ] => first [ reflexivity | progress simpl ]
  | [ H: eval _ _ = Some _ |- _ ] => simpl in H
  | [ H: eval_binop_m _ _ _ = Some _ |- _ ] => simpl in H
  | [ H: context[match Some _ with _ => _ end] |- _ ] => may_touch H; simpl in H
  | [ H: ?k <> ?k' |- context[not_mapsto_adt ?k (StringMap.add ?k' _ _)] ] => rewrite not_mapsto_adt_add by congruence
  | [ H: ?k' <> ?k |- context[not_mapsto_adt ?k (StringMap.add ?k' _ _)] ] => rewrite not_mapsto_adt_add by congruence
  | [ H: ?k ∉ ?m |- context[not_mapsto_adt ?k ?m] ] => rewrite NotIn_not_mapsto_adt by assumption
  end.

Lemma SameValues_Cons_unfold_Some :
  forall `{FacadeWrapper (Value av) A} k (st: State av) val ext tail,
    st ≲ (Cons (NTSome k) val tail) ∪ ext ->
    exists v: A, StringMap.MapsTo k (wrap v) st /\ val ↝ v /\ StringMap.remove k st ≲ tail v ∪ ext.
Proof.
  simpl; intros;
  repeat match goal with
         | _ => exfalso; assumption
         | [ H: match ?x with Some _ => _ | None => False end |- _ ] => let _eq := fresh in destruct x eqn:_eq
         | _ => cleanup
         | _ => intuition eauto using StringMap.find_2
         end.
Qed.

Lemma SameValues_Cons_unfold_None :
  forall {av A} (st: State av) (val: Comp A) ext tail,
    st ≲ (Cons NTNone val tail) ∪ ext ->
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

  | [ |- @ProgOk _ _ _ _ _ _ ] => red

  | _ => StringMap_t
  | _ => progress subst

  | [ H: TelEq _ ?x _ |- context[?st ≲ ?x ∪ _] ] => rewrite (H st)
  | [ H: TelEq _ ?x _, H': context[?st ≲ ?x ∪ _] |- _ ] => may_touch H'; rewrite_in (H st) H'

  (* Specialize ProgOk *)
  | [ H: ProgOk ?ext _ _ ?tel _, H': ?st ≲ ?tel ∪ ?ext |- _ ] => learn (H st H')
  | [ H: forall st : State _, RunsTo ?env ?p ?ext st -> _, H': RunsTo ?env ?p ?ext ?st |- _ ] => learn (H st H')
  (* Cleanup Cons *)
  | [ H: ?st ≲ Cons (NTSome _) _ _ ∪ _ |- _ ] => learn (Cons_PushExt _ _ _ _ _ H)
  | [ H: ?st ≲ Cons NTNone _ _ ∪ _ |- _ ] => learn (Cons_PopAnonymous H)
  | [ H: ?st ≲ (fun _ => _) _ ∪ _ |- _ ] => progress cbv beta in H
  | [ H: ?st ≲ (Cons (NTSome ?k) ?val ?tail) ∪ ?ext |- _ ] => learn (SameValues_Cons_unfold_Some k st val ext tail H)
  | [ H: ?st ≲ (Cons NTNone ?val ?tail) ∪ ?ext |- _ ] => learn (SameValues_Cons_unfold_None H)
  | [ H: StringMap.MapsTo ?k ?v ?ext, H': ?st ≲ ?tenv ∪ ?ext |- _ ] => learn (SameValues_MapsTo_Ext_State H' H)
  (* Cleanup NotInTelescope *)
  | [ H: NotInTelescope ?k (Cons NTNone _ _) |- _ ] => simpl in H
  | [ H: NotInTelescope ?k (Cons (NTSome ?k') ?v ?tail) |- _ ] => learn (NotInTelescope_not_eq_head _ H)
  | [ H: NotInTelescope ?k (Cons (NTSome ?k') ?v ?tail), H': ?v ↝ _ |- _ ] => learn (NotInTelescope_not_in_tail _ _ H' H)
  (* Learn MapsTo instances from WeakEqs *)
  | [ H: ?st ≲ Nil ∪ ?ext |- _ ] => learn (SameValues_Nil H)
  | [ H: WeakEq _ ?st |- not_mapsto_adt _ ?st = _ ] => rewrite <- H
  | [ H: WeakEq ?st1 ?st2 |- _ ] => learn_from_WeakEq H st1 st2

  (* Cleanup not_mapsto_adt *)
  | [ H: ?k <> ?s |- not_mapsto_adt ?k (StringMap.add ?s _ _) = true ] => apply not_mapsto_adt_neq_remove'; [ congruence | ]
  | [ H: ?s <> ?k |- not_mapsto_adt ?k (StringMap.add ?s _ _) = true ] => apply not_mapsto_adt_neq_remove'; [ congruence | ]

  (* Cleanup typeclass uses *)
  | [  |- context[SCA ?av ?w]     ] => change (SCA av w) with (wrap (FacadeWrapper := FacadeWrapper_SCA (av := av)) w)
  | [ H: context[SCA ?av ?w] |- _ ] => may_touch H; change (SCA av w) with (wrap (FacadeWrapper := FacadeWrapper_SCA (av := av)) w) in H

  | [ H: ?a -> _, H': ?a |- _ ] => match type of a with Prop => specialize (H H') end

  | _ => facade_construction
  end.

Ltac SameValues_Facade_t :=
  repeat SameValues_Facade_t_step;
  try solve [eauto 4 with SameValues_db].

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
  forall `{FacadeWrapper (Value av) A} env key prog
    (tail1 tail2: A -> Telescope av)
    ext (v: A),
    key ∉ ext ->
    ({{ tail1 v }} prog {{ tail2 v }} ∪ {{ [key |> wrap v] :: ext }} // env <->
     {{ Cons (NTSome key) (ret v) tail1 }} prog {{ Cons (NTSome key) (ret v) tail2 }} ∪ {{ ext }} // env).
Proof.
  repeat match goal with
         | _ => progress intros
         | _ => progress split
         | _ => tauto
         | [ H: ?a /\ ?b |- _ ] => destruct H
         | [ H: ?a ≲ Cons _ _ _ ∪ _ |- _ ] => learn (Cons_PushExt _ _ _ _ _ H)
         | [ H: ProgOk ?fmap _ _ ?t1 ?t2, H': _ ≲ ?t1 ∪ ?fmap |- _ ] => destruct (H _ H'); no_duplicates
         | [ H: RunsTo _ _ ?from ?to, H': forall st, RunsTo _ _ ?from st -> _ |- _ ] => specialize (H' _ H)
         | [ H: _ ≲ _ ∪ [_ |> _] :: _ |- _ ] => apply Cons_PopExt in H
         | _ => solve [eauto using Cons_PopExt]
         end.
Qed.

Lemma ProgOk_Chomp_Some :
  forall `{FacadeWrapper (Value av) A} env key value prog
    (tail1: A -> Telescope av)
    (tail2: A -> Telescope av)
    ext,
    key ∉ ext ->
    (forall v: A, value ↝ v -> {{ tail1 v }} prog {{ tail2 v }} ∪ {{ [key |> wrap v] :: ext }} // env) ->
    ({{ Cons (NTSome key) value tail1 }} prog {{ Cons (NTSome key) value tail2 }} ∪ {{ ext }} // env).
Proof.
  intros; apply ProkOk_specialize_to_ret; intros; apply ProgOk_Chomp_lemma; eauto.
Qed.

Lemma ProgOk_Chomp_None :
  forall {av A} env value prog
    (tail1: A -> Telescope av)
    (tail2: A -> Telescope av) ext,
    (forall v, value ↝ v -> {{ tail1 v }} prog {{ tail2 v }} ∪ {{ ext }} // env) ->
    ({{ Cons NTNone value tail1 }} prog {{ Cons NTNone value tail2 }} ∪ {{ ext }} // env).
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
    SameADTs st ([k |> wrap v]::st).
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
    SameADTs ext ([k |> wrap v]::st).
Proof.
  eauto using SameADTs_Trans, SameADTs_pop_SCA_util.
Qed.

Lemma SameSCAs_pop_SCA_util:
  forall (av : Type) (st : StringMap.t (Value av))
    (k : StringMap.key) (v : W),
    k ∉ st ->
    SameSCAs st ([k |> wrap v]::st).
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
    SameSCAs ext ([k |> wrap v]::st).
Proof.
  eauto using SameSCAs_Trans, SameSCAs_pop_SCA_util.
Qed.

Lemma WeakEq_pop_SCA:
  forall (av : Type) (st : StringMap.t (Value av))
    (k : StringMap.key) (ext : StringMap.t (Value av))
    (v : W),
    k ∉ st ->
    WeakEq ext st ->
    WeakEq ext ([k |> wrap v]::st).
Proof.
  unfold WeakEq;
  intuition eauto using SameSCAs_pop_SCA, SameADTs_pop_SCA, NotIn_not_mapsto_adt.
Qed.

Lemma SameADTs_pop_SCA':
  forall (av : Type) (st : StringMap.t (Value av))
    (k : StringMap.key) (v : W) ext,
    k ∉ ext ->
    SameADTs ext st ->
    SameADTs ext ([k |> wrap v]::st).
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
    SameSCAs ext ([k |> wrap v]::st).
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
    WeakEq ext ([k |> wrap v]::st).
Proof.
  unfold WeakEq;
  intuition eauto using SameSCAs_pop_SCA', SameADTs_pop_SCA'.
Qed.

Hint Resolve @WeakEq_pop_SCA' : call_helpers_db.

Lemma SameSCAs_pop_SCA_left :
  forall {av} k (v: W) (m1 m2: StringMap.t (Value av)),
    k ∉ m1 ->
    SameSCAs (StringMap.add k (wrap v) m1) m2 ->
    SameSCAs m1 m2.
Proof.
  unfold SameSCAs; intros; eauto using MapsTo_NotIn_inv, StringMap.add_2.
Qed.

Lemma SameADTs_pop_SCA_left :
  forall {av} k (v: W) (m1 m2: StringMap.t (Value av)),
    k ∉ m1 ->
    SameADTs (StringMap.add k (wrap v) m1) m2 ->
    SameADTs m1 m2.
Proof.
  unfold SameADTs; split; intros; rewrite <- H0 in *.
  - eauto using MapsTo_NotIn_inv, StringMap.add_2.
  - destruct (StringMap.E.eq_dec k k0); subst;
    StringMap_t; (congruence || discriminate).
Qed.

Lemma WeakEq_pop_SCA_left :
  forall {av} k (v: W) (m1 m2: StringMap.t (Value av)),
    k ∉ m1 ->
    WeakEq (StringMap.add k (wrap v) m1) m2 ->
    WeakEq m1 m2.
Proof.
  unfold WeakEq; intuition eauto using SameADTs_pop_SCA_left, SameSCAs_pop_SCA_left.
Qed.

Hint Resolve @SameADTs_pop_SCA : SameValues_db.
Hint Resolve @SameSCAs_pop_SCA : SameValues_db.
Hint Resolve @WeakEq_pop_SCA : SameValues_db.

Lemma not_mapsto_adt_neq_remove:
  forall (av : Type) (s : string) (k : StringMap.key)
    (st : StringMap.t (Value av)),
    k <> s ->
    not_mapsto_adt k (StringMap.remove (elt:=Value av) s st) = true ->
    not_mapsto_adt k st = true.
Proof.
  not_mapsto_adt_t; SameValues_Facade_t.
Qed.

Hint Resolve @not_mapsto_adt_neq_remove : SameValues_db.

Lemma not_mapsto_adt_eq_SCA:
  forall (av : Type) (k : StringMap.key) (w : W) (fmap : StringMap.t (Value av)),
    not_mapsto_adt k (StringMap.add k (SCA av w) fmap) = true.
Proof.
  eauto using MapsTo_SCA_not_mapsto_adt, StringMap.add_1.
Qed.

Hint Resolve @not_mapsto_adt_eq_SCA : SameValues_db.

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

Lemma WeakEq_remove_notIn:
  forall av (k : StringMap.key) (st1 st2 : State av),
    k ∉ st1 ->
    WeakEq st1 st2 ->
    WeakEq st1 (StringMap.remove k st2).
Proof.
  intros. rewrite <- (remove_notIn_Equal (k := k)  (m := st1)) by assumption.
  eauto using WeakEq_remove.
Qed.

Hint Resolve @WeakEq_remove_notIn : SameValues_db.

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
  eexists; rewrite remove_remove_comm by congruence; SameValues_Facade_t.
Qed.

Lemma SameValues_forget_Ext_helper:
  forall `{FacadeWrapper (Value av) A} (k : string) (cmp : Comp A) val
    (tmp : StringMap.key) (ext : StringMap.t (Value av))
    (final_state : State av),
    tmp ∉ ext ->
    final_state ≲ [[ ` k ~~> cmp as _]]::Nil ∪ [tmp |> SCA _ val]::ext ->
    final_state ≲ [[ ` k ~~> cmp as _]]::Nil ∪ ext.
Proof.
  simpl; intros. SameValues_Fiat_t.
  eauto using WeakEq_pop_SCA, WeakEq_Refl, WeakEq_Trans.
Qed.

Hint Resolve @not_In_Telescope_not_in_Ext_not_mapsto_adt : SameValues_db.
Hint Resolve @SameValues_not_In_Telescope_not_in_Ext_remove : SameValues_db.
Hint Resolve @SameValues_forget_Ext_helper : SameValues_db.

Lemma SameValues_add_SCA:
  forall av {A} (Wrp: FacadeWrapper (Value av) A)
    tel (st: StringMap.t (Value av)) k ext (v: A),
    (forall a, is_adt (wrap a) = false) ->
    k ∉ st ->
    st ≲ tel ∪ ext ->
    (StringMap.add k (wrap v) st) ≲ tel ∪ ext.
Proof.
  induction tel;
  repeat (t_Morphism || SameValues_Facade_t).
  pose proof (H v); destruct (wrap v); try (simpl in *; congruence); SameValues_Facade_t.
  apply H; repeat (t_Morphism || SameValues_Facade_t).
Qed.

Lemma SameValues_add_W:
  forall av tel (st: StringMap.t (Value av)) k ext (v: W),
    k ∉ st ->
    st ≲ tel ∪ ext ->
    (StringMap.add k (wrap v) st) ≲ tel ∪ ext.
Proof.
  intros; eauto using SameValues_add_SCA.
Qed.

Lemma SameValues_Nil_inv :
  forall (A : Type) (state ext : StringMap.t (Value A)),
    WeakEq ext state -> state ≲ Nil ∪ ext.
Proof.
  intros; assumption.
Qed.

Hint Resolve @SameValues_Nil_inv : SameValues_db.
Hint Resolve @WeakEq_pop_SCA_left : SameValues_db.

Lemma SameValues_forget_Ext:
  forall (av : Type) (tenv : Telescope av) (var : StringMap.key) (val2 : W)
    (ext : StringMap.t (Value av)) (st' : State av),
    var ∉ ext ->
    st' ≲ tenv ∪ [var |> wrap val2] :: ext ->
    st' ≲ tenv ∪ ext.
Proof.
  induction tenv; SameValues_Facade_t.
  SameValues_Fiat_t.
Qed.

Hint Resolve @SameValues_forget_Ext : SameValues_db.

Lemma SameValues_Dealloc_SCA :
  forall {av} {A} (Wrp: FacadeWrapper (Value av) A)
    st k (v: Comp A) tail ext,
    (forall a, is_adt (wrap a) = false) ->
    st ≲ Cons (av := av) (NTSome k) v tail ∪ ext ->
    st ≲ Cons NTNone v tail ∪ ext.
Proof.
  SameValues_Fiat_t.
  StringMap_t.
  repeat match goal with
         | [ H: StringMap.MapsTo _ _ ?st |- ?st ≲ _ ∪ _ ] => rewrite (MapsTo_add_remove H)
         | [ H: is_adt ?v = false |- _ ] => destruct v; simpl in H; try congruence
         | [ H: match ?x with _ => _ end = _ |- _ ] => destruct x; try congruence
         end.
  apply SameValues_add_SCA; eauto using StringMap.remove_1.
Qed.

Lemma SameValues_Dealloc_W :
  forall {av} st k (v: Comp W) tail ext,
    st ≲ Cons (av := av) (NTSome k) v tail ∪ ext ->
    st ≲ Cons NTNone v tail ∪ ext.
Proof.
  intros; eauto using SameValues_Dealloc_SCA.
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

Hint Resolve @not_in_WeakEq_not_mapsto_adt : SameValues_db.

(* Ltac empty_remove_t := *)
(*   repeat match goal with *)
(*          | _ => SameValues_Facade_t_step *)
(*          | [ H: StringMap.MapsTo ?k _ (StringMap.empty _) |- _ ] => learn (StringMap.empty_1 H) *)
(*          | [ H: StringMap.MapsTo ?k ?v (StringMap.remove ?k' ?m) |- _ ] => learn (StringMap.remove_3 H) *)
(*          | [ H: forall k v, StringMap.MapsTo _ _ ?m <-> _ |- StringMap.MapsTo _ _ ?m ] => rewrite H *)
(*          end. *)

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

Lemma SameValues_add_W_notIn_ext :
  forall {av} k (v: W) (st: StringMap.t (Value av)) tenv ext,
    k ∉ ext ->
    NotInTelescope k tenv ->
    st ≲ tenv ∪ ext ->
    StringMap.add k (wrap v) st ≲ tenv ∪ ext.
Proof.
  eauto with SameValues_db.
Qed.

Hint Resolve @SameValues_add_W_notIn_ext : SameValues_db.

Lemma WeakEq_add_MapsTo :
  forall {av} k v m1 m2,
    StringMap.MapsTo k v m1 ->
    WeakEq (StringMap.add k v m1) m2 ->
    @WeakEq av m1 m2.
Proof.
  intros; rewrite add_redundant_cancel; eassumption.
Qed.

Hint Resolve @WeakEq_add_MapsTo : call_helpers_db.
Hint Resolve @WeakEq_add : call_helpers_db.

Lemma TelEq_swap:
  forall {av A A' ext} (k: @NameTag av A) (k': @NameTag av A') (v: Comp A) (v': Comp A') (tenv: A -> A' -> Telescope av),
    TelEq ext
          ([[k ~~> v as vv]] :: [[k' ~~> v' as vv']] :: tenv vv vv')
          ([[k' ~~> v' as vv']] :: [[k ~~> v as vv]] :: tenv vv vv').
Proof.
  destruct k, k';
  unfold TelEq;
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => progress SameValues_Fiat_t_step
         | [ H: StringMap.MapsTo _ _ (StringMap.remove _ _) |- _ ] => learn (remove_mapsto H)
         | _ => rewrite remove_remove_comm; congruence
         end.
Qed.

Lemma SameValues_Push_ret:
  forall `{H : FacadeWrapper (Value av) A} (k : string)
    (tenv : A -> Telescope av) (ext : StringMap.t (Value av))
    (initial_state : State av) (a : A),
    StringMap.MapsTo k (wrap a) initial_state ->
    StringMap.remove k initial_state ≲ tenv a ∪ ext ->
    initial_state ≲ [[`k ->> a as vv0]]::tenv vv0 ∪ ext.
Proof.
  SameValues_Fiat_t.
  SameValues_Facade_t.
Qed.

Lemma Propagate_anonymous_ret:
  forall {av A} (tenv' : A -> Telescope av)
    (ext : StringMap.t (Value av)) (vv : A),
    TelEq ext ([[ret vv as vv0]]::tenv' vv0) (tenv' vv).
Proof.
  unfold TelEq; SameValues_Fiat_t.
Qed.

Lemma Propagate_anonymous_ret__fast:
  forall {av A} (v : A) (tenv : Telescope av) tenv' env ext p,
    {{ tenv }} p {{ tenv' v }} ∪ {{ ext }} // env ->
    {{ tenv }} p {{ Cons NTNone (ret v) tenv' }} ∪ {{ ext }} // env.
Proof.
  intros; rewrite Propagate_anonymous_ret; assumption.
Qed.

Ltac miniChomp_t_step :=
  match goal with
  | _ => solve [simpl; eauto]
  | _ => SameValues_Facade_t_step
  | [ H: match ?x with _ => _ end = _ |- _ ] => destruct x; try discriminate; [idtac]
  | [ H: _ = ?x |- context[match ?x with _ => _ end] ] => rewrite <- H
  | [ H: forall vv, ?v ↝ vv -> _, H': ?v ↝ _ |- _ ] => learn (H _ H')
  | [ H: StringMap.remove ?k ?st ≲ _ ∪ _, H': StringMap.MapsTo ?k _ ?st |- _ ] => learn (SameValues_Push_ret _ _ _ H' H)
  end.

Ltac miniChomp_t :=
  intros; unfold ProgOk;
  repeat miniChomp_t_step.

Lemma miniChomp_arbitrary_post :
  forall `{FacadeWrapper (Value av) A} k (v: Comp A) tenv tenv' ext prog env,
    (forall vv, v ↝ vv ->
           {{ [[`k ->> vv as vv]] :: (tenv vv) }} prog {{ tenv' v }} ∪ {{ ext }} // env) ->
    {{ [[`k ~~> v as vv]] :: (tenv vv) }} prog {{ tenv' v }} ∪ {{ ext }} // env.
Proof.
  miniChomp_t.
Qed.

Lemma miniChomp:                (* Isn't this more or less [ProkOk_specialize_to_ret]? *)
  forall `{FacadeWrapper (Value av) A} k k' (v: Comp A) tenv tenv' ext prog env,
    (forall vv, v ↝ vv ->
           {{ [[`k ->> vv as vv]] :: (tenv vv) }} prog {{ [[k' ~~> ret vv as vv]] :: tenv' vv }} ∪ {{ ext }} // env) ->
    {{ [[`k ~~> v as vv]] :: (tenv vv) }} prog {{ [[k' ~~> v as vv]] :: tenv' vv }} ∪ {{ ext }} // env.
Proof.
  miniChomp_t.
  destruct k'; simpl; miniChomp_t.
Qed.

Lemma miniChomp' :
  forall `{FacadeWrapper (Value av) A} k (v: Comp A) tenv tenv' ext prog env,
    (forall vv, v ↝ vv ->
           {{ [[`k ->> vv as vv]] :: (tenv vv) }} prog {{ tenv' vv }} ∪ {{ ext }} // env) ->
    {{ [[`k ~~> v as vv]] :: (tenv vv) }} prog {{ [[v as vv]] :: tenv' vv }} ∪ {{ ext }} // env.
Proof.
  intros; apply miniChomp; intros; rewrite Propagate_anonymous_ret by reflexivity; eauto.
Qed.

Lemma SameValues_remove_SCA:
  forall (av : Type) {A} (Wrapper: FacadeWrapper (Value av) A),
    (forall a, is_adt (wrap a) = false) ->
    forall (tenv' : Telescope av)
    (ext : StringMap.t (Value av)) (k : StringMap.key)
    (final_state : State av) (x : A),
    StringMap.MapsTo k (wrap x) final_state ->
    StringMap.remove (elt:=Value av) k final_state ≲ tenv' ∪ ext ->
    final_state ≲ tenv' ∪ ext.
Proof.
  induction tenv'; simpl; intros.
  - rewrite (add_redundant_cancel H0).
    rewrite <- add_remove_cancel; try reflexivity.
    pose proof (H x) as p; destruct (wrap x); simpl in p; try congruence; clear p.
    apply WeakEq_pop_SCA.
    apply StringMap.remove_1; reflexivity.
    assumption.
  - destruct key; repeat cleanup.
    + eauto.
    + SameValues_Fiat_t.
      StringMap_t.
      rewrite remove_mapsto_iff in *.
      cleanup.
      StringMap_t.
      eexists; repeat cleanup; eauto.
      eapply H0.
      rewrite remove_mapsto_iff in *; eauto.
      rewrite remove_remove_comm; eauto.
Qed.

Hint Resolve SameValues_remove_SCA : SameValues_db.

Lemma SameValues_remove_W:
  forall (av0 : Type) (tenv' : Telescope av0)
    (ext : StringMap.t (Value av0)) (k : StringMap.key)
    (final_state : State av0) (x : W),
    StringMap.MapsTo k (wrap x) final_state ->
    StringMap.remove (elt:=Value av0) k final_state ≲ tenv' ∪ ext ->
    final_state ≲ tenv' ∪ ext.
Proof.
  intros; eauto using (SameValues_remove_SCA FacadeWrapper_SCA).
Qed.

Hint Resolve SameValues_remove_W : SameValues_db.

Lemma CompileDeallocSCA_discretely :
  forall {av} {A} (H: FacadeWrapper (Value av) A) (tenv tenv': Telescope av) ext env k (v: Comp A) prog,
    k ∉ ext ->
    NotInTelescope k tenv ->
    (forall a, is_adt (wrap a) = false) ->
    {{ [[`k ~~> v as _]] :: tenv }} prog {{ [[`k ~~> v as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[`k ~~> v as _]] :: tenv }} prog {{ tenv' }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma CompileDeallocW_discretely :
  forall {av} (tenv tenv': Telescope av) ext env k (v: Comp W) prog,
    k ∉ ext ->
    NotInTelescope k tenv ->
    {{ [[`k ~~> v as _]] :: tenv }} prog {{ [[`k ~~> v as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[`k ~~> v as _]] :: tenv }} prog {{ tenv' }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma ProgOk_Chomp_Some_snd :
  forall {av A T} `{FacadeWrapper (Value av) A} `{FacadeWrapper (Value av) T} env key value k (v': Comp T) prog
    (tail1: A -> Telescope av)
    (tail2: A -> Telescope av)
    ext,
    key ∉ ext ->
    (forall v: A, value ↝ v -> {{ tail1 v }} prog {{ Cons (NTSome k) v' (fun _ => tail2 v) }} ∪ {{ [key |> wrap v] :: ext }} // env) ->
    ({{ Cons (NTSome key) value tail1 }} prog {{ Cons (NTSome k) v' (fun _ => Cons (NTSome key) value tail2) }} ∪ {{ ext }} // env).
Proof.
  intros.
  rewrite TelEq_swap.
  apply ProgOk_Chomp_Some; eauto.
Qed.

Lemma ProgOk_Chomp_None_snd :
  forall {av A T} `{FacadeWrapper (Value av) T} env key value prog
    (tail1: A -> Telescope av)
    (tail2: A -> Telescope av)
    ext k (v': Comp T),
    key ∉ ext ->
    (forall v: A, value ↝ v -> {{ tail1 v }} prog {{ Cons (NTSome k) v' (fun _ => tail2 v) }} ∪ {{ ext }} // env) ->
    ({{ Cons NTNone value tail1 }} prog {{ Cons (NTSome k) v' (fun _ => Cons NTNone value tail2) }} ∪ {{ ext }} // env).
Proof.
  intros.
  rewrite TelEq_swap.
  apply ProgOk_Chomp_None; eauto.
Qed.

Lemma SameValues_Fiat_Bind_TelEq_Pair :
  forall {av A1 A2 B} key compA compB tail ext,
    TelEq ext
          (Cons (av := av) key (@Bind (A1 * A2) B compA compB) tail)
          (Cons NTNone compA (fun a => Cons NTNone (ret (fst a)) (fun a1 => Cons NTNone (ret (snd a)) (fun a2 => Cons key (compB (a1, a2)) tail)))).
Proof.
  unfold TelEq;
  repeat match goal with
         | _ => progress subst
         | _ => progress SameValues_Fiat_t_step
         | _ => rewrite <- surjective_pairing in *
         end.
Qed.