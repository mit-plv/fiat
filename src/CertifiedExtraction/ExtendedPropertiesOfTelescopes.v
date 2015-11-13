Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeNotations
        CertifiedExtraction.PropertiesOfTelescopes
        CertifiedExtraction.ExtendedLemmas.

Lemma DropName_remove :
  forall {av} (tenv: Telescope av) k ext st,
    k ∉ ext ->
    st ≲ tenv ∪ ext ->
    StringMap.remove k st ≲ (DropName k tenv) ∪ ext.
Proof.
  induction tenv;
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | [ key: NameTag _ _ |- _ ] => destruct key
         | [  |- context[string_dec ?x ?y] ] => destruct (string_dec x y)
         | _ => progress simpl
         | [  |- exists _, _ ] => eexists
         end;
  try solve [simpl; eauto using M.remove_2 with SameValues_db];
  [ rewrite <- remove_remove_redundant | rewrite remove_remove_comm ];
  eauto using M.remove_2.
Qed.

Hint Resolve DropName_remove : SameValues_db.

Lemma DropName_Cons_Some_neq :
  forall `{FacadeWrapper (Value av) A} k k' v (tail: A -> Telescope av),
    k <> k' ->
    (DropName k (Cons (NTSome k') v tail)) = (Cons (NTSome k') v (fun vv => DropName k (tail vv))).
Proof.
  intros; simpl.
  destruct (string_dec _ _); (congruence || reflexivity).
Qed.

Lemma DropName_Cons_Some_eq :
  forall `{FacadeWrapper (Value av) A} k k' v (tail: A -> Telescope av),
    k = k' ->
    (DropName k (Cons (NTSome k') v tail)) = (Cons NTNone v (fun vv => DropName k (tail vv))).
Proof.
  intros; simpl.
  destruct (string_dec _ _); (congruence || reflexivity).
Qed.

Lemma DropName_Cons_None :
  forall `{FacadeWrapper (Value av) A} k v (tail: A -> Telescope av),
    (DropName k (Cons NTNone v tail)) = (Cons NTNone v (fun vv => DropName k (tail vv))).
Proof.
  intros; simpl; reflexivity.
Qed.

Lemma DropName_NotInTelescope :
  forall {av} (tenv: Telescope av) k,
    NotInTelescope k tenv ->
    TelStrongEq (DropName k tenv) tenv.
Proof.
  induction tenv; intros; simpl.
  - reflexivity.
  - destruct key; simpl in *; cleanup;
    [ | destruct (string_dec _ _); subst; cleanup ];
    constructor; eauto with typeclass_instances.
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
         | _ => progress Lift_morphism_t
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
  forall {av A} k v ext tenv tenv',
    @PointWise_TelEq av A ext v tenv tenv' ->
    TelEq ext (Cons k v tenv) (Cons k v tenv').
Proof.
  intros * H; rewrite H; reflexivity.
Qed.

Lemma TelEq_chomp_None_right :
  forall {av A} v ext tenv tenv',
    (exists vv, v ↝ vv) ->
    @PointWise_TelEq av A ext v (fun _ => tenv) tenv' ->
    TelEq ext tenv (Cons NTNone v tenv').
Proof.
  intros * ? H; rewrite <- H; red.
  split; eauto with SameValues_db.
Qed.

Lemma TelEq_chomp_None_left :
  forall {av A} v ext tenv tenv',
    (exists vv, v ↝ vv) ->
    @PointWise_TelEq av A ext v tenv (fun _ => tenv') ->
    TelEq ext (Cons NTNone v tenv) tenv'.
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

Lemma Lifted_MapsTo_eq:
  forall `{FacadeWrapper (Value av) A} ext k v tail,
    @Lifted_MapsTo av ext (Cons (NTSome k) (ret v) tail) k (wrap v).
Proof.
  unfold Lifted_MapsTo, LiftPropertyToTelescope; intros.
  SameValues_Facade_t.
Qed.

Lemma Lifted_MapsTo_neq:
  forall `{FacadeWrapper (Value av) A} `{FacadeWrapper (Value av) A'} ext k (v: A) tail k' (v': A'),
    k <> k' ->
    @Lifted_MapsTo av ext (tail v) k' (wrap v') ->
    @Lifted_MapsTo av ext (Cons (NTSome k) (ret v) tail) k' (wrap v').
Proof.
  unfold Lifted_MapsTo, LiftPropertyToTelescope; intros.
  SameValues_Facade_t.
  eauto using StringMap.remove_3.
Qed.

Lemma Lifted_not_mapsto_adt_eq:
  forall {av} ext k (v: W) tail,
    @Lifted_not_mapsto_adt av ext (Cons (NTSome k) (ret v) tail) k.
Proof.
  unfold Lifted_not_mapsto_adt, LiftPropertyToTelescope; intros.
  SameValues_Facade_t.
Qed.

Lemma Lifted_not_mapsto_adt_neq:
  forall `{FacadeWrapper (Value av) A} ext k (v: A) tail k',
    k <> k' ->
    @Lifted_not_mapsto_adt av ext (tail v) k' ->
    @Lifted_not_mapsto_adt av ext (Cons (NTSome k) (ret v) tail) k'.
Proof.
  unfold Lifted_not_mapsto_adt, LiftPropertyToTelescope; intros.
  SameValues_Facade_t.
Qed.

Lemma Lifted_not_In_Telescope_not_in_Ext_not_mapsto_adt:
  forall `{FacadeWrapper (Value av) A} ext k tenv,
    k ∉ ext ->
    NotInTelescope k tenv ->
    @Lifted_not_mapsto_adt av ext tenv k.
Proof.
  unfold Lifted_not_mapsto_adt, LiftPropertyToTelescope; intros.
  eauto using not_In_Telescope_not_in_Ext_not_mapsto_adt.
Qed.

Lemma Lifted_is_true_eq_MapsTo :
  forall {av} ext tenv var (v: W),
    Lifted_MapsTo (av := av) ext tenv var (wrap v) ->
    Lifted_is_true ext tenv (var = v)%facade.
Proof.
  unfold Lifted_is_true, Lifted_MapsTo, LiftPropertyToTelescope, is_true, is_false, eval_bool, eval.
  repeat match goal with
         | _ => cleanup_facade_pure
         | _ => SameValues_Facade_t_step
         | [ H: forall _, _ -> _, H': _ |- _ ] => specialize (H _ H')
         | _ => progress simpl
         end.
Qed.

Ltac is_dirty_telescope term :=
  match term with
  | appcontext[DropName] => idtac
  | _ => fail 1
  end.

Ltac decide_TelEq_instantiate_do_swaps k target :=
  match target with
  | context[k] => repeat setoid_rewrite (TelEq_swap _ k)
  | _ => idtac
  end.

Ltac decide_TelEq_instantiate_step :=
  match goal with
  | [  |- TelEq _ ?from ?to ] =>
    match constr:(from, to) with
    | _ => rewrite DropName_Cons_Some_eq by congruence
    | _ => rewrite DropName_Cons_Some_neq by congruence
    | (Cons NTNone _ _, _) => apply TelEq_chomp_None_left; [ eexists; reflexivity | red; intros ]
    | (_, Cons NTNone _ _) => apply TelEq_chomp_None_right; [ eexists; reflexivity | red; intros ]
    | (Cons ?k _ _, ?t) => decide_TelEq_instantiate_do_swaps k t; apply TelEq_chomp_head; red; intros
    | (?t, Cons ?k _ _) => decide_TelEq_instantiate_do_swaps k t; apply TelEq_chomp_head; red; intros
    | context [DropName ?k ?tenv] => first [ is_dirty_telescope tenv; fail 1 |
                                            rewrite (DropName_NotInTelescope tenv k) by eauto ]
    | _ => apply TelEq_refl
    end
  end.

Ltac decide_TelEq_instantiate :=
  repeat decide_TelEq_instantiate_step.

Ltac clean_telescope tel ext :=
  let clean := fresh in
  let type := type of tel in
  let clean := fresh in
  evar (clean: type);
    setoid_replace tel with clean using relation (@TelEq _ ext);
    unfold clean;
    clear clean;
    [ | decide_TelEq_instantiate ].

Ltac Lifted_t :=
  repeat match goal with
         | _ => congruence
         | [  |- _ ∉ _ ] => decide_not_in
         | [  |- StringMap.MapsTo _ _ _ ] => decide_mapsto
         | [  |- NotInTelescope _ _ ] => decide_NotInTelescope
         | [  |- TelEq _ _ _ ] => reflexivity
         | [  |- Lifted_MapsTo _ (Cons (NTSome ?k) _ _) ?k' _ ] => apply Lifted_MapsTo_eq
         | [  |- Lifted_MapsTo _ (Cons (NTSome ?k) _ _) ?k' _ ] => apply Lifted_MapsTo_neq; [ congruence | ]
         | [  |- Lifted_not_mapsto_adt _ (Cons (NTSome ?k) _ _) ?k' ] => apply Lifted_not_mapsto_adt_eq
         | [  |- Lifted_not_mapsto_adt _ (Cons (NTSome ?k) _ _) ?k' ] => apply Lifted_not_mapsto_adt_neq; [ congruence | ]
         | [  |- Lifted_not_mapsto_adt _ _ _ ] => apply Lifted_not_In_Telescope_not_in_Ext_not_mapsto_adt; [ decide_not_in | decide_NotInTelescope ]
         | [  |- Lifted_is_true _ _ _ ] => apply Lifted_is_true_eq_MapsTo (* Coercions make precise matching hard *)
         end.
