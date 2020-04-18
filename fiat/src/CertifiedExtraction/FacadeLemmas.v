Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.PureUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.FacadeUtils.
Require Import Coq.Setoids.Setoid.

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
  MoreStringMapFacts.normalize; reflexivity.
Qed.

Hint Resolve MapsTo_SCA_not_mapsto_adt : SameValues_db.

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

Lemma is_true_eq_MapsTo :
  forall av st var val,
    is_true st (TestE IL.Eq (Var var) (Const val)) ->
    StringMap.MapsTo var (SCA av val) st.
Proof.
  intros.
  unfold is_true, is_false, eval_bool, eval, eval_binop_m, eval_binop, IL.evalTest in *.

  repeat match goal with
         | _ => cleanup_pure
         | _ => cleanup_facade_pure; subst
         | _ => MoreStringMapFacts.normalize
         | [ H: context[StringMap.find ?k ?v] |- _ ] => destruct (StringMap.find k v) eqn:eq0
         | [ H: context[IL.weqb ?a ?b] |- _ ] => destruct (IL.weqb a b) eqn:eq1
         | [ H: Value _ |- _ ] => destruct H
         | [ H: _ = Some _ |- _ ] => compute in H
         end.
Qed.

Lemma is_true_is_false_contradiction :
  forall av expr st,
    @is_true av expr st ->
    @is_false av expr st ->
    False.
Proof.
  unfold is_true, is_false; intros; congruence.
Qed.
