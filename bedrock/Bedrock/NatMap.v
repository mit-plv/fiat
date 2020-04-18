Require Import Coq.omega.Omega.
Require Import Coq.Structures.OrderedType Coq.FSets.FMapAVL.
Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses.
Require Import Bedrock.Reflection.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Set Implict Arguments.
Set Strict Implicit.

Module Ordered_nat <: OrderedType with Definition t := nat.
  Definition t := nat.
  Definition eq := @eq nat.
  Definition lt := @lt.

  Theorem eq_refl : forall x, eq x x.
    reflexivity.
  Qed.

  Theorem eq_sym : forall a b, eq a b -> eq b a.
    intros; symmetry; auto.
  Qed.

  Theorem eq_trans : forall a b c, eq a b -> eq b c -> eq a c.
    intros; etransitivity; eauto.
  Qed.

  Theorem lt_trans : forall a b c, lt a b -> lt b c -> lt a c.
    intros. unfold lt in *. omega.
  Qed.

  Theorem lt_not_eq : forall a b, lt a b -> ~(eq a b).
    unfold eq, lt. intros; omega.
  Qed.

  Definition compare (x y : t) : OrderedType.Compare lt eq x y :=
    match Compare_dec.nat_compare x y as r return
      Compare_dec.nat_compare x y = r -> OrderedType.Compare lt eq x y
      with
      | Lt => fun pf => OrderedType.LT (lt:=lt) (nat_compare_Lt_lt _ _ pf)
      | Eq => fun pf => OrderedType.EQ (lt:=lt) (Compare_dec.nat_compare_eq _ _ pf)
      | Gt => fun pf => OrderedType.GT (lt:=lt) (nat_compare_Gt_gt _ _ pf)
    end (refl_equal _).

  Definition eq_dec (x y : nat) : {x = y} + {x <> y} :=
    match beq_nat x y as r return
      beq_nat x y = r -> {x = y} + {x <> y} with
      | true => fun pf => left (beq_nat_true _ _ pf)
      | false => fun pf => right (beq_nat_false _ _ pf)
    end (refl_equal _).


End Ordered_nat.

Module IntMap := FMapAVL.Make Ordered_nat.

Remove Hints IntMap.E.eq_sym IntMap.E.eq_refl IntMap.E.eq_trans IntMap.E.lt_not_eq IntMap.E.lt_trans
  IntMap.Raw.Proofs.L.PX.eqk_refl IntMap.Raw.Proofs.L.PX.eqk_sym
  IntMap.Raw.Proofs.L.PX.eqk_trans
  IntMap.Raw.Proofs.PX.eqk_refl IntMap.Raw.Proofs.PX.eqk_sym IntMap.Raw.Proofs.PX.eqk_trans
  IntMap.Raw.Proofs.L.PX.eqke_refl IntMap.Raw.Proofs.L.PX.eqke_sym IntMap.Raw.Proofs.L.PX.eqke_trans
  IntMap.Raw.Proofs.PX.eqke_refl IntMap.Raw.Proofs.PX.eqke_sym IntMap.Raw.Proofs.PX.eqke_trans
  IntMap.Raw.Proofs.L.PX.MO.lt_eq IntMap.Raw.Proofs.L.PX.MO.eq_lt IntMap.Raw.Proofs.L.MX.lt_eq
  IntMap.Raw.Proofs.L.MX.eq_lt IntMap.Raw.Proofs.PX.MO.lt_eq IntMap.Raw.Proofs.PX.MO.eq_lt
  IntMap.Raw.Proofs.MX.lt_eq IntMap.Raw.Proofs.MX.eq_lt
  IntMap.Raw.Proofs.L.PX.eqk_ltk IntMap.Raw.Proofs.L.PX.ltk_eqk IntMap.Raw.Proofs.L.PX.ltk_trans
  IntMap.Raw.Proofs.PX.eqk_ltk IntMap.Raw.Proofs.PX.ltk_eqk IntMap.Raw.Proofs.PX.ltk_trans
  IntMap.Raw.Proofs.L.PX.MO.lt_antirefl
  IntMap.Raw.Proofs.L.MX.lt_antirefl IntMap.Raw.Proofs.PX.MO.lt_antirefl IntMap.Raw.Proofs.MX.lt_antirefl
  IntMap.Raw.Proofs.L.PX.eqk_not_ltk IntMap.Raw.Proofs.L.PX.ltk_not_eqke
  IntMap.Raw.Proofs.L.PX.ltk_not_eqk IntMap.Raw.Proofs.L.PX.MO.lt_not_gt
  IntMap.Raw.Proofs.L.PX.MO.eq_not_gt IntMap.Raw.Proofs.L.PX.MO.eq_neq
  IntMap.Raw.Proofs.L.PX.MO.neq_eq IntMap.Raw.Proofs.L.PX.MO.eq_le
  IntMap.Raw.Proofs.L.PX.MO.le_eq IntMap.Raw.Proofs.L.PX.MO.eq_not_lt
  IntMap.Raw.Proofs.L.PX.MO.gt_not_eq IntMap.Raw.Proofs.L.MX.lt_not_gt
  IntMap.Raw.Proofs.L.MX.eq_not_gt IntMap.Raw.Proofs.L.MX.eq_neq
  IntMap.Raw.Proofs.L.MX.neq_eq IntMap.Raw.Proofs.L.MX.eq_le
  IntMap.Raw.Proofs.L.MX.le_eq IntMap.Raw.Proofs.L.MX.eq_not_lt
  IntMap.Raw.Proofs.L.MX.gt_not_eq IntMap.Raw.Proofs.PX.eqk_not_ltk
  IntMap.Raw.Proofs.PX.ltk_not_eqke IntMap.Raw.Proofs.PX.ltk_not_eqk
  IntMap.Raw.Proofs.PX.MO.lt_not_gt IntMap.Raw.Proofs.PX.MO.eq_not_gt
  IntMap.Raw.Proofs.PX.MO.eq_neq IntMap.Raw.Proofs.PX.MO.neq_eq
  IntMap.Raw.Proofs.PX.MO.eq_le IntMap.Raw.Proofs.PX.MO.le_eq
  IntMap.Raw.Proofs.PX.MO.eq_not_lt IntMap.Raw.Proofs.PX.MO.gt_not_eq
  IntMap.Raw.Proofs.MX.lt_not_gt IntMap.Raw.Proofs.MX.eq_not_gt
  IntMap.Raw.Proofs.MX.eq_neq IntMap.Raw.Proofs.MX.neq_eq
  IntMap.Raw.Proofs.MX.eq_le IntMap.Raw.Proofs.MX.le_eq
  IntMap.Raw.Proofs.MX.eq_not_lt IntMap.Raw.Proofs.MX.gt_not_eq
  IntMap.Raw.Proofs.L.PX.Sort_Inf_NotIn IntMap.Raw.Proofs.PX.Sort_Inf_NotIn
  IntMap.Raw.Proofs.L.PX.Inf_eq IntMap.Raw.Proofs.L.PX.MO.Inf_lt
  IntMap.Raw.Proofs.L.MX.Inf_lt IntMap.Raw.Proofs.PX.Inf_eq
  IntMap.Raw.Proofs.PX.MO.Inf_lt IntMap.Raw.Proofs.MX.Inf_lt
  IntMap.Raw.Proofs.L.PX.Inf_lt IntMap.Raw.Proofs.L.PX.MO.Inf_lt
  IntMap.Raw.Proofs.L.MX.Inf_lt IntMap.Raw.Proofs.PX.Inf_lt
  IntMap.Raw.Proofs.PX.MO.Inf_lt IntMap.Raw.Proofs.MX.Inf_lt
  IntMap.Raw.InRight IntMap.Raw.InLeft IntMap.Raw.InRoot
  IntMap.Raw.Proofs.L.PX.InA_eqke_eqk IntMap.Raw.Proofs.L.PX.MO.In_eq
  IntMap.Raw.Proofs.L.PX.MO.ListIn_In IntMap.Raw.Proofs.L.MX.In_eq
  IntMap.Raw.Proofs.L.MX.ListIn_In IntMap.Raw.Proofs.PX.InA_eqke_eqk
  IntMap.Raw.Proofs.PX.MO.In_eq IntMap.Raw.Proofs.PX.MO.ListIn_In
  IntMap.Raw.Proofs.MX.In_eq IntMap.Raw.Proofs.MX.ListIn_In
  IntMap.Raw.Proofs.L.PX.In_inv_3 IntMap.Raw.Proofs.PX.In_inv_3
  IntMap.Raw.Proofs.L.PX.In_inv_2 IntMap.Raw.Proofs.PX.In_inv_2
  IntMap.Raw.MapsRight IntMap.Raw.MapsLeft
  IntMap.Raw.MapsRoot IntMap.Raw.Proofs.L.PX.MO.Sort_NoDup
  IntMap.Raw.Proofs.L.MX.Sort_NoDup IntMap.Raw.Proofs.PX.MO.Sort_NoDup
  IntMap.Raw.Proofs.MX.Sort_NoDup
  IntMap.Raw.BSLeaf IntMap.Raw.BSNode IntMap.Raw.Leaf IntMap.Raw.Node.

Require Coq.FSets.FMapFacts.
Module IntMapFacts := FMapFacts.WFacts_fun(Ordered_nat)(IntMap).

Module IntMapProperties := FMapFacts.WProperties_fun(Ordered_nat)(IntMap).

Definition singleton {T} (k : nat) (v : T) : IntMap.t T :=
  IntMap.add k v (IntMap.empty _).

(** Neither Properties nor Facts contains anything useful about 'map' **)
Module MoreFMapFacts (FM : FMapInterface.WS)
.
  Module PROPS := FMapFacts.WProperties_fun(FM.E) FM.
  Module FACTS := FMapFacts.WFacts_fun FM.E FM.

  Definition union T :=
    FM.fold (fun k (v : T) a => FM.add k v a).

  Lemma add_remove_Equal : forall (elt : Type) k (v : elt) m,
    FM.Equal (FM.add k v m) (FM.add k v (FM.remove k m)).
  Proof.
    clear. unfold FM.Equal. intros.
    repeat (rewrite FACTS.add_o || rewrite FACTS.remove_o).
    destruct (FM.E.eq_dec k y); auto.
  Qed.

  Lemma MapsTo_add_remove_Equal : forall (elt : Type) k (v : elt) m,
    FM.MapsTo k v m ->
    FM.Equal m (FM.add k v (FM.remove k m)).
  Proof.
    clear. unfold FM.Equal. intros.
    repeat (rewrite FACTS.add_o || rewrite FACTS.remove_o).
    destruct (FM.E.eq_dec k y); auto.
    rewrite <- e. apply FACTS.find_mapsto_iff; auto.
  Qed.

  Lemma map_Empty : forall T U (F : T -> U) m,
    FM.Empty m ->
    FM.Empty (FM.map F m).
  Proof.
    intros.
    unfold FM.Empty in *.
    intros. intro.
    eapply FACTS.map_mapsto_iff in H0. destruct H0; intuition. eauto.
  Qed.

  Lemma map_Add : forall T U (F : T -> U) x e m m',
    PROPS.Add x e m m' ->
    PROPS.Add x (F e) (FM.map F m) (FM.map F m').
  Proof.
    unfold PROPS.Add; intros.
    specialize (H y).
    repeat (rewrite FACTS.add_o in * || rewrite FACTS.map_o in *).
    rewrite H. destruct (FM.E.eq_dec x y); reflexivity.
  Qed.

  Lemma map_not_In : forall T U (F : T -> U) x m,
    ~ FM.In x m ->
    ~ FM.In x (FM.map F m).
  Proof.
    intros. intro. apply H; clear H. destruct H0.
    apply FACTS.map_mapsto_iff in H. destruct H.
    exists x1. intuition.
  Qed.

  Lemma union_empty : forall T m,
    FM.Equal (union T m (FM.empty _)) m.
  Proof.
    intros. unfold union.
    remember (FM.empty T).
    apply PROPS.map_induction with (m := m); intros.
      rewrite PROPS.fold_Empty; eauto with typeclass_instances. subst; auto.
      unfold FM.Equal, FM.Empty in *. intros.
      rewrite FACTS.empty_o. case_eq (FM.find y m0); intros; auto.
      exfalso. eapply H. eapply FM.find_2; eauto.

    erewrite PROPS.fold_Add; eauto with typeclass_instances.
    rewrite H. unfold PROPS.Add, FM.Equal in *. eauto.

    repeat (red; intros; subst).
    repeat (rewrite FACTS.add_o).
      destruct (FM.E.eq_dec k y); auto.
      destruct (FM.E.eq_dec k' y); auto. rewrite <- e1 in e2. exfalso; auto.
  Qed.

  Lemma map_fold' : forall T U (F : T -> U) (m : FM.t T) (m' : FM.t U),
    FM.Equal (union _ (FM.map F m) m')
             (FM.fold (fun k v a => FM.add k (F v) a) m m').
  Proof.
    do 4 intro. unfold union.
    eapply PROPS.map_induction with (m := m); intros.
    symmetry.
    rewrite PROPS.fold_Empty; eauto with typeclass_instances.
    rewrite PROPS.fold_Empty; eauto with typeclass_instances. reflexivity.
    eapply map_Empty; auto.

    symmetry; rewrite PROPS.fold_Add; eauto with typeclass_instances.
      specialize (H m'0).
      cut (PROPS.Add x (F e) (FM.map F m0) (FM.map F m')); intros.
      symmetry. rewrite PROPS.fold_Add. 6: eapply H2. 2: eauto with typeclass_instances.
      rewrite H. reflexivity.

      repeat (red; intros; subst). rewrite H3. rewrite H4. reflexivity.
      repeat (red; intros; subst). repeat rewrite FACTS.add_o.
      destruct (FM.E.eq_dec k y); destruct (FM.E.eq_dec k' y); eauto.
      rewrite <- e1 in e2; exfalso; auto.
      intro. apply FACTS.map_in_iff in H3. auto.

      unfold PROPS.Add in *; intros.
      specialize (H1 y). repeat (rewrite FACTS.add_o || rewrite FACTS.map_o || rewrite H1).
      unfold FACTS.option_map.
      destruct (FM.E.eq_dec x y); auto.

      repeat (red; intros; subst). rewrite H3. rewrite H2. reflexivity.
      repeat (red; intros; subst). repeat rewrite FACTS.add_o.
      repeat match goal with
               | [ |- context [ FM.E.eq_dec ?X ?Y ] ] => destruct (FM.E.eq_dec X Y); auto
             end.
      rewrite <- e1 in e2; exfalso; auto.
  Qed.

  Lemma map_fold : forall T U (F : T -> U) m,
    FM.Equal (FM.map F m)
             (FM.fold (fun k v a => FM.add k (F v) a) m (FM.empty _)).
  Proof.
    intros. etransitivity. symmetry; apply union_empty. apply map_fold'.
  Qed.

  Lemma find_empty_iff : forall T (m : FM.t T),
    FM.Empty m <-> forall k, FM.find k m = None.
  Proof.
    unfold FM.Empty. intros. split.
    { intros; case_eq (FM.find k m); auto; intros.
      exfalso. eapply FACTS.find_mapsto_iff in H0. eapply H; eauto. }
    { intros. intro. apply FACTS.find_mapsto_iff in H0.
      specialize (H a). congruence. }
  Qed.

  Lemma find_Empty : forall T k (m : FM.t T),
    FM.Empty m -> FM.find k m = None.
  Proof.
    intros. apply find_empty_iff; auto.
  Qed.


  Section fusion.
    Variable T U V : Type.
    Variable F : T -> U.
    Variable G : FM.key -> U -> V -> V.
    Hypothesis equ : V -> V -> Prop.
    Hypothesis equ_Equiv : RelationClasses.Equivalence equ.
    Hypothesis G_trans: PROPS.transpose_neqkey equ G.
    Hypothesis G_respect: Morphisms.Proper
      (Morphisms.respectful FM.E.eq
        (Morphisms.respectful eq (Morphisms.respectful equ equ))) G.

    Local Hint Resolve G_trans G_respect equ_Equiv.
    Local Hint Extern 1 (Morphisms.Proper _ _) =>
        repeat (red; intros; subst); repeat rewrite FACTS.add_o;
        repeat match goal with
                 | [ |- context [ FM.E.eq_dec ?X ?Y ] ] =>
                   destruct (FM.E.eq_dec X Y)
                 | [ H : FM.E.eq ?X ?Y |- _ ] => rewrite H in *
               end; auto; exfalso; auto.
    Local Hint Extern 1 (PROPS.transpose_neqkey _ _) =>
        repeat (red; intros; subst); repeat rewrite FACTS.add_o;
        repeat match goal with
                 | [ |- context [ FM.E.eq_dec ?X ?Y ] ] =>
                   destruct (FM.E.eq_dec X Y)
                 | [ H : FM.E.eq ?X ?Y |- _ ] => rewrite H in *
               end; auto; exfalso; auto.
    Local Hint Resolve FACTS.EqualSetoid.

    Lemma fold_map_fusion : forall m a,
      equ (FM.fold G (FM.map F m) a)
      (FM.fold (fun k x acc => G k (F x) acc) m a).
    Proof.
      intro. eapply PROPS.map_induction with (m := m); intros.
        rewrite PROPS.fold_Empty; eauto with typeclass_instances.
        rewrite PROPS.fold_Empty; eauto with typeclass_instances. eapply equ_Equiv.
        apply map_Empty. auto.

        symmetry. rewrite PROPS.fold_Add; eauto with typeclass_instances.
        2: repeat (red; intros; subst); eapply G_respect; auto.

        symmetry. rewrite PROPS.fold_Equal. 5: eapply map_fold. 2: eapply equ_Equiv. 3: eapply G_trans.
        2: eapply G_respect.
        rewrite PROPS.fold_Equal. 5: rewrite PROPS.fold_Add; eauto.
        5: reflexivity. rewrite PROPS.fold_add; eauto.
        eapply G_respect; eauto. erewrite <- H.
        symmetry. rewrite PROPS.fold_Equal. 5: apply map_fold. reflexivity. eauto. eauto. eauto.

        { revert H0. clear. revert x. eapply PROPS.map_induction with (m := m0); intros.
          rewrite PROPS.fold_Empty; eauto. intro. eapply FACTS.empty_in_iff; eauto with typeclass_instances.

          rewrite PROPS.fold_Add. 6: eauto. 5: eauto. 2: eauto. 2: eauto. 2: eauto.
          intro. apply FACTS.add_in_iff in H3. destruct H3.
            rewrite <- H3 in *. apply H2. specialize (H1 x). rewrite FACTS.add_o in *.
            destruct (FM.E.eq_dec x x); try solve [ exfalso; auto ]. apply FACTS.in_find_iff. congruence.

            eapply H. 2: eauto. intro. clear H3. specialize (H1 x0).
            rewrite FACTS.add_o in H1.
            repeat match goal with
                     | [ H : ~ FM.In _ _ |- _ ] => apply FACTS.not_find_in_iff in H
                     | [ H : FM.In _ _ |- _ ] => apply FACTS.in_find_iff in H
                   end.
            destruct (FM.E.eq_dec x x0); congruence.
        }

        eauto.
        eauto.
        eauto.
    Qed.

    Lemma remove_empty : forall T k,
      FM.Equal (FM.remove k (FM.empty T)) (FM.empty _).
    Proof.
      clear. unfold FM.Equal; intros.
      rewrite FACTS.remove_o. rewrite FACTS.empty_o. destruct (FM.E.eq_dec k y); auto.
    Qed.

    Lemma remove_Empty : forall T k (m : FM.t T),
      FM.Empty m ->
      FM.Equal (FM.remove k m) m.
    Proof.
      clear. unfold FM.Equal; intros.
      rewrite FACTS.remove_o. consider (FM.E.eq_dec k y); auto.
      eapply find_empty_iff in H; eauto.
    Qed.

    Lemma map_remove : forall k m,
      FM.Equal (FM.map F (FM.remove k m))
               (FM.remove k (FM.map F m)).
    Proof.
      clear; unfold FM.Equal; intros.
      repeat (rewrite FACTS.map_o || rewrite FACTS.remove_o).
      destruct (FM.E.eq_dec k y); reflexivity.
    Qed.

    Lemma map_add : forall k v m,
      FM.Equal (FM.map F (FM.add k v m))
               (FM.add k (F v) (FM.map F m)).
    Proof.
      clear; unfold FM.Equal; intros.
      repeat (rewrite FACTS.map_o || rewrite FACTS.add_o).
      destruct (FM.E.eq_dec k y); reflexivity.
    Qed.

  End fusion.

  Lemma MapsTo_def : forall T k m,
    FM.In k m <-> exists (v : T), FM.MapsTo k v m.
  Proof.
    unfold FM.In; split; auto.
  Qed.

  Global Add Parametric Morphism (elt : Type) F : (@FM.Equiv elt F) with
    signature (FM.Equal ==> FM.Equal ==> iff)
    as equiv_eq_mor.
  Proof.
    intros. unfold FM.Equiv. split; intros.
      intuition; rewrite <- H in *; rewrite <- H0 in *; firstorder.
      intuition; rewrite H in *; rewrite H0 in *; firstorder.
  Qed.

  Section Equiv.
    Variable T : Type.
    Variable R : T -> T -> Prop.
    Hypothesis refl : Reflexive R.

    Global Instance Refl_Equiv : Reflexive (FM.Equiv R).
    Proof.
      revert refl; clear.
      red. unfold FM.Equiv. firstorder.
      apply FACTS.find_mapsto_iff in H.
      apply FACTS.find_mapsto_iff in H0.
      rewrite H in H0. inversion H0; apply refl.
    Qed.

    Lemma Equiv_Add : forall k v m m' n',
      FM.Equiv R m' n' ->
      ~FM.In k m ->
      PROPS.Add k v m m' ->
      exists n v',
        PROPS.Add k v' n n' /\
        ~FM.In k n /\
        FM.Equiv R m n /\
        R v v'.
    Proof.
      intros. unfold PROPS.Add in *.
      destruct H. generalize (H1 k). intros.
      rewrite FACTS.add_o in *. destruct (FM.E.eq_dec k k); try solve [ exfalso; auto ].
      case_eq (FM.find k n'); intros. exists (FM.remove k n'). exists t.
      { intuition.
        rewrite FACTS.add_o. rewrite FACTS.remove_o. destruct (FM.E.eq_dec k y); auto.
        rewrite <- e0; eauto.

        destruct H5. apply FACTS.find_mapsto_iff in H5. rewrite FACTS.remove_o in H5.
        destruct (FM.E.eq_dec k k); congruence.

        split. intros. destruct (FM.E.eq_dec k k0); try rewrite <- e0 in *.
        split; intro; try solve [ exfalso ; auto ]. destruct H5. apply FACTS.find_mapsto_iff in H5.
        rewrite FACTS.remove_o in H5; destruct (FM.E.eq_dec k k); congruence.
        split; intro. apply FACTS.remove_in_iff; split; auto.

        { eapply H. destruct H5. apply FACTS.find_mapsto_iff in H5. exists x. apply FACTS.find_mapsto_iff.
          rewrite H1. rewrite FACTS.add_o. destruct (FM.E.eq_dec k k0); try congruence. }
        { apply FACTS.remove_in_iff in H5. intuition. apply H in H7.
          destruct H7. apply FACTS.find_mapsto_iff in H5. exists x. apply FACTS.find_mapsto_iff.
          rewrite H1 in H5. rewrite FACTS.add_o in H5. destruct (FM.E.eq_dec k k0); try congruence. }
        { intros. apply FACTS.remove_mapsto_iff in H6. intuition.
          specialize (H1 k0). rewrite FACTS.add_o in *.
          destruct (FM.E.eq_dec k k0). congruence.
          apply FACTS.find_mapsto_iff in H5. rewrite <- H1 in *. apply FACTS.find_mapsto_iff in H5.
          eapply H2; eauto. }

        { eapply H2; eapply FACTS.find_mapsto_iff; eauto. } }
      { exfalso. apply FACTS.not_find_in_iff in H4. apply H4. apply H. apply FACTS.find_mapsto_iff in H3; eexists; eauto. }
    Qed.

    Hypothesis sym : Symmetric R.
    Global Instance Sym_Equiv : Symmetric (FM.Equiv R).
    Proof.
      clear refl. red. unfold FM.Equiv. intros.
      intuition; eauto; firstorder.
    Qed.

    Hypothesis trans : Transitive R.
    Global Instance Trans_Equiv : Transitive (FM.Equiv R).
    Proof.
      clear refl sym. red. unfold FM.Equiv. intros.
      intuition.
      eapply H. eapply H1. auto.
      eapply H1; eapply H; auto.
      cut (FM.In k y); intros.
      destruct H5. etransitivity. eapply H2; eauto. eapply H3; eauto.
      eapply H1. eexists; eauto.
    Qed.

  End Equiv.
End MoreFMapFacts.
