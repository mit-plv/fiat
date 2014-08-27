Require Import Common.
Require Export BagsInterface BagsProperties.
Require Import SetEqProperties FMapExtensions AdditionalLemmas AdditionalPermutationLemmas.
Require Import FMapInterface Coq.FSets.FMapFacts.

Unset Implicit Arguments.

(* A class for Bags whose update functions preserve the key
Class KeyPreservingUpdateBag
      {TItem : Type}
      {TKey : Type}
      (TKeyEq : TKey -> TKey -> Prop)
      (projection: TItem -> TKey)
  := { KP_BagProof :> @BagPlusBagProof TItem;
       KeyPreservation_Proof : KeyPreservingUpdate TKeyEq projection KP_BagProof }. *)

Module TreeBag (Import M: WS).
  Module Import BasicFacts := WFacts_fun E M.
  Module Import BasicProperties := WProperties_fun E M.
  Module Import MoreFacts := FMapExtensions_fun E M.

  Definition TKey := key.

  Section TreeBagDefinitions.

    Context {TItem : Type}
            (TBag : Bag TItem)
            (TBagCorrect : CorrectBag TBag).

    Variables (projection: TItem -> TKey)
              (key_preserving_Update :
                 forall K item updateTerm,
                   E.eq (projection item) K
                   -> E.eq (projection (bupdate_transform updateTerm item)) K ).

    Definition IndexedBag := t BagType.

    Definition IndexedTree_RepInv fmap :=
      forall (key: TKey) (bag: BagType),
        MapsTo key bag fmap ->
        forall (item: TItem),
          List.In item (benumerate bag) ->
          E.eq (projection item) key.

    Definition KeyFilter (key: TKey) (item : TItem) :=
      if E.eq_dec (projection item) key then true else false.

    Lemma KeyFilter_beq :
      forall beq,
        (forall x y, reflect (E.eq x y) (beq x y)) ->
        (forall key (item: TItem),
           KeyFilter key item = beq (projection item) key).
    Proof.
      intros beq spec key item.
      specialize (spec (projection item) key).
      unfold KeyFilter.
      destruct spec as [ is_eq | neq ];
        destruct (F.eq_dec _ _); intuition.
    Qed.

    Lemma iconsistency_empty :
      IndexedTree_RepInv (empty BagType).
    Proof.
      unfold IndexedTree_RepInv;
      intros; rewrite empty_mapsto_iff in *; exfalso; trivial.
    Qed.

    Lemma consistency_key_eq :
      forall (container : IndexedBag)
        (key: TKey) bag item,
        IndexedTree_RepInv container ->
        MapsTo key bag container ->
        List.In item (benumerate bag) ->
        E.eq (projection item) key.
    Proof.
      intros.
      unfold IndexedTree_RepInv in *.
      eauto.
    Qed.

    Ltac destruct_if :=
      match goal with
          [ |- context [ if ?cond then _ else _ ] ] => destruct cond
      end.

    Lemma KeyFilter_true :
      forall k item,
        KeyFilter k item = true <-> E.eq (projection item) k.
    Proof.
      unfold KeyFilter; intros;
      destruct_if; intros; intuition.
    Qed.

    Lemma KeyFilter_false :
      forall k item,
        KeyFilter k item = false <-> ~ E.eq (projection item) k.
    Proof.
      unfold KeyFilter; intros;
      destruct_if; intros; intuition.
    Qed.

    Definition IndexedBag_bempty := empty BagType.

    Definition IndexedBag_bstar :=
      (@None TKey, bstar).

    Definition IndexedBag_bid :=
      (@None TKey, bid).

    Definition IndexedBag_bfind_matcher
               (key_searchterm: (option TKey) * SearchTermType) (item: TItem) :=
      let (key_option, search_term) := key_searchterm in
      match key_option with
        | Some k => KeyFilter k item
        | None   => true
      end && (bfind_matcher search_term item).

    Definition IndexedBag_benumerate
               (container: IndexedBag) :=
      flatten (List.map benumerate (Values container)).

    Definition IndexedBag_bfind
               (container: IndexedBag)
               (key_searchterm: (option TKey) * SearchTermType) :=
      match key_searchterm with
        | (key_option, search_term) =>
          match key_option with
            | Some k =>
              match find k container with
                | Some bag => bfind bag search_term
                | None     => nil
              end
            | None   =>
              flatten (List.map (fun bag => bfind bag search_term) (Values container))
          end
      end.

    Definition IndexedBag_binsert
               (container: IndexedBag)
               (item: TItem) : IndexedBag :=
      let k := projection item in
      let fmap := container in
      let bag := FindWithDefault k bempty fmap in
        add k (binsert bag item) fmap.

    Definition IndexedBag_bcount
               (container: IndexedBag)
               (key_searchterm: (option TKey) * SearchTermType) :=
      let (key_option, search_term) := key_searchterm in
      match key_option with
        | Some k =>
          match find k container with
            | Some bag => bcount bag search_term
            | None     => 0
          end
        | None   =>
          fold (fun _ bag acc => acc + bcount bag search_term)
               container 0
      end.

    Definition IndexedBag_bdelete
               (container: IndexedBag)
               (key_searchterm: (option TKey) * SearchTermType)
    : (list TItem) * IndexedBag :=
      let (key_option, search_term) := key_searchterm in
      match key_option with
        | Some k => match find k container with
                      | Some bag =>
                        let (d,r) := bdelete bag search_term in
                        (d, add k r container)
                      | None => (nil, container)
                    end
        | None => fold (fun k bag (res : (list TItem) * (t BagType)) =>
                          match bdelete bag search_term with
                            | (d, r) => let (d', r') := res in
                                        (d ++ d', add k r r')
                          end) (container) ([], empty BagType)
      end.

    Definition IndexedBag_bupdate
               (container: IndexedBag)
               (key_searchterm: (option TKey) * SearchTermType)
               (updateTerm : UpdateTermType)
    : IndexedBag :=
      let (key_option, search_term) := key_searchterm in
      match key_option with
        | Some k => match find k container with
                      | Some bag => add k (bupdate bag search_term updateTerm) container
                      | None => container
                    end
        | None => map (fun bag => bupdate bag search_term updateTerm) container
      end.

  Instance IndexedBagAsBag
  : Bag TItem :=
    {| BagType := IndexedBag;
       SearchTermType := prod (option TKey) (SearchTermType);
       UpdateTermType := UpdateTermType;

       bempty            := IndexedBag_bempty;
       bstar             := IndexedBag_bstar;
       bid               := bid;
       bfind_matcher     := IndexedBag_bfind_matcher ;
       bupdate_transform := bupdate_transform;

       benumerate := IndexedBag_benumerate;
       bfind      := IndexedBag_bfind;
       binsert    := IndexedBag_binsert;
       bcount     := IndexedBag_bcount;
       bdelete    := IndexedBag_bdelete;
       bupdate    := IndexedBag_bupdate |}.

    Lemma IndexedBag_bdelete_consistent
          (container: IndexedBag)
          (key_searchterm: (option TKey) * SearchTermType)
          (containerCorrect : IndexedBagCorrect container)
    : IndexedTree_RepInv (snd (IndexedBag_bdelete' container key_searchterm)).
    Proof.
      intros; destruct key_searchterm; destruct o; simpl in *;
      unfold IndexedTree_RepInv; intros.
      - case_eq (find t0 (ifmap container)); intros; rewrite H1 in *.
        + case_eq (bdelete b s); intros; rewrite H2 in *; simpl in *.
          rewrite add_mapsto_iff in H; intuition; subst.
          * pose proof (bdelete_correct b s); subst; rewrite H2 in *;
            simpl in *; intuition.
            apply find_2 in H1; rewrite <- H.
            eapply iconsistency; eauto.
            eapply In_partition; eauto using Permutation_in, In_partition.
          * eapply iconsistency; eauto.
        +  eapply iconsistency; eauto.
      - destruct containerCorrect as [WF_bag']; simpl in *.
        rewrite fold_pair in H; simpl in H.
        rewrite FMap_Insert_fold_add_map_eq in H.
        rewrite map_mapsto_iff in H; destruct_ex; intuition; subst.
        eapply WF_bag'; eauto.
        destruct (bdelete_correct x s).
        eapply In_partition; right; eapply Permutation_in; eauto.
    Defined.

    Lemma IndexedBag_bupdate'_consistent
          (container : IndexedBag)
          (key_searchterm: (option TKey) * SearchTermType)
          (updateTerm : UpdateTermType)
          (containerCorrect : IndexedBagCorrect container)
    : IndexedTree_RepInv (IndexedBag_bupdate' container key_searchterm updateTerm).
    Proof.
      intros; destruct key_searchterm; destruct o; simpl in *.
      - case_eq (find t0 (ifmap container)); intros; eauto using iconsistency.
        unfold IndexedTree_RepInv; intros.
        apply add_mapsto_iff in H0; intuition.
        + pose proof (bupdate_correct b s updateTerm).
          rewrite <- H3 in H1.
          apply find_2 in H; rewrite <- H0.
          pose proof (Permutation_in _ H2 H1) as H4;
            apply in_app_or in H4; destruct H4.
          * pose proof ((proj2 (In_partition _ _ _)) (or_intror H4));
            eapply iconsistency; eauto.
          * apply in_map_iff in H4; destruct H4 as [item' [item'_eq In_item']].
            pose proof (iconsistency _ containerCorrect _ _ H _
                                     ((proj2 (In_partition _ _ _)) (or_introl In_item'))).
            rewrite <- H4.
            rewrite <- item'_eq.
            eapply key_preserving_Update; eauto using In_partition_matched.
        + eapply iconsistency; eauto.
      - unfold IndexedTree_RepInv; intros.
        apply map_mapsto_iff in H;
          destruct H as [bag' [bag'_eq MapsTo_key0]]; subst.
        pose proof (bupdate_correct bag' s updateTerm).
        pose proof (Permutation_in _ H H0) as H4;
          apply in_app_or in H4; destruct H4.
        + pose proof ((proj2 (In_partition _ _ _)) (or_intror H1));
          eapply iconsistency; eauto.
        + apply in_map_iff in H1; destruct H1 as [item' [item'_eq In_item']].
          pose proof (iconsistency _ containerCorrect _ _ MapsTo_key0 _
                                   ((proj2 (In_partition _ _ _)) (or_introl In_item'))).
          rewrite <- H1.
          rewrite <- item'_eq.
          eapply key_preserving_Update; eauto using In_partition_matched.
    Defined.

    Definition IndexedBag_bupdate
               (container: IndexedBag)
               (key_searchterm: (option TKey) * SearchTermType)
               (updateTerm : UpdateTermType)
    : IndexedBag :=
      {| ifmap := IndexedBag_bupdate' container key_searchterm updateTerm |}.


    Lemma indexed_bag_insert_consistent :
      forall (container: IndexedBag)
             (item: TItem)
             (containerCorrect : IndexedBagCorrect container),
        let k := projection item in
        let fmap := ifmap container in
        let bag := FindWithDefault k bempty fmap in
        IndexedTree_RepInv (add k (binsert bag item) fmap).
    Proof.
      intros.

      intros k' bag' maps_to item'.

      rewrite add_mapsto_iff in maps_to;
        destruct maps_to as [(is_eq & refreshed) | (neq & maps_to)];
        subst.

      rewrite (binsert_enumerate_weak item' item bag).
      intro H; destruct H.
      apply ((iconsistency _ containerCorrect) k' bag); trivial.

      rewrite <- is_eq.
      unfold bag in *.

      unfold fmap in *.
      destruct (FindWithDefault_dec k bempty (ifmap container))
        as [ [bag' (mapsto & equality)] | (not_found & equality) ];
        rewrite equality in *; clear equality.

      subst; trivial.
      exfalso; apply (benumerate_empty) in H; trivial.

      subst.
      unfold k in *.
      trivial.

      apply ((iconsistency _ containerCorrect) k' bag' maps_to item').
    Qed.


    Add Parametric Morphism {A} :
      (@cons A)
        with signature (eq ==> eq ==> eq)
          as cons_eq_eq_eq_morphism.
    Proof.
      trivial.
    Qed.

    Definition KeyBasedPartitioningFunction BagType reference :=
      fun key (_: BagType) => if E.eq_dec key reference then true else false.

    Lemma KeyBasedPartitioningFunction_Proper :
      forall BagType reference,
        Proper (E.eq ==> eq ==> eq) (KeyBasedPartitioningFunction BagType reference).
    Proof.
      intros;
      unfold KeyBasedPartitioningFunction, Proper, respectful; intros x y E_eq **; subst;
      destruct (F.eq_dec x _), (F.eq_dec y _); rewrite E_eq in *; intuition.
    Qed.

    Lemma negb_KeyBasedPartitioningFunction_Proper :
      forall BagType reference,
        Proper (E.eq ==> eq ==> eq)
               (fun k e => negb (KeyBasedPartitioningFunction BagType reference k e)).
    Proof.
      intros;
      unfold KeyBasedPartitioningFunction, Proper, respectful; intros x y E_eq **; subst;
      destruct (F.eq_dec x _), (F.eq_dec y _); rewrite E_eq in *; intuition.
    Qed.

    Lemma eq_dec_refl :
      forall x,
        (if E.eq_dec x x then true else false) = true.
    Proof.
      intros; destruct (E.eq_dec _ _); eauto using E.eq_refl.
    Qed.

    Lemma eq_dec_comm :
      forall x y,
        (if E.eq_dec x y then true else false) = (if E.eq_dec y x then true else false).
    Proof.
      intros; destruct (E.eq_dec x y), (E.eq_dec y x); intuition.
    Qed.

    Lemma KeyBasedPartitioningFunction_eq_true :
      forall TValue k k' v,
        E.eq k k' <->
        KeyBasedPartitioningFunction TValue k k' v = true.
    Proof.
      intros; unfold KeyBasedPartitioningFunction; destruct (E.eq_dec _ _); intuition.
    Qed.

    Lemma KeyBasedPartitioningFunction_eq_false :
      forall TValue k k' v,
        ~ E.eq k k' <->
        KeyBasedPartitioningFunction TValue k k' v = false.
    Proof.
      intros; unfold KeyBasedPartitioningFunction; destruct (E.eq_dec _ _); intuition.
    Qed.

    Lemma KeyBasedPartitioningFunction_refl :
      forall TValue k k' v,
        KeyBasedPartitioningFunction TValue k k' v = KeyBasedPartitioningFunction TValue k' k v.
    Proof.
      intros; unfold KeyBasedPartitioningFunction; rewrite eq_dec_comm; reflexivity.
    Qed.

    (* The value [v] mapped to by [k] is the unique value [k] maps to. *)
    Lemma KeyBasedPartition_fst_singleton :
      forall {TValue} k v (m: t TValue),
        MapsTo k v m ->
        Equal (fst (partition (KeyBasedPartitioningFunction TValue k) m)) (add k v (empty TValue)).
    Proof.
      intros.
      symmetry.
      unfold Equal; intro key.

      destruct (E.eq_dec key k) as [ eq_k_proj | neq_k_proj ].

      rewrite eq_k_proj;
        rewrite add_eq_o by eauto;
        symmetry; rewrite <- find_mapsto_iff;
        rewrite partition_iff_1 with (f := KeyBasedPartitioningFunction TValue k) (m := m);
        intuition (try rewrite <- KeyBasedPartitioningFunction_eq_true;
                   eauto using E.eq_refl, KeyBasedPartitioningFunction_Proper).

      rewrite add_neq_o by eauto.
      rewrite empty_o.
      destruct (find key _) eqn:eqfind';
        [ exfalso | eauto ].
      rewrite <- find_mapsto_iff in eqfind'.
      rewrite partition_iff_1 with (f := KeyBasedPartitioningFunction TValue k) (m := m) in eqfind'.
      destruct eqfind' as (maps_to & kvpf_true).
      apply neq_k_proj.
      erewrite KeyBasedPartitioningFunction_eq_true.
      rewrite KeyBasedPartitioningFunction_refl.
      eauto.
      eauto using KeyBasedPartitioningFunction_Proper.
      reflexivity.
    Qed.

    (* If [k'] maps to a value in the first half of a map partitioned on [k],
       it is equivalent to [k]. *)
    Lemma MapsTo_KeyBasedPartition_fst :
      forall {TValue} k k' v (m: t TValue),
        MapsTo k' v (fst (partition (KeyBasedPartitioningFunction TValue k) m)) ->
        E.eq k k'.
    Proof.
      intros * maps_to.
      rewrite partition_iff_1
      with (f := KeyBasedPartitioningFunction TValue k) (m := m)
        in maps_to; eauto using KeyBasedPartitioningFunction_Proper.
      destruct maps_to as (_ & kbpf_true).
      rewrite <- KeyBasedPartitioningFunction_eq_true in kbpf_true.
      trivial.
    Qed.

    Lemma In_KeyBasedPartition_fst :
      forall {TValue} k k' (m: t TValue),
        In k' (fst (partition (KeyBasedPartitioningFunction TValue k) m)) ->
        E.eq k k'.
    Proof.
      intros * in_singleton.
      apply In_MapsTo in in_singleton.
      destruct in_singleton as [ val (maps_to & _) ].
      eapply MapsTo_KeyBasedPartition_fst; eauto.
    Qed.

    (* If [k'] maps to a value in the second half of a map partitioned on [k],
       it is *not* equivalent to [k]. *)
    Lemma MapsTo_KeyBasedPartition_snd :
      forall {TValue} k k' v (m: t TValue),
        MapsTo k' v (snd (partition (KeyBasedPartitioningFunction TValue k) m)) ->
        ~ E.eq k k'.
    Proof.
      intros * maps_to.
      rewrite partition_iff_2
      with (f := KeyBasedPartitioningFunction TValue k) (m := m)
        in maps_to; eauto using KeyBasedPartitioningFunction_Proper.
      destruct maps_to as (_ & kbpf_false).
      rewrite <- KeyBasedPartitioningFunction_eq_false in kbpf_false.
      trivial.
    Qed.

    Lemma In_KeyBasedPartition_snd :
      forall {TValue} k k' (m: t TValue),
        In k' (snd (partition (KeyBasedPartitioningFunction TValue k) m)) ->
        ~ E.eq k k'.
    Proof.
      intros * in_falses.
      apply In_MapsTo in in_falses.
      destruct in_falses as [ val ( maps_to' & _ ) ].
      eapply MapsTo_KeyBasedPartition_snd; eauto.
    Qed.

    (* Paritioning a finite map [m] augmented with a key [k] over [k]
       will produce a map containing just [k] and a map equivalent to [m]. *)
    Lemma partition_after_KeyBasedPartition_and_add :
      forall {TValue} k v' (m: t TValue),
        Partition (add k v' m)
                  (add k v' (fst (partition (KeyBasedPartitioningFunction TValue k) m)))
                  (snd (partition (KeyBasedPartitioningFunction TValue k) m)).
    Proof.
      unfold Partition.
      split.

      {
        unfold Disjoint.
        intros key (in_modified & in_unmodified).
        rewrite add_in_iff in in_modified.

        assert (E.eq k key)
          by (
              destruct in_modified;
              [ assumption | eapply In_KeyBasedPartition_fst; eauto ]
            ); clear in_modified.

        apply In_KeyBasedPartition_snd in in_unmodified.

        intuition.
      }

      split; intros * maps_to'.
      rewrite add_mapsto_iff in maps_to'.
      destruct maps_to' as [ (keq & veq) | (kneq & maps_to') ]; subst.

      left;
        apply add_1; eauto.
      right;
        rewrite partition_iff_2
        with (f := KeyBasedPartitioningFunction TValue k) (m := m)
        by (eauto using KeyBasedPartitioningFunction_Proper);
        rewrite <- KeyBasedPartitioningFunction_eq_false;
        intuition.

      destruct maps_to' as [ maps_to' | maps_to' ].

      rewrite add_mapsto_iff in maps_to';
        destruct maps_to' as [ (keq & veq) | (kneq & maps_to') ];
        [ subst; apply add_1; assumption | ].

      exfalso.
      apply MapsTo_KeyBasedPartition_fst in maps_to'.
      intuition.

      pose proof maps_to'.
      apply MapsTo_KeyBasedPartition_snd in maps_to'.
      apply add_2;
        [ assumption | eapply MapsTo_partition_snd; eauto using KeyBasedPartitioningFunction_Proper ].
    Qed.

    Lemma IndexedBag_BagInsertEnumerate :
      BagInsertEnumerate IndexedBag_benumerate IndexedBag_binsert.
    Proof.
      unfold BagInsertEnumerate, IndexedBag_benumerate.
      intros; simpl in *.

      pose proof bfind_star.
      unfold BagFindStar in H.

      match goal with
        | [ |- context[FindWithDefault ?a ?b ?c] ] =>
          destruct (FindWithDefault_dec a b c)
            as [ [ result (maps_to & _eq) ] | (find_none & _eq) ];
            rewrite _eq; clear _eq
      end.

      (* Existing key *)

      pose proof (partition_after_KeyBasedPartition_and_add
                    (TValue := BagType)
                    (projection inserted)
                    (binsert result inserted)
                    (ifmap container)) as part_add.

      pose proof (partition_Partition_simple
                    (BagType)
                    (KeyBasedPartitioningFunction BagType (projection inserted))
                    (KeyBasedPartitioningFunction_Proper _ _)
                    (ifmap container)) as part.

      rewrite !Values_fold_perm
        by (eauto using Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey).

      rewrite Partition_fold at 1
        by (eauto using part_add, Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey).
      symmetry.

      rewrite Partition_fold at 1
        by (eauto using part    , Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey).
      symmetry.

      pose proof (KeyBasedPartition_fst_singleton (TValue := BagType) _ _ _ maps_to) as singleton.
      pose proof (add_Equal_simple singleton (projection inserted) (binsert result inserted)) as singleton'.

      rewrite (fold_Equal_simpl (eqA := @Permutation BagType) singleton')
        by (eauto using Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey).
      rewrite (fold_Equal_simpl (eqA := @Permutation BagType) singleton)
        by (eauto using Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey).
      rewrite (fold_Equal_simpl (multiple_adds _ _ _ _))
        by (eauto using Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey).
      rewrite !fold_add
        by (eauto using Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey, empty_In).

      rewrite fold_empty.

      simpl.
      rewrite binsert_enumerate.
      rewrite <- app_comm_cons.

      eauto.

      (* New key *)

      rewrite <- not_find_in_iff in find_none.
      rewrite values_add_not_in by assumption.
      simpl.

      rewrite binsert_enumerate.
      rewrite benumerate_empty_eq_nil.
      simpl; reflexivity.
    Qed.

    Lemma fold_map :
      forall {A B C} seq f g init,
        @List.fold_left C A (fun acc x => f acc (g x)) seq init =
        @List.fold_left C B (fun acc x => f acc (  x)) (@List.map A B g seq) init.
    Proof.
      induction seq; simpl; intros; trivial; try rewrite IHseq; intuition.
    Qed.

    Lemma fold_over_Values :
      forall {TValue TAcc} (m: t TValue) f g (init: TAcc),
        (forall k v acc, f k v acc = g acc v) ->
        fold f m init = fold_left g (Values m) init.
    Proof.
      intros * equiv.
      rewrite fold_1.
      setoid_rewrite equiv.
      rewrite fold_map.
      reflexivity.
    Qed.

    Lemma fold_plus_sym :
      forall (seq: list nat) (default: nat),
        List.fold_right plus default seq =
        List.fold_left plus seq default.
    Proof.
      intros; rewrite <- fold_left_rev_right.
      revert default; induction seq; simpl; eauto; intros.
      rewrite fold_right_app; simpl; rewrite <- IHseq.
      clear IHseq; revert a default; induction seq;
      simpl; intros; auto with arith.
      rewrite <- IHseq; omega.
    Qed.

    Lemma IndexedBag_BagCountCorrect :
      BagCountCorrect IndexedBag_bcount IndexedBag_bfind .
    Proof.
      unfold IndexedBag_bcount, IndexedBag_bfind, BagCountCorrect;
      simpl; intros; destruct search_term as [ [ key | ] search_term ].

      + destruct (find _ _); eauto using bcount_correct.
      + rewrite length_flatten.
        rewrite (fold_over_Values _ _ (fun acc bag => acc + bcount bag search_term)) by eauto.
        rewrite <- fold_left_rev_right.
        setoid_rewrite Plus.plus_comm at 1.
        replace (fun (y : BagType) (x : nat) => bcount y search_term + x)
        with (compose plus (fun bag => bcount bag search_term)) by reflexivity.
        rewrite !foldright_compose.

        symmetry; setoid_rewrite <- rev_involutive at 1.
        rewrite fold_left_rev_right, map_rev, rev_involutive.

        rewrite fold_plus_sym, <- !fold_map.
        setoid_rewrite bcount_correct.
        f_equal;
          repeat (apply functional_extensionality; intros);
          auto with arith.
    Qed.

    Lemma IndexedBag_BagEnumerateEmpty :
      BagEnumerateEmpty IndexedBag_benumerate IndexedBag_bempty.
    Proof.
      intros;
      unfold BagEnumerateEmpty, IndexedBag_benumerate, flatten; simpl;
      rewrite Values_empty; tauto.
    Qed.

    Lemma IndexedBag_BagFindStar :
      BagFindStar IndexedBag_bfind IndexedBag_benumerate IndexedBag_bstar.
    Proof.
      unfold BagFindStar, IndexedBag_benumerate; simpl.

      intros; induction (Values (ifmap container)); simpl; trivial.
      rewrite bfind_star.
      f_equal; trivial.
    Qed.

    (* Enumerating the values for each key in an indexed bag [container]
       and filtering those values over a key [k] returns the same set of
       values as enumerating the values of the bag contained at index [k].
       (i.e. [iconsistency] gives us the property we expect.
     *)

    Lemma consist :
        forall
          (container: IndexedBag)
          (containerCorrect : IndexedBagCorrect container),
        forall k,
          flatten
            (List.map (List.filter (KeyFilter k))
                      (List.map benumerate (Values (ifmap container))))
          = match find k (ifmap container) with
              | Some bag => benumerate bag
              | None => nil
            end.
      Proof.
        intros.

        pose (iconsistency container); unfold IndexedTree_RepInv in i.
        unfold Values.
        destruct (find k (ifmap container)) as [ bag | ] eqn:eqfind.

        rewrite <- find_mapsto_iff in eqfind.
        (* assert (exists k', MapsTo k' bag (ifmap container)) as eqfind' by (exists k; trivial).*)

        pose proof eqfind as maps_to.

        rewrite elements_mapsto_iff in eqfind.
        apply InA_split in eqfind.

        destruct eqfind as [ l1 [ y [ l2 (y_k_bag & decomp) ] ] ].
        rewrite decomp.

        rewrite (map_map snd benumerate).
        rewrite ! map_app; simpl.

        pose proof (elements_3w (ifmap container)) as no_dup.
        rewrite decomp in no_dup; apply NoDupA_swap in no_dup; eauto using equiv_eq_key.

        inversion no_dup as [ | ? ? y_not_in no_dup' ]; subst.
        rewrite InA_app_iff in y_not_in by eauto using equiv_eq_key.

        unfold eq_key_elt in y_k_bag; simpl in y_k_bag.
        destruct y_k_bag as (y_k & y_bag).

        assert (forall k' bag', InA (@eq_key_elt _) (k', bag') (l1 ++ l2) ->
                                forall item,
                                  List.In item (benumerate bag') ->
                                  ~ E.eq (projection item) k).
        {
          intros k' bag' in_app item in_bag'_items eq_k.

          rewrite InA_app_iff in in_app; eauto using equiv_eq_key_elt.
          pose proof in_app as in_app'.

          apply (InA_front_tail_InA _ _ y) in in_app.
          rewrite <- decomp, <- elements_mapsto_iff in in_app.

          pose proof (i containerCorrect _ _ in_app _ in_bag'_items) as eq_k'.
          symmetry in eq_k.
          pose proof (E.eq_trans eq_k eq_k').

          assert (eq_key y (k', bag')) as y_eq by (unfold eq_key; simpl; eauto).

          destruct in_app' as [ in_seq | in_seq ];
            (apply (InA_eqke_eqk (k2 := fst y) (snd y)) in in_seq; eauto);
            rewrite <- surjective_pairing in in_seq; intuition.
        }

        rewrite ! map_filter_all_false;
          [ | intros subseq in_map item in_subseq;
              rewrite in_map_iff in in_map;
              destruct in_map as [ (k', bag') (benum_eq & in_seq) ];
              rewrite KeyFilter_false;

              simpl in benum_eq;
              subst subseq;
              apply (H k' bag');
              eauto;

              apply In_InA; eauto using equiv_eq_key_elt;
              rewrite in_app_iff;
              eauto
                .. ].

        rewrite
          flatten_app,
        flatten_head,
        !flatten_nils,
        app_nil_l, app_nil_r,
        <- y_bag,
        filter_all_true; trivial.

        intros;
          rewrite KeyFilter_true;
          apply (iconsistency _ containerCorrect _ bag); eauto.

        rewrite nil_in_false.
        intros [item item_in].

        rewrite in_flatten_iff in item_in.
        do 2 setoid_rewrite in_map_iff in item_in.

        destruct item_in as
            [ subseq
                (in_subseq
                   & [ subseq_prefilter
                         ( pre_post_filter
                             & [ bag
                                   (eq_bag_pre_filter
                                      & bag_in) ] ) ] ) ].

        subst subseq.
        rewrite filter_In in in_subseq.
        destruct in_subseq as (in_subseq_prefilter & key_filter).

        rewrite KeyFilter_true in key_filter.
        rewrite <- MapsTo_snd in bag_in.
        destruct bag_in as [k' maps_to].

        subst.
        rewrite <- key_filter in eqfind.
        rewrite <- (iconsistency _ containerCorrect k' bag maps_to _ in_subseq_prefilter) in maps_to.
        rewrite find_mapsto_iff in maps_to.

        congruence.
      Qed.

    Lemma consist' :
        forall (container: IndexedBag) key,
          Permutation
            (Values (filter
                       (fun (k : M.key) (e : list TItem) =>
                          negb (KeyBasedPartitioningFunction (list TItem) key k e))
                       (map benumerate (ifmap container))))
            (Values (map benumerate (remove key (ifmap container)))).
    Proof.
      intros; eapply Permutation_InA_cons; eauto using elements_3w.
      intros.
      repeat rewrite <- elements_mapsto_iff.
      rewrite filter_iff.
      - intuition; intros.
        + rewrite map_mapsto_iff in H0; destruct H0 as [bag' [eq_bag' filter_k]]; subst.
          rewrite map_mapsto_iff; eexists; split; eauto.
          rewrite remove_mapsto_iff; split; eauto.
          unfold not; intros.
          rewrite KeyBasedPartitioningFunction_eq_true in H;
            rewrite H in H1; discriminate.
        + rewrite map_mapsto_iff in H; destruct H as [bag' [eq_bag' filter_k]]; subst.
          rewrite remove_mapsto_iff in filter_k; intuition.
        + rewrite map_mapsto_iff in H; destruct H as [bag' [eq_bag' filter_k]]; subst.
          rewrite remove_mapsto_iff in filter_k; intuition.
          eapply KeyBasedPartitioningFunction_eq_false in H; rewrite H;
          reflexivity.
      - unfold Proper; compute; intros; subst; trivial.
        destruct (F.eq_dec x _), (F.eq_dec y _); rewrite H in *; intuition.
    Qed.

    Print BagFindCorrect.

    Lemma IndexedBag_BagFindCorrect :
      BagFindCorrect IndexedBag_bfind IndexedBag_bfind_matcher IndexedBag_benumerate.
    Proof.
      intros.
      destruct search_term as (option_key, search_term).
      destruct option_key as [ key | ].

      (* Key provided *)

      unfold IndexedBag_benumerate, IndexedBag_bfind_matcher.
      pose (iconsistency container).
      unfold IndexedTree_RepInv in i.

      rewrite filter_and'.

      rewrite flatten_filter.


      simpl.
      rewrite consist.
      destruct (find key (ifmap container)) as [ bag | ].

      apply bfind_correct.
      eauto.

      (* No key provided *)

      simpl. unfold IndexedBag_benumerate, IndexedBag_bfind_matcher.
      rewrite flatten_filter.

      induction (Values (ifmap container)); simpl.

      eauto.

      apply Permutation_app.
      apply (bfind_correct _).

      rewrite IHl; reflexivity.
    Qed.

    Lemma partition_filter_eq {A} :
      forall (f : A -> bool) l,
        fst (List.partition f l) = List.filter f l.
    Proof.
      induction l; simpl; eauto.
      destruct (List.partition f l); destruct (f a); simpl in *; congruence.
    Qed.

    Lemma partition_filter_neq {A} :
      forall (f : A -> bool) l,
        snd (List.partition f l) = List.filter (fun a => negb (f a)) l.
    Proof.
      induction l; simpl; eauto.
      destruct (List.partition f l); destruct (f a); simpl in *; congruence.
    Qed.

    Lemma snd_bdelete_eq_bdelete' :
      forall container search_term,
        ifmap (snd (IndexedBag_bdelete container search_term))
        = snd (IndexedBag_bdelete' container search_term).
    Proof.
      unfold IndexedBag_bdelete, IndexedBag_bdelete'; simpl.
      assert (forall (l' : (list TItem) * (t BagType)) Pl',
                ifmap
                  (snd
                     ((let (deleted, container') as l
                           return
                           (IndexedTree_RepInv (snd l) -> list TItem * IndexedBag) :=
                           l' in
                       fun i : IndexedTree_RepInv container' =>
            (deleted, {| ifmap := container'; iconsistency := i |}))
                        Pl')) =
                snd l') as H by (destruct l'; simpl; eauto).
      destruct search_term; destruct o; apply H.
    Qed.

    Lemma fst_bdelete_eq_bdelete' :
      forall container search_term,
        fst (IndexedBag_bdelete container search_term)
        = fst (IndexedBag_bdelete' container search_term).
    Proof.
      unfold IndexedBag_bdelete, IndexedBag_bdelete'; simpl.
      assert (forall (l' : (list TItem) * (t BagType)) Pl',
                fst ((let (deleted, container') as l
                           return
                           (IndexedTree_RepInv (snd l) -> list TItem * IndexedBag) :=
                           l' in
                       fun i : IndexedTree_RepInv container' =>
                         (deleted, {| ifmap := container'; iconsistency := i |}))
                       Pl') =
                fst l') as H by (destruct l'; simpl; eauto).
      destruct search_term; destruct o; apply H.
    Qed.

    (* Lemma Permutation_map_Values {A B} eqA :
      forall (f : A -> B) m x,
        InA eqA x (map f m) <->
        exists x', InA x' (Values m) /\ x = f x'.
      unfold Values; split; intros.
      rewrite in_map_iff in H.
      destruct H as [[k b] [eq_b In_kb]]; simpl in *; subst.
      apply in_elements_mapsto in In_kb.
      rewrite map_mapsto_iff in In_kb;
        destruct In_kb as [a [a_eq In_a]]; subst.
      eexists; split; eauto.
      apply InA_In.
      apply elements_1 in In_a; induction In_a; simpl. *)

    Lemma map_snd {A B C} :
      forall (f : A -> B) (l : list (C * A)),
        List.map f (List.map snd l) =
        List.map snd (List.map (fun ca => (fst ca, f (snd ca))) l).
    Proof.
      intros; repeat rewrite List.map_map; induction l; simpl; eauto.
    Qed.

    Lemma Permutation_map_Values {A B} :
      forall (f : A -> B) m,
        Permutation
          (List.map f (Values m))
          (Values (map f m)).
    Proof.
      unfold Values; intros.
      rewrite map_snd.
      apply Permutation_InA_cons; eauto using elements_3w.
      - pose proof (elements_3w m) as NoDupM.
        induction NoDupM; simpl in *; simpl; constructor; eauto.
        unfold not; intros; apply H; clear NoDupM IHNoDupM H;
        induction l; simpl in *; inversion H0; subst; eauto.
      - split; intros.
        apply elements_1.
        rewrite InA_Map in H; destruct H as [[k' v'] [eq_k In_k]];
        destruct eq_k; simpl in *; subst.
        rewrite H; eauto using elements_2, map_1, In_InA, equiv_eq_key_elt.
        rewrite InA_Map.
        apply elements_2 in H.
        apply map_mapsto_iff in H; destruct H as [a [a_eq MapsTo_k]]; subst.
        apply elements_1 in MapsTo_k.
        rewrite InA_alt in MapsTo_k.
        destruct MapsTo_k as [[k' a'] [eq_k In_k]].
        eexists; split; eauto.
        destruct eq_k; simpl in *; subst; constructor; eauto.
    Qed.

    Lemma Permutation_filter_Values {B} :
      forall (f : key -> B -> bool) m
             (Proper_f : Proper (E.eq ==> eq ==> eq) f),
        Permutation
          (Values (filter f m))
          (List.map snd (List.filter (fun kv => f (fst kv) (snd kv)) (elements m))).
    Proof.
      unfold Values; intros.
      apply Permutation_InA_cons; eauto using elements_3w.
      - pose proof (elements_3w m) as NoDupM.
        induction NoDupM; simpl in *; simpl; try constructor.
        case_eq (f (fst x) (snd x)); simpl; eauto.
        intros; constructor; eauto.
        unfold not; intros; apply H; clear NoDupM IHNoDupM H;
        induction l; simpl in *.
        inversion H0; subst; eauto.
        case_eq (f (fst a) (snd a)); intros; rewrite H in *; eauto.
        inversion H1; subst.
        constructor; eauto.
        constructor 2; eauto.
      - intros; rewrite <- elements_mapsto_iff, filter_iff; eauto;
        intuition.
        + rewrite elements_mapsto_iff in H0; induction H0.
          * simpl; destruct H; rewrite Proper_f in H1; eauto;
            rewrite H1; repeat constructor; eauto.
          * simpl; destruct (f (fst y) (snd y)); simpl; eauto.
        + rewrite elements_mapsto_iff; induction (elements m);
          simpl in *.
          * inversion H.
          * case_eq (f (fst a) (snd a)); intros; rewrite H0 in H.
            inversion H; subst.
            constructor; eauto.
            constructor 2; eauto.
            constructor 2; eauto.
        + induction (elements m); simpl in *.
          * inversion H.
          * case_eq (f (fst a) (snd a)); intros; rewrite H0 in H; eauto.
            inversion H; subst.
            destruct H2; rewrite Proper_f in H0; eauto.
            eauto.
    Qed.

    Lemma Permutation_Partition_App {Value}:
      forall (m m1 m2 : t Value),
        Partition m m1 m2 ->
        Permutation (Values m) (Values m1 ++ Values m2).
    Proof.
      unfold Partition; intros; intuition.
      unfold Values; rewrite <- List.map_app.
      eapply Permutation_InA_cons; eauto using elements_3w.
      eapply NoDupA_app; eauto using elements_3w, equiv_eq_key.
      intros; destruct x as [k v]; eapply (H0 k).
      apply InA_alt in H; destruct H; apply InA_alt in H2; destruct H2;
      intuition; unfold eq_key in *; simpl in *.
      destruct x; simpl in *; rewrite H3; econstructor;
      apply elements_2; eauto; apply In_InA; eauto using equiv_eq_key_elt.
      destruct x0; simpl in *; rewrite H; econstructor;
      apply elements_2; eauto; apply In_InA; eauto using equiv_eq_key_elt.
      intros; rewrite InA_app_iff by eauto using equiv_eq_key_elt;
      intuition.
      apply elements_2 in H; rewrite H1 in H; intuition;
      eauto using elements_1.
      apply elements_1; rewrite H1; eauto using elements_2.
      apply elements_1; rewrite H1; eauto using elements_2.
    Qed.

    Corollary Permutation_partition {Value}:
      forall f (m : t Value),
        (Proper (E.eq ==> eq ==> eq) f)
        -> Permutation (Values m)
                       (Values (fst (partition f m)) ++ Values (snd (partition f m))).
    Proof.
      intros; eauto using Permutation_Partition_App,
              partition_Partition_simple.
    Qed.

    Lemma map_add {A B}:
      forall (f : A -> B) m k v,
        Equal (map f (add k v m))
              (add k (f v) (map f m)).
    Proof.
      unfold Equal; intros; case_eq (find y (add k (f v) (map f m)));
      case_eq (find y (map f (add k v m))); intros; eauto.
      - rewrite <- find_mapsto_iff in H, H0.
        rewrite map_mapsto_iff in H; destruct H as [a [b_eq In_b]]; subst.
        rewrite add_mapsto_iff in H0, In_b; intuition; subst; eauto.
        rewrite map_mapsto_iff in H3; destruct H3 as [a' [b_eq' In_b']]; subst.
        rewrite find_mapsto_iff in In_b', H2; congruence.
      - rewrite <- find_mapsto_iff in H0.
        rewrite <- not_find_in_iff in H; exfalso; apply H.
        rewrite add_mapsto_iff in H0; intuition; subst; eauto.
        rewrite H0, map_in_iff, add_in_iff; eauto.
        rewrite map_mapsto_iff in H2; destruct H2 as [a [b_eq In_b]]; subst.
        rewrite map_in_iff, add_in_iff; right; econstructor; eauto.
      - rewrite <- find_mapsto_iff in H.
        rewrite <- not_find_in_iff in H0; exfalso; apply H0.
        rewrite map_mapsto_iff in H; destruct H as [a [b_eq In_b]]; subst.
        rewrite add_mapsto_iff in In_b; intuition; subst; eauto.
        rewrite H1, add_in_iff; eauto.
        rewrite add_in_iff, map_in_iff; right; econstructor; eauto.
    Qed.

    Lemma Equal_elements {A} :
      forall m1 m2,
        Equal m1 m2
        -> forall k (a : A), (InA (@eq_key_elt _) (k, a) (elements m1)
                              <-> InA (@eq_key_elt _) (k, a) (elements m2)).
    Proof.
      unfold Equal; split; intros;
      rewrite <- elements_mapsto_iff, find_mapsto_iff in H0;
      rewrite <- elements_mapsto_iff, find_mapsto_iff; congruence.
    Qed.

    Add Parametric Morphism {A} :
      (@Values A)
        with signature (Equal ==> @Permutation A)
          as Permutation_Equal_Values.
    Proof.
      intros; unfold Values.
      eapply Permutation_InA_cons; eauto using elements_3w, Equal_elements.
    Qed.

    Lemma elements_in_iff' :
      forall (elt : Type) (m : t elt) x,
        In x m <->
        exists v, InA (eq_key (elt:=elt)) (x, v) (elements m) .
    Proof.
      split; rewrite elements_in_iff; intros.
      destruct H; induction H.
      destruct H; eexists x0; econstructor; eauto.
      destruct IHInA; econstructor; econstructor 2; eassumption.
      destruct H; induction H.
      eexists; repeat econstructor; simpl; eauto.
      destruct IHInA; eexists; econstructor 2; eauto.
    Qed.

    Corollary elements_in_if' :
      forall (elt : Type) (m : t elt) x v,
        InA (eq_key (elt:=elt)) (x, v) (elements m) ->
        In x m.
    Proof.
      intros; eapply elements_in_iff'; eauto.
    Qed.

    Lemma consist'' :
        forall (container: IndexedBag) key search_term,
          Permutation
            (Values
               (map
                  (fun x : BagType =>
                     List.filter
                       (fun a : TItem =>
                          negb (KeyFilter key a && bfind_matcher search_term a))
                       (benumerate x)) (ifmap container)))
            (Values
               (map benumerate
                    (snd (partition (KeyBasedPartitioningFunction _ key) (ifmap container))))
               ++ (Values
                     (map
                        (fun x : BagType =>
                           List.filter
                             (fun a : TItem =>
                                negb (bfind_matcher search_term a))
                             (benumerate x))
                        (fst (partition (KeyBasedPartitioningFunction _ key) (ifmap container)))))).
    Proof.
      unfold Values; intros; rewrite <- List.map_app.
      eapply Permutation_InA_cons; eauto using elements_3w.
      - eapply NoDupA_app; eauto using elements_3w, equiv_eq_key; intros.
        unfold eq_key in H.
        destruct x.
        apply elements_in_if' in H.
        apply elements_in_if' in H0.
        rewrite map_in_iff in H, H0.
        apply In_KeyBasedPartition_snd in H.
        apply In_KeyBasedPartition_fst in H0.
        congruence.
      - intros; rewrite InA_app_iff by eauto using equiv_eq_key_elt.
        repeat rewrite <- elements_mapsto_iff; repeat rewrite map_mapsto_iff.
        intuition.
        destruct H as [a [? In_k]]; subst.
        destruct (E.eq_dec key0 k); [ right | left ].
        + eexists a.
          rewrite <- e in *.
          rewrite KeyBasedPartition_fst_singleton; eauto; split.
          generalize (iconsistency _ _ _ In_k);
            induction (benumerate a); simpl; intros; eauto.
          case_eq (KeyFilter key0 a0); intros; simpl.
          case_eq (bfind_matcher search_term a0); intros; simpl;
          rewrite IHl; eauto.
          apply KeyFilter_false in H0; exfalso; eauto.
          eapply add_1; reflexivity.
        + eexists a; split.
          generalize (iconsistency _ _ _ In_k);
          induction (benumerate a); intros; simpl; eauto.
          case_eq (KeyFilter key0 a0); simpl; rewrite IHl; eauto.
          intros Filter_key0; apply KeyFilter_true in Filter_key0.
          exfalso; apply n; rewrite <- Filter_key0, H; eauto.
          simpl in *; constructor; eauto.
          simpl in *; intros; eapply H; eauto.
          simpl in *; intros; eapply H; eauto.
          rewrite partition_iff_2 with (f := KeyBasedPartitioningFunction _ key0);
            eauto using KeyBasedPartitioningFunction_Proper.
          intuition; eapply KeyBasedPartitioningFunction_eq_false; eassumption.
        + destruct H0 as [a [? MapsTo_k]]; subst.
          pose proof (MapsTo_KeyBasedPartition_snd _ _ _ _ MapsTo_k).
          rewrite partition_iff_2 with (f := KeyBasedPartitioningFunction _ key0) in MapsTo_k;
            eauto using KeyBasedPartitioningFunction_Proper.
          exists a; intuition.
          generalize (iconsistency _ _ _ H0).
          induction (benumerate a); simpl; intros; eauto.
          case_eq (KeyFilter key0 a0); simpl; rewrite <- IHl; eauto.
          intros Filter_key0; apply KeyFilter_true in Filter_key0.
          exfalso; apply H; rewrite <- Filter_key0; eapply H2; eauto.
        + destruct H0 as [a [? MapsTo_k]]; subst.
          pose proof (MapsTo_KeyBasedPartition_fst _ _ _ _ MapsTo_k).
          rewrite partition_iff_1 with (f := KeyBasedPartitioningFunction _ key0) in MapsTo_k;
            eauto using KeyBasedPartitioningFunction_Proper.
          exists a; intuition.
          generalize (iconsistency _ _ _ H0).
          induction (benumerate a); simpl; intros; eauto.
          case_eq (KeyFilter key0 a0); simpl; rewrite <- IHl; eauto.
          intros Filter_key0; apply KeyFilter_false in Filter_key0.
          exfalso; apply Filter_key0; rewrite H, H2; eauto.
    Qed.

    Lemma Permutation_map_enumerate
    : forall key m,
        Permutation
          (Values
             (snd
                (partition (KeyBasedPartitioningFunction (list TItem) key)
                           (map benumerate m))))
          (Values
             (map benumerate
                  (snd
                     (partition (KeyBasedPartitioningFunction BagType key)
                                m)))).
    Proof.
      intros; eapply Permutation_InA_cons; eauto using elements_3w.
      intros; repeat rewrite <- elements_mapsto_iff; split.
      - intros; pose proof (MapsTo_KeyBasedPartition_snd _ _ _ _ H).
        rewrite map_mapsto_iff.
        rewrite partition_iff_2 with (f := KeyBasedPartitioningFunction _ key0) in H;
          eauto using KeyBasedPartitioningFunction_Proper; intuition.
        rewrite map_mapsto_iff in H1; destruct H1 as [bag [? In_k]]; subst;
        eexists; split; eauto.
        rewrite partition_iff_2 with (f := KeyBasedPartitioningFunction _ key0);
          eauto using KeyBasedPartitioningFunction_Proper; intuition.
      - intros.
        rewrite map_mapsto_iff in H.
        destruct H as [bag [? In_k]]; subst.
        rewrite partition_iff_2 with (f := KeyBasedPartitioningFunction _ key0) in In_k;
          eauto using KeyBasedPartitioningFunction_Proper; intuition.
        rewrite partition_iff_2 with (f := KeyBasedPartitioningFunction _ key0);
          eauto using KeyBasedPartitioningFunction_Proper; intuition.
    Qed.

    Lemma Permutation_map_filter_negb
    : forall key m,
        Permutation
          (Values
             (map benumerate
                  (filter
                     (fun (k : M.key) (e : BagType) =>
                      negb (KeyBasedPartitioningFunction BagType key k e))
                     m)))
          (Values
             (filter
                (fun (k : M.key) (e : _) =>
                   negb (KeyBasedPartitioningFunction _ key k e))
                (map benumerate m))).
    Proof.
      intros; eapply Permutation_InA_cons; eauto using elements_3w.
      intros; repeat rewrite <- elements_mapsto_iff;
      rewrite filter_iff; repeat rewrite map_mapsto_iff; intuition;
      eauto using negb_KeyBasedPartitioningFunction_Proper.
      - destruct H as [bag [? In_k]]; subst; rewrite filter_iff in In_k;
        intuition; eauto using negb_KeyBasedPartitioningFunction_Proper.
      - destruct H as [bag [? In_k]]; subst; rewrite filter_iff in In_k;
        intuition; eauto using negb_KeyBasedPartitioningFunction_Proper.
      - destruct H0 as [bag [? In_k]]; subst.
        eexists; split; eauto; rewrite filter_iff;
        intuition; eauto using negb_KeyBasedPartitioningFunction_Proper.
    Qed.

    Lemma Permutation_map_filter
    : forall key m,
        Permutation
          (Values
             (map benumerate
                  (filter (KeyBasedPartitioningFunction BagType key) m)))
          (Values
             (filter
                (fun (k : M.key) (e : _) =>
                   KeyBasedPartitioningFunction _ key k e)
                (map benumerate m))).
    Proof.
      intros; eapply Permutation_InA_cons; eauto using elements_3w.
      intros; repeat rewrite <- elements_mapsto_iff;
      rewrite filter_iff; repeat rewrite map_mapsto_iff; intuition;
      eauto using KeyBasedPartitioningFunction_Proper.
      - destruct H as [bag [? In_k]]; subst; rewrite filter_iff in In_k;
        intuition; eauto using KeyBasedPartitioningFunction_Proper.
      - destruct H as [bag [? In_k]]; subst; rewrite filter_iff in In_k;
        intuition; eauto using KeyBasedPartitioningFunction_Proper.
      - destruct H0 as [bag [? In_k]]; subst.
        eexists; split; eauto; rewrite filter_iff;
        intuition; eauto using KeyBasedPartitioningFunction_Proper.
    Qed.

    Lemma Permuation_filter_flatten {A B}
    : forall (f : B -> bool) f' l,
        Permutation (flatten (List.map (fun x : A => List.filter f (f' x)) l))
                    (List.filter f (flatten (List.map f' l))).
    Proof.
      induction l; simpl.
      constructor.
      rewrite filter_app, IHl; reflexivity.
    Qed.

    Lemma IndexedTree_RepInv'
    : forall container k b, InA (@eq_key_elt _) (k, b) (elements (ifmap container))
                            -> forall item : TItem,
                                 List.In item (benumerate b) -> E.eq (projection item) k.
    Proof.
      intros; eapply iconsistency; eauto; eapply elements_mapsto_iff; eauto.
    Qed.

    Lemma consist4 :
        forall (container: IndexedBag) key,
          Permutation
            (flatten (Values (filter
                                (KeyBasedPartitioningFunction (list TItem) key)
                                (map benumerate (ifmap container)))))
            match find key (ifmap container) with
                       | Some bag => benumerate bag
                       | None => nil
             end.
    Proof.
      intros; rewrite <- consist.
      rewrite <- Permutation_map_filter.
      rewrite <- Permutation_map_Values.
      rewrite Permutation_filter_Values;
        eauto using KeyBasedPartitioningFunction_Proper.
      unfold Values.
      pose proof (IndexedTree_RepInv' container).
      induction (elements (ifmap container)); simpl.
      constructor.
      case_eq (KeyBasedPartitioningFunction BagType key0 (fst a) (snd a)); simpl;
      rewrite IHl; intros.
      - apply Permutation_app; try reflexivity.
        apply KeyBasedPartitioningFunction_eq_true in H0.
        rewrite filter_all_true; eauto.
        intros; eapply KeyFilter_true; eapply H; eauto.
        repeat econstructor; eauto.
      - eapply H; eauto.
      - apply KeyBasedPartitioningFunction_eq_false in H0.
        rewrite filter_all_false; eauto.
        intros; eapply KeyFilter_false.
        unfold not; intros; apply H0; rewrite <- H2; eapply H;
        eauto; repeat econstructor; reflexivity.
      - eapply H; eauto.
    Qed.

    Lemma partition_app {A} :
      forall f (l1 l2 : list A),
        List.partition f (l1 ++ l2) =
        (fst (List.partition f l1) ++ fst (List.partition f l2),
         snd (List.partition f l1) ++ snd (List.partition f l2)).
    Proof.
      induction l1; simpl.
      - intros; destruct (List.partition f l2); reflexivity.
      - intros; rewrite IHl1; destruct (f a); destruct (List.partition f l1);
        simpl; f_equal.
    Qed.

    Lemma fold_left_fst_partition :
      forall search_term l l' l'',
        Permutation l''
                    (fst
                       (List.partition (fun item : TItem => bfind_matcher search_term item)
                                       l'))
        -> Permutation
             (fold_left
                (fun (a : list TItem) (p : key * BagType) =>
                   fst (bdelete (snd p) search_term) ++ a) l l'')
          (fst
             (List.partition (fun item : TItem => bfind_matcher search_term item)
                             (l' ++ (flatten
                                      ((List.map benumerate (List.map snd l))))))).
    Proof.
      induction l; simpl; intros.
      rewrite app_nil_r; eauto.
      rewrite app_assoc.
      rewrite <- IHl; f_equiv.
      rewrite H, partition_app; simpl.
      rewrite Permutation_app_comm; f_equiv.
      apply bdelete_correct.
    Qed.

    Lemma IndexedBag_BagDeleteCorrect :
      BagDeleteCorrect IndexedBag_bfind IndexedBag_bfind_matcher
        IndexedBag_benumerate IndexedBag_bdelete.
    Proof.

      destruct search_term as [option_key search_term];
      destruct option_key as [ key | ]; simpl.

      (* Key provided *)

      - unfold IndexedBag_benumerate, IndexedBag_bfind_matcher; simpl.
        rewrite snd_bdelete_eq_bdelete', fst_bdelete_eq_bdelete';
          unfold IndexedBag_bdelete'; simpl.
        case_eq (find key (ifmap container)); simpl; split.
        + rewrite partition_filter_neq.
          repeat rewrite <- flat_map_flatten;
            rewrite filter_flat_map; repeat rewrite flat_map_flatten.
          pose proof (bdelete_correct b search_term); intuition.
          repeat rewrite Permutation_map_Values.
          destruct (bdelete b search_term); simpl in *.
          erewrite map_add.

          rewrite Permutation_Partition_App by
              eapply partition_after_KeyBasedPartition_and_add.
          rewrite KeyBasedPartition_fst_singleton by
              (rewrite map_mapsto_iff; eexists; rewrite find_mapsto_iff;
               split; eauto).
          rewrite multiple_adds.
          rewrite (values_add_not_in (empty _))
                  by (unfold not; intros; eapply empty_in_iff; eassumption).
          rewrite consist''.
          rewrite Permutation_app_comm.
          rewrite Values_empty; simpl.
          repeat rewrite flatten_app; simpl; rewrite H1.
          rewrite Permutation_app; eauto.
          * rewrite Permutation_map_filter_negb; repeat rewrite consist'; reflexivity.
          * rewrite app_nil_r, <- Permutation_map_Values,
            Permuation_filter_flatten, Permutation_map_Values,
            Permutation_map_filter, consist4, H.
            rewrite partition_filter_neq; reflexivity.
        + pose proof (bdelete_correct b search_term); intuition.
          destruct (bdelete b search_term); simpl in *.
          rewrite H2, partition_filter_eq, partition_filter_eq.
          rewrite filter_and', flatten_filter, consist, H; reflexivity.
        + rewrite partition_filter_neq, flatten_filter.
          unfold Values.
          pose proof (IndexedTree_RepInv' container).
          rewrite <- not_find_in_iff in H.
          rewrite elements_in_iff in H.
          induction (elements (ifmap container)); simpl.
          * constructor.
          * rewrite IHl.
            apply Permutation_app; eauto.
            assert (forall item : TItem,
                      List.In item (benumerate (snd a)) -> E.eq (projection item) (fst a))
              by (intros; eapply H0; eauto; repeat constructor; reflexivity).
            assert (~ E.eq key (fst a))
              by (unfold not; intros; apply H; eexists; repeat econstructor; eauto).
            revert H1 H2.
            clear; induction (benumerate (snd a)); simpl; intros.
            constructor.
            case_eq (KeyFilter key a0); simpl.
            intros; apply KeyFilter_true in H; rewrite <- H in H2.
            exfalso; apply H2; apply H1; eauto.
            rewrite <- IHl; eauto.
            unfold not; intros H1; apply H; destruct H1;
            econstructor; constructor 2; eauto.
            intros; eapply H0; eauto.
        + rewrite partition_filter_eq, flatten_filter.
          unfold Values.
          pose proof (IndexedTree_RepInv' container).
          rewrite <- not_find_in_iff in H.
          rewrite elements_in_iff in H.
          induction (elements (ifmap container)); simpl.
          * constructor.
          * rewrite <- IHl.
            assert (forall item : TItem,
                      List.In item (benumerate (snd a)) -> E.eq (projection item) (fst a))
              by (intros; eapply H0; eauto; repeat constructor; reflexivity).
            assert (~ E.eq key (fst a))
              by (unfold not; intros; apply H; eexists; repeat econstructor; eauto).
            revert H1 H2.
            clear; induction (benumerate (snd a)); simpl; intros.
            constructor.
            case_eq (KeyFilter key a0); simpl.
            intros; apply KeyFilter_true in H; rewrite <- H in H2.
            exfalso; apply H2; apply H1; eauto.
            rewrite <- IHl; eauto.
            unfold not; intros H1; apply H; destruct H1;
            econstructor; constructor 2; eauto.
            intros; eapply H0; eauto.
      - unfold IndexedBag_benumerate, IndexedBag_bfind_matcher; simpl.
        rewrite snd_bdelete_eq_bdelete', fst_bdelete_eq_bdelete';
          unfold IndexedBag_bdelete'; simpl.
        rewrite fold_pair; unfold Values; simpl; intuition.
        + rewrite !FMap_Insert_fold_add, elements_empty, app_nil_r by
              eauto using empty_In.
          rewrite !List.map_map; simpl.
          induction elements; simpl;
          [ constructor
          | rewrite IHl, partition_app; simpl; f_equiv;
              eapply bdelete_correct ].
        + rewrite fold_1, fold_left_fst_partition with (l' := []);
          reflexivity.
    Qed.

    Lemma IndexedBag_BagUpdateCorrect :
      BagUpdateCorrect IndexedBag_bfind IndexedBag_bfind_matcher
        IndexedBag_benumerate bupdate_transform IndexedBag_bupdate.
    Proof.

      destruct search_term as [option_key search_term];
      destruct option_key as [ key | ];
      unfold IndexedBag_benumerate, IndexedBag_bfind_matcher; simpl.

      (* Key provided *)

      - case_eq (find key (ifmap container)); simpl; intros.

        + rewrite partition_filter_neq.
          repeat rewrite <- flat_map_flatten;
            rewrite filter_flat_map; repeat rewrite flat_map_flatten.
          pose proof (bupdate_correct b search_term); intuition.
          repeat rewrite Permutation_map_Values.
          erewrite map_add.

          rewrite Permutation_Partition_App by
              eapply partition_after_KeyBasedPartition_and_add.
          rewrite KeyBasedPartition_fst_singleton by
              (rewrite map_mapsto_iff; eexists; rewrite find_mapsto_iff;
               split; eauto).
          rewrite multiple_adds.
          rewrite (values_add_not_in (empty _))
                  by (unfold not; intros; eapply empty_in_iff; eassumption).
          rewrite consist''.
          rewrite Permutation_app_comm.
          rewrite Values_empty; simpl.
          repeat rewrite flatten_app; simpl; rewrite H0.
          rewrite app_nil_r, !app_assoc, Permutation_app; eauto.
          * rewrite Permutation_map_filter_negb; rewrite consist'; f_equiv.
            rewrite <- Permutation_map_Values,
            Permuation_filter_flatten, Permutation_map_Values,
            Permutation_map_filter, consist4, H.
            rewrite partition_filter_neq; reflexivity.
          *  rewrite partition_filter_eq, partition_filter_eq.
             rewrite filter_and', flatten_filter, consist, H; reflexivity.
        + rewrite partition_filter_neq, flatten_filter,
          partition_filter_eq, filter_and', flatten_filter,
          consist, H; simpl; rewrite app_nil_r.
          pose proof (IndexedTree_RepInv' container).
          rewrite <- not_find_in_iff in H.
          rewrite elements_in_iff in H.
          unfold Values; induction (elements (ifmap container)); simpl.
          * constructor.
          * rewrite <- IHl; f_equiv.
            assert (forall item : TItem,
                      List.In item (benumerate (snd a)) -> E.eq (projection item) (fst a))
              by (intros; eapply H0; eauto; repeat constructor; reflexivity).
            assert (~ E.eq key (fst a))
              by (unfold not; intros; apply H; eexists; repeat econstructor; eauto).
            revert H1 H2.
            clear; induction (benumerate (snd a)); simpl; intros.
            constructor.
            case_eq (KeyFilter key a0); simpl.
            intros; apply KeyFilter_true in H; rewrite <- H in H2.
            exfalso; apply H2; apply H1; eauto.
            rewrite <- IHl; eauto.
            unfold not; intros H1; apply H; destruct H1;
            econstructor; constructor 2; eauto.
            intros; eapply H0; eauto.
      - intros; rewrite <- !Permutation_map_Values.
        induction (Values (ifmap container)); simpl.
        + constructor.
        + rewrite IHl, partition_app; simpl.
          rewrite Permutation_app by eauto using bupdate_correct.
          rewrite <- !app_assoc.
          apply Permutation_app;
            [f_equiv
             | rewrite Permutation_app_comm, <- app_assoc].
          apply Permutation_app;
            [f_equiv
            | rewrite Permutation_app_comm, map_app; f_equiv].
    Qed.

  End TreeBagDefinitions.

  Print IndexedBag.

  Instance IndexedBagAsBag
           {TItem : Type}
           (TBag : Bag TItem)
           projection
  : Bag TItem :=
    {| BagType := IndexedBag TBag projection;
       SearchTermType := prod (option TKey) (SearchTermType);
       UpdateTermType := UpdateTermType;

       bempty            := IndexedBag_bempty TBag projection;
       bstar             := IndexedBag_bstar TBag;
       bid               := bid;
       bfind_matcher     := IndexedBag_bfind_matcher TBag projection ;
       bupdate_transform := bupdate_transform;

       benumerate := IndexedBag_benumerate TBag projection;
       bfind      := IndexedBag_bfind TBag projection;
       binsert    := IndexedBag_binsert TBag projection;
       bcount     := IndexedBag_bcount BagProof projection;
       bdelete    := IndexedBag_bdelete BagProof projection;
       bupdate    := IndexedBag_bupdate BagProof projection key_preserving_Update |}.

                 binsert_enumerate := IndexedBag_BagInsertEnumerate BagProof projection;
                 benumerate_empty  := IndexedBag_BagEnumerateEmpty BagProof projection;
                 bfind_star        := IndexedBag_BagFindStar BagProof projection;
                 bfind_correct     := IndexedBag_BagFindCorrect BagProof projection;
                 bcount_correct    := IndexedBag_BagCountCorrect BagProof projection;
                 bdelete_correct   := IndexedBag_BagDeleteCorrect BagProof projection;
                 bupdate_correct   := IndexedBag_BagUpdateCorrect BagProof projection key_preserving_Update  |}

         |}.

           (key_preserving_Update :
              forall K item updateTerm,
                E.eq (projection item) K
                -> E.eq (projection (bupdate_transform updateTerm item)) K )


End TreeBag.
