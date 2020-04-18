(* Print LoadPath. *)

Require Export Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsInterface
        Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsProperties.
Require Import
        Coq.FSets.FMapInterface Coq.FSets.FMapFacts
        Fiat.Common
        Fiat.Common.List.ListFacts
        Fiat.Common.List.FlattenList
        Fiat.Common.SetEqProperties
        Fiat.Common.FMapExtensions
        Fiat.Common.List.PermutationFacts.

Unset Implicit Arguments.

Module TreeBag (Import M: WS).
  Module Import BasicFacts := WFacts_fun E M.
  Module Import BasicProperties := WProperties_fun E M.
  Module Import MoreFacts := FMapExtensions_fun E M.

  Definition TKey := key.

  Section TreeBagDefinitions.

    Context {BagType TItem SearchTermType UpdateTermType : Type}
            (TBag : Bag BagType TItem SearchTermType UpdateTermType)
            (RepInv : BagType -> Prop)
            (ValidUpdate : UpdateTermType -> Prop)
            (TBagCorrect : CorrectBag RepInv ValidUpdate TBag)
            (projection: TItem -> TKey).

    Definition IndexedBag := t BagType.

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

    Definition IndexedBag_bfind_matcher
               (key_searchterm: (option TKey) * SearchTermType) (item: TItem) :=
      match fst key_searchterm with
        | Some k => KeyFilter k item
        | None   => true
      end && (bfind_matcher (snd key_searchterm) item).

    Definition IndexedBag_benumerate
               (container: IndexedBag) :=
      flatten (List.map benumerate (Values container)).

    Definition IndexedBag_bfind
               (container: IndexedBag)
               (key_searchterm: (option TKey) * SearchTermType) :=
          match fst key_searchterm with
            | Some k =>
              match find k container with
                | Some bag => bfind (Bag := TBag) bag (snd key_searchterm)
                | None     => nil
              end
            | None   =>
              flatten (List.map (fun bag : BagType => bfind bag (snd key_searchterm)) (Values container))
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
      match fst key_searchterm with
        | Some k =>
          match find k container with
            | Some bag => bcount bag (snd key_searchterm)
            | None     => 0
          end
        | None   =>
          fold (fun _ bag acc => acc + bcount bag (snd key_searchterm))
               container 0
      end.

    Definition IndexedBag_bdelete
               (container: IndexedBag)
               (key_searchterm: (option TKey) * SearchTermType)
    : (list TItem) * IndexedBag :=
      match fst (key_searchterm) with
        | Some k => match find k container with
                      | Some bag =>
                        let (d,r) := bdelete bag (snd key_searchterm) in
                        (d, add k r container)
                      | None => (nil, container)
                    end
        | None => fold (fun k bag (res : (list TItem) * (t BagType)) =>
                          match bdelete bag (snd key_searchterm) with
                            | (d, r) => let (d', r') := res in
                                        (d ++ d', add k r r')
                          end) (container) ([], empty BagType)
      end.

    Definition IndexedBag_bupdate
               (container: IndexedBag)
               (key_searchterm: (option TKey) * SearchTermType)
               (updateTerm : UpdateTermType)
    : (list TItem) * IndexedBag :=
      let (key_option, search_term) := key_searchterm in
      match key_option with
        | Some k => match find k container with
                      | Some bag =>
                        let (d,r) := bupdate bag search_term updateTerm in
                        (d, add k r container)
                      | None => (nil, container)
                    end
        | None => fold (fun k bag (res : (list TItem) * (t BagType)) =>
                          match bupdate bag search_term updateTerm with
                            | (d, r) => let (d', r') := res in
                                        (d ++ d', add k r r')
                          end) (container) ([], empty BagType)
      end.

    Definition IndexedBag_RepInv (fmap : IndexedBag) :=
      forall (key: TKey) (bag: BagType),
        MapsTo key bag fmap ->
        (RepInv bag) /\
        forall (item: TItem),
          List.In item (benumerate bag) ->
          E.eq (projection item) key.

    Definition IndexedBag_ValidUpdate (update_term : UpdateTermType) :=
      ValidUpdate update_term /\
      forall K item,
        E.eq (projection item) K
        -> E.eq (projection (bupdate_transform update_term item)) K.

    Lemma IndexedBag_Empty_RepInv :
      IndexedBag_RepInv (empty BagType).
    Proof.
      unfold IndexedBag_RepInv;
      intros; rewrite empty_mapsto_iff in *; exfalso; trivial.
    Qed.

    Lemma consistency_key_eq :
      forall (container : IndexedBag)
        (key: TKey) bag item,
        IndexedBag_RepInv container ->
        MapsTo key bag container ->
        List.In item (benumerate bag) ->
        E.eq (projection item) key.
    Proof.
      intros; unfold IndexedBag_RepInv in *; eauto.
      eapply H; eauto.
    Qed.

    Lemma IndexedBag_binsert_Preserves_RepInv :
      binsert_Preserves_RepInv IndexedBag_RepInv IndexedBag_binsert.
    Proof.
      unfold binsert_Preserves_RepInv, IndexedBag_RepInv.
      intros ? item' ? k' bag' maps_to.
      unfold IndexedBag_binsert in maps_to.
      rewrite add_mapsto_iff in maps_to;
        destruct maps_to as [(is_eq & refreshed) | (neq & maps_to)];
        subst; intuition; intros.
      - destruct (FindWithDefault_dec (projection item') bempty container)
          as [ [bag' (mapsto & equality)] | (not_found & equality) ];
        rewrite equality in *; eauto using binsert_RepInv.
        eapply binsert_RepInv; eapply containerCorrect; eauto.
        eapply binsert_RepInv; eapply bempty_RepInv.
      - rewrite <- is_eq.
        rewrite binsert_enumerate_weak with (RepInv0 := RepInv) (ValidUpdate0 := ValidUpdate) in H; intuition; subst.

        destruct (FindWithDefault_dec (projection item') bempty container)
          as [ [bag' (mapsto & equality)] | (not_found & equality) ];
        rewrite equality in *; clear equality.
        eapply containerCorrect; eauto.
        rewrite benumerate_empty_eq_nil with (RepInv0 := RepInv) (ValidUpdate0 := ValidUpdate) in H0;
          simpl in H0; intuition.
        reflexivity.
        destruct (FindWithDefault_dec (projection item') bempty container)
          as [ [bag' (mapsto & equality)] | (not_found & equality) ];
        rewrite equality in *; clear equality; eauto.
        + eapply containerCorrect; eauto.
        + apply bempty_RepInv.
      - eapply containerCorrect; eauto.
      - eapply containerCorrect; eauto.
    Qed.

    Lemma IndexedBag_bdelete_Preserves_RepInv :
      bdelete_Preserves_RepInv IndexedBag_RepInv IndexedBag_bdelete.
    Proof.
      unfold bdelete_Preserves_RepInv, IndexedBag_RepInv,
      IndexedBag_bdelete.
      intros; destruct search_term; destruct o; simpl in *;
      unfold IndexedBag_RepInv; intros.
      - case_eq (find t0 container); intros; rewrite H0 in *.
        + case_eq (bdelete b s); intros; rewrite H1 in *; simpl in *.
          assert (RepInv b)
            as WF_b by (eapply containerCorrect; rewrite find_mapsto_iff; eassumption).
          rewrite add_mapsto_iff in H; intuition; subst.
          pose proof (bdelete_RepInv b s) as RepInv_H1; rewrite H1 in RepInv_H1;
          apply RepInv_H1; eauto.
          * pose proof (bdelete_correct b s WF_b); subst; rewrite H1 in *;
            simpl in *; intuition.
            apply find_2 in H0; rewrite <- H.
            eapply containerCorrect; eauto.
            eapply In_partition; eauto using Permutation_in, In_partition.
          * eapply containerCorrect; eauto.
          * eapply containerCorrect; eauto.
        + intuition; eapply containerCorrect; eauto.
      - rewrite fold_pair in H; simpl in H.
        rewrite FMap_Insert_fold_add_map_eq in H.
        rewrite map_mapsto_iff in H; destruct_ex; intuition; subst;
        assert (RepInv x) as WF_x by (eapply containerCorrect; eauto).
        eapply (bdelete_RepInv x s WF_x).
        destruct (bdelete_correct x s WF_x).
        eapply containerCorrect; eauto.
        eapply In_partition; right; eapply Permutation_in; eauto.
    Defined.

    Lemma IndexedBag_bupdate_Preserves_RepInv
    : bupdate_Preserves_RepInv IndexedBag_RepInv IndexedBag_ValidUpdate IndexedBag_bupdate.
    Proof.
      unfold bupdate_Preserves_RepInv, IndexedBag_RepInv.
      intros; destruct search_term; destruct o; simpl in *.
      destruct valid_update as [valid_update valid_update'].
      - case_eq (find t0 container); intros; rewrite H0 in *.
        rewrite <- find_mapsto_iff in H0.
        assert (RepInv b) as WF_b by (eapply containerCorrect; eauto).
        case_eq (bupdate b s update_term); intros; rewrite H1 in *; simpl in *.
        pose proof (bupdate_RepInv b s update_term WF_b valid_update) as RepInv_H1.
        rewrite H1 in RepInv_H1.
        intuition.
        + rewrite add_mapsto_iff in H; intuition.
          unfold IndexedBag_ValidUpdate in *.
          rewrite <- H3; intuition.
          eapply containerCorrect; eauto.
        + rewrite add_mapsto_iff in H; intuition.
          pose proof (bupdate_correct b s update_term WF_b valid_update); simpl in *; intuition.
          rewrite <- H4 in H2.
          rewrite <- H; rewrite H1 in H5; simpl in *.
          pose proof (Permutation_in _ H5 H2);
            apply in_app_or in H3; destruct H3.
          * pose proof ((proj2 (In_partition _ _ _)) (or_intror H3));
            eapply containerCorrect; eauto.
          * apply in_map_iff in H3; destruct H3 as [item' [item'_eq In_item'] ].
            rewrite <- item'_eq in *.
            eapply valid_update'.
            eapply containerCorrect; eauto; eapply In_partition; eauto.
          * eapply containerCorrect; eauto.
        + eapply containerCorrect; eauto.
      - rewrite fold_pair in H; simpl in H.
        rewrite FMap_Insert_fold_add_map_eq in H.
        rewrite map_mapsto_iff in H;
        destruct H as [bag' [bag'_eq MapsTo_key0] ]; subst.
        assert (RepInv bag') as WF_bag' by (eapply containerCorrect; eauto).
        destruct valid_update as [valid_update valid_update'].
        pose proof (bupdate_correct bag' s update_term WF_bag' valid_update); intuition.
        apply bupdate_RepInv; eauto.
        pose proof (Permutation_in _ H0 H) as H4;
          apply in_app_or in H4; destruct H4.
        + pose proof ((proj2 (In_partition _ _ _)) (or_intror H2));
          eapply containerCorrect; eauto.
        + rewrite in_map_iff in H2; destruct H2 as [item' [item'_eq In_item'] ].
          rewrite <- item'_eq in *.
          eapply valid_update'.
          eapply containerCorrect; eauto; eapply In_partition; eauto.
    Defined.

    Lemma IndexedBag_BagInsertEnumerate :
      BagInsertEnumerate IndexedBag_RepInv IndexedBag_benumerate IndexedBag_binsert.
    Proof.
      unfold BagInsertEnumerate, IndexedBag_benumerate, IndexedBag_binsert.
      intros; simpl in *.

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
                    container) as part_add.

      pose proof (partition_Partition_simple
                    (BagType)
                    (KeyBasedPartitioningFunction BagType (projection inserted))
                    (KeyBasedPartitioningFunction_Proper _ _)
                    container) as part.

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

      eapply containerCorrect; eauto.
      (* New key *)

      rewrite <- not_find_in_iff in find_none.
      rewrite values_add_not_in by assumption.
      simpl.

      rewrite binsert_enumerate.
      rewrite benumerate_empty_eq_nil with (RepInv0 := RepInv) (ValidUpdate0 := ValidUpdate); eauto.
      apply bempty_RepInv.
    Qed.

    Lemma alt_IndexedBag_RepInv
    : forall container,
        IndexedBag_RepInv container
        -> forall (key0 : TKey) (bag : BagType),
                InA (@eq_key_elt _) (key0, bag) (elements container) ->
                RepInv bag /\
                (forall item : TItem,
                   List.In item (benumerate bag) ->
                   E.eq (projection item) key0).
    Proof.
      intros; eapply H; rewrite elements_mapsto_iff; eauto.
    Qed.

    Lemma IndexedBag_BagCountCorrect :
      BagCountCorrect IndexedBag_RepInv IndexedBag_bcount IndexedBag_bfind .
    Proof.
      unfold IndexedBag_RepInv, IndexedBag_bcount, IndexedBag_bfind, BagCountCorrect;
      simpl in *; intros; destruct search_term as [ [ key | ] search_term ]; simpl in *.
      + case_eq (find key container); simpl; eauto.
        intros; rewrite <- find_mapsto_iff in *;
        rewrite bcount_correct; eauto; eapply containerCorrect; eauto.
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
        unfold Values.

        pose proof (alt_IndexedBag_RepInv _ containerCorrect) as containerCorrect'.
        remember 0; clear Heqn;
        revert TBagCorrect n containerCorrect'; clear; induction (elements container);
        simpl; intros; eauto.
        rewrite IHl; intuition.
        f_equal.
        rewrite bcount_correct; auto with arith.
        destruct a; eapply containerCorrect'; simpl; eauto; repeat constructor.
        simpl; reflexivity.
        eapply containerCorrect'; constructor 2; eauto.
        eapply containerCorrect'; eauto; constructor 2; eauto.
    Qed.

    Lemma IndexedBag_BagEnumerateEmpty :
      BagEnumerateEmpty IndexedBag_benumerate IndexedBag_bempty.
    Proof.
      intros;
      unfold BagEnumerateEmpty, IndexedBag_benumerate, flatten; simpl.
      unfold IndexedBag_bempty; rewrite Values_empty; tauto.
    Qed.

    (* Enumerating the values for each key in an indexed bag [container]
       and filtering those values over a key [k] returns the same set of
       values as enumerating the values of the bag contained at index [k].
       (i.e. [iconsistency] gives us the property we expect.
     *)

    Lemma consist :
        forall
          (container: IndexedBag)
          (containerCorrect : IndexedBag_RepInv container),
        forall k,
          flatten
            (List.map (List.filter (KeyFilter k))
                      (List.map benumerate (Values container)))
          = match find k container with
              | Some bag => benumerate bag
              | None => nil
            end.
      Proof.
        unfold IndexedBag_RepInv; intros.

        unfold Values.
        destruct (find k container) as [ bag | ] eqn:eqfind.

        rewrite <- find_mapsto_iff in eqfind.
        (* assert (exists k', MapsTo k' bag (ifmap container)) as eqfind' by (exists k; trivial).*)

        pose proof eqfind as maps_to.

        rewrite elements_mapsto_iff in eqfind.
        apply InA_split in eqfind.

        destruct eqfind as [ l1 [ y [ l2 (y_k_bag & decomp) ] ] ].
        rewrite decomp.

        rewrite (map_map snd benumerate).
        rewrite ! map_app; simpl.

        pose proof (elements_3w container) as no_dup.
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

          pose proof (proj2 (containerCorrect _ _ in_app) _ in_bag'_items) as eq_k'.

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
          apply (containerCorrect _ bag); eauto.

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
        rewrite <- (proj2 (containerCorrect k' bag maps_to) _ in_subseq_prefilter) in maps_to.
        rewrite find_mapsto_iff in maps_to.

        congruence.
      Qed.

    Lemma consist' :
        forall (container: IndexedBag) key
               (containerCorrect : IndexedBag_RepInv container),
          Permutation
            (Values (filter
                       (fun (k : M.key) (e : list TItem) =>
                          negb (KeyBasedPartitioningFunction (list TItem) key k e))
                       (map benumerate container)))
            (Values (map benumerate (remove key container))).
    Proof.
      intros; eapply Permutation_InA_cons; eauto using elements_3w.
      intros.
      repeat rewrite <- elements_mapsto_iff.
      rewrite filter_iff.
      - intuition; intros.
        + rewrite map_mapsto_iff in H0; destruct H0 as [bag' [eq_bag' filter_k] ]; subst.
          rewrite map_mapsto_iff; eexists; split; eauto.
          rewrite remove_mapsto_iff; split; eauto.
          unfold not; intros.
          rewrite KeyBasedPartitioningFunction_eq_true in H;
            rewrite H in H1; discriminate.
        + rewrite map_mapsto_iff in H; destruct H as [bag' [eq_bag' filter_k] ]; subst.
          rewrite remove_mapsto_iff in filter_k; intuition.
        + rewrite map_mapsto_iff in H; destruct H as [bag' [eq_bag' filter_k] ]; subst.
          rewrite remove_mapsto_iff in filter_k; intuition.
          eapply KeyBasedPartitioningFunction_eq_false in H; rewrite H;
          reflexivity.
      - unfold Proper; compute; intros; subst; trivial.
        destruct (F.eq_dec x _), (F.eq_dec y _); rewrite H in *; intuition.
    Qed.

    Lemma IndexedBag_BagFindCorrect :
      BagFindCorrect IndexedBag_RepInv IndexedBag_bfind IndexedBag_bfind_matcher IndexedBag_benumerate.
    Proof.
      intros; hnf.
      destruct search_term as (option_key, search_term).
      destruct option_key as [ key | ].

      (* Key provided *)

      unfold IndexedBag_benumerate, IndexedBag_bfind,
      IndexedBag_bfind_matcher.
      unfold IndexedBag_RepInv; intros.

      rewrite filter_and.
      rewrite flatten_filter.

      simpl.
      rewrite consist.
      case_eq (M.find key container); intros.

      apply bfind_correct.
      eapply containerCorrect; rewrite find_mapsto_iff; eauto.
      eauto.

      unfold IndexedBag_RepInv; eauto.
      (* No key provided *)

      simpl. unfold IndexedBag_benumerate, IndexedBag_bfind_matcher,
             IndexedBag_RepInv, IndexedBag_bfind.
      rewrite flatten_filter; intros.

      pose proof (alt_IndexedBag_RepInv _ containerCorrect) as containerCorrect'.
      revert TBagCorrect containerCorrect'; clear.
      unfold Values; induction (elements container); simpl; eauto; intros.

      apply Permutation_app.
      apply (bfind_correct _).
      destruct a;  eapply containerCorrect'; repeat constructor; eauto.

      rewrite IHl; eauto.
    Qed.

    Lemma consist'' :
        forall (container: IndexedBag) key search_term
               (containerCorrect : IndexedBag_RepInv container),
          Permutation
            (Values
               (map
                  (fun x : BagType =>
                     List.filter
                       (fun a : TItem =>
                          negb (KeyFilter key a && bfind_matcher search_term a))
                       (benumerate x)) container))
            (Values
               (map benumerate
                    (snd (partition (KeyBasedPartitioningFunction _ key) container)))
               ++ (Values
                     (map
                        (fun x : BagType =>
                           List.filter
                             (fun a : TItem =>
                                negb (bfind_matcher (Bag := TBag) search_term a))
                             (benumerate x))
                        (fst (partition (KeyBasedPartitioningFunction _ key) container))))).
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
        destruct H as [a [? In_k] ]; subst.
        destruct (E.eq_dec key0 k); [ right | left ].
        + eexists a.
          rewrite <- e in *.
          rewrite KeyBasedPartition_fst_singleton; eauto; split.
          simpl; unfold IndexedBag_bfind_matcher; simpl.
          * generalize (proj2 (containerCorrect _ _ In_k));
            induction (benumerate a); simpl; intros; eauto.
            case_eq (KeyFilter key0 a0); intros; simpl.
            case_eq (bfind_matcher search_term a0); intros; simpl.
            rewrite IHl; eauto.
            rewrite IHl; eauto.
            apply KeyFilter_false in H0; exfalso; eauto.
          * generalize (proj2 (containerCorrect _ _ In_k));
            induction (benumerate a); simpl; intros; eauto.
            eapply add_1; reflexivity.
        + eexists a; split.
          generalize (proj2 (containerCorrect _ _ In_k));
          induction (benumerate a); intros; simpl; eauto.
          case_eq (KeyFilter key0 a0); simpl; try rewrite IHl; eauto.
          intros Filter_key0; apply KeyFilter_true in Filter_key0.
          exfalso; apply n; rewrite <- Filter_key0, H; eauto.
          simpl in *; constructor; eauto.
          intros; apply H; constructor 2; eauto.
          intros; apply H; constructor 2; eauto.
          rewrite partition_iff_2 with (f := KeyBasedPartitioningFunction _ key0);
            eauto using KeyBasedPartitioningFunction_Proper.
          intuition; eapply KeyBasedPartitioningFunction_eq_false; eassumption.
        + destruct H0 as [a [? MapsTo_k] ]; subst.
          pose proof (MapsTo_KeyBasedPartition_snd _ _ _ _ MapsTo_k).
          rewrite partition_iff_2 with (f := KeyBasedPartitioningFunction _ key0) in MapsTo_k;
            eauto using KeyBasedPartitioningFunction_Proper.
          exists a; intuition.
          generalize (proj2 (containerCorrect _ _  H0)).
          induction (benumerate a); simpl; intros; eauto.
          case_eq (KeyFilter key0 a0); simpl; try rewrite <- IHl; eauto.
          intros Filter_key0; apply KeyFilter_true in Filter_key0.
          exfalso; apply H; rewrite <- Filter_key0; eapply H2; eauto.
        + destruct H0 as [a [? MapsTo_k] ]; subst.
          pose proof (MapsTo_KeyBasedPartition_fst _ _ _ _ MapsTo_k).
          rewrite partition_iff_1 with (f := KeyBasedPartitioningFunction _ key0) in MapsTo_k;
            eauto using KeyBasedPartitioningFunction_Proper.
          simpl; unfold IndexedBag_bfind_matcher; simpl.
          exists a; intuition.
          generalize (proj2 (containerCorrect _ _ H0)).
          induction (benumerate a); simpl; intros; eauto.
          case_eq (KeyFilter key0 a0); simpl; eauto.
          intros Filter_key0; apply KeyFilter_true in Filter_key0.
          rewrite IHl; eauto.
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
        rewrite map_mapsto_iff in H1; destruct H1 as [bag [? In_k] ]; subst;
        eexists; split; eauto.
        rewrite partition_iff_2 with (f := KeyBasedPartitioningFunction _ key0);
          eauto using KeyBasedPartitioningFunction_Proper; intuition.
      - intros.
        rewrite map_mapsto_iff in H.
        destruct H as [bag [? In_k] ]; subst.
        rewrite partition_iff_2 with (f := KeyBasedPartitioningFunction _ key0) in In_k;
          eauto using KeyBasedPartitioningFunction_Proper; intuition.
        rewrite partition_iff_2 with (f := KeyBasedPartitioningFunction _ key0);
          eauto using KeyBasedPartitioningFunction_Proper; intuition.
    Qed.

    Lemma Permutation_map_filter_negb
    : forall key m,
        Permutation
          (Values
             (map (benumerate (Bag := TBag))
                  (filter
                     (fun (k : M.key) (e : BagType) =>
                      negb (KeyBasedPartitioningFunction BagType key k e))
                     m)))
          (Values
             (filter
                (fun (k : M.key) (e : _) =>
                   negb (KeyBasedPartitioningFunction _ key k e))
                (map (benumerate (Bag := TBag)) m))).
    Proof.
      intros; eapply Permutation_InA_cons; eauto using elements_3w.
      intros; repeat rewrite <- elements_mapsto_iff;
      rewrite filter_iff; repeat rewrite map_mapsto_iff; intuition;
      eauto using negb_KeyBasedPartitioningFunction_Proper.
      - destruct H as [bag [? In_k] ]; subst; rewrite filter_iff in In_k;
        intuition; eauto using negb_KeyBasedPartitioningFunction_Proper.
      - destruct H as [bag [? In_k] ]; subst; rewrite filter_iff in In_k;
        intuition; eauto using negb_KeyBasedPartitioningFunction_Proper.
      - destruct H0 as [bag [? In_k] ]; subst.
        eexists; split; eauto; rewrite filter_iff;
        intuition; eauto using negb_KeyBasedPartitioningFunction_Proper.
    Qed.

    Lemma Permutation_map_filter
    : forall key (m : IndexedBag),
        Permutation
          (Values
             (map benumerate
                  (filter (KeyBasedPartitioningFunction BagType key) m)))
          (Values
             (filter
                (KeyBasedPartitioningFunction _ key)
                (map benumerate m))).
    Proof.
      intros; eapply Permutation_InA_cons; eauto using elements_3w.
      intros; repeat rewrite <- elements_mapsto_iff;
      rewrite filter_iff; repeat rewrite map_mapsto_iff; intuition;
      eauto using KeyBasedPartitioningFunction_Proper.
      - destruct H as [bag [? In_k] ]; subst; rewrite filter_iff in In_k;
        intuition; eauto using KeyBasedPartitioningFunction_Proper.
      - destruct H as [bag [? In_k] ]; subst; rewrite filter_iff in In_k;
        intuition; eauto using KeyBasedPartitioningFunction_Proper.
      - destruct H0 as [bag [? In_k] ]; subst.
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

    Lemma consist4 :
       forall (container: IndexedBag) key
              (containerCorrect : IndexedBag_RepInv container),
          Permutation
            (flatten (Values (filter
                                (KeyBasedPartitioningFunction (list TItem) key)
                                (map benumerate container))))
            match find key container with
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
      pose proof (alt_IndexedBag_RepInv _ containerCorrect) as containerCorrect'.
      induction (elements container); simpl.
      constructor.
      case_eq (KeyBasedPartitioningFunction BagType key0 (fst a) (snd a)); simpl;
      rewrite IHl; intros.
      - apply Permutation_app; try reflexivity.
        apply KeyBasedPartitioningFunction_eq_true in H.
        rewrite filter_all_true; eauto.
        intros; eapply KeyFilter_true; eapply containerCorrect'; eauto.
        repeat econstructor; eauto.
      - intuition; eapply containerCorrect'; eauto.
      - apply KeyBasedPartitioningFunction_eq_false in H.
        rewrite filter_all_false; eauto.
        intros; eapply KeyFilter_false.
        unfold not; intros; apply H; rewrite <- H1; eapply containerCorrect';
        eauto; repeat econstructor; reflexivity.
      - intuition; eapply containerCorrect'; eauto.
      - eauto.
    Qed.

    Lemma fold_left_fst_partition :
      forall search_term l l' l'',
      (forall (key0 : TKey) (bag : BagType),
                InA (@eq_key_elt _) (key0, bag) l ->
                RepInv bag /\
                (forall item : TItem,
                   List.In item (benumerate bag) ->
                   E.eq (projection item) key0))
      -> Permutation l''
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
      intros; eapply H; constructor 2; eauto.
      rewrite H0, partition_app; simpl.
      rewrite Permutation_app_comm; f_equiv.
      apply bdelete_correct.
      destruct a; eapply H; repeat constructor; eauto.
    Qed.

    Lemma IndexedBag_BagDeleteCorrect :
      BagDeleteCorrect IndexedBag_RepInv IndexedBag_bfind IndexedBag_bfind_matcher
        IndexedBag_benumerate IndexedBag_bdelete.
    Proof.
      hnf.
      destruct search_term as [option_key search_term];
      destruct option_key as [ key | ]; simpl.

      (* Key provided *)

      - unfold IndexedBag_benumerate, IndexedBag_bfind_matcher,
        IndexedBag_bfind, IndexedBag_bdelete; simpl.
        case_eq (find key container); simpl; split.
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
          rewrite Permutation_app_comm.
          rewrite Values_empty; simpl.
          rewrite consist''.
          repeat rewrite flatten_app; simpl.
          apply Permutation_app.
          * rewrite Permutation_map_filter_negb; reflexivity.
          * rewrite app_nil_r, <- Permutation_map_Values,
            Permuation_filter_flatten, Permutation_map_Values,
            Permutation_map_filter, consist4.
            destruct H0;
              [eapply containerCorrect; rewrite find_mapsto_iff; eauto
              | rewrite H0].
            rewrite partition_filter_neq, H; reflexivity.
            eauto.
          * eauto.
        + pose proof (bdelete_correct b search_term); intuition.
          destruct (bdelete b search_term); simpl in *.
          destruct H0;
            [eapply containerCorrect; rewrite find_mapsto_iff; eauto
            | rewrite H1].
          rewrite partition_filter_eq, partition_filter_eq.
          rewrite filter_and, flatten_filter, consist, H; eauto.
        + rewrite partition_filter_neq, flatten_filter.
          unfold Values.
          pose proof (alt_IndexedBag_RepInv _ containerCorrect) as containerCorrect'.
          rewrite <- not_find_in_iff in H.
          rewrite elements_in_iff in H.
          clear containerCorrect.
          induction (elements container); simpl.
          * constructor.
          * rewrite IHl.
            apply Permutation_app; eauto.
            assert (forall item : TItem,
                      List.In item (benumerate (snd a)) -> E.eq (projection item) (fst a))
              by (intros; eapply containerCorrect'; eauto; repeat constructor; reflexivity).
            assert (~ E.eq key (fst a))
              by (unfold not; intros; apply H; eexists; repeat econstructor; eauto).
            revert H0 H1.
            clear; induction (benumerate (snd a)); simpl; intros.
            constructor.
            case_eq (KeyFilter key a0); simpl.
            intros; apply KeyFilter_true in H; rewrite <- H in H1.
            exfalso; apply H1; apply H0; eauto.
            rewrite <- IHl; eauto.
            unfold not; intros H1; apply H; destruct H1;
            econstructor; constructor 2; eauto.
            intros; eapply containerCorrect'; eauto.
        + rewrite partition_filter_eq, flatten_filter.
          unfold Values.
          pose proof (alt_IndexedBag_RepInv _ containerCorrect) as containerCorrect'.
          rewrite <- not_find_in_iff in H.
          rewrite elements_in_iff in H.
          induction (elements container); simpl.
          * constructor.
          * rewrite <- IHl.
            assert (forall item : TItem,
                      List.In item (benumerate (snd a)) -> E.eq (projection item) (fst a))
              by (intros; eapply containerCorrect'; eauto; repeat constructor; reflexivity).
            assert (~ E.eq key (fst a))
              by (unfold not; intros; apply H; eexists; repeat econstructor; eauto).
            revert H0 H1.
            clear; induction (benumerate (snd a)); simpl; intros.
            constructor.
            case_eq (KeyFilter key a0); simpl.
            intros; apply KeyFilter_true in H; rewrite <- H in H1.
            exfalso; apply H1; apply H0; eauto.
            rewrite <- IHl; eauto.
            unfold not; intros H1; apply H; destruct H1;
            econstructor; constructor 2; eauto.
            intros; eapply containerCorrect'; eauto.
      - unfold IndexedBag_benumerate, IndexedBag_bfind_matcher,
        IndexedBag_bdelete; simpl.
        rewrite fold_pair; unfold Values; simpl; intuition.
        + rewrite !FMap_Insert_fold_add, elements_empty, app_nil_r by
              eauto using empty_In.
          rewrite !List.map_map; simpl.
          pose proof (alt_IndexedBag_RepInv _ containerCorrect) as containerCorrect'.
          induction (elements container); simpl;
          [ constructor
          | rewrite IHl, partition_app; simpl; f_equiv ].
          eapply bdelete_correct.
          destruct a; eapply containerCorrect'; repeat constructor; eauto.
          intros; eapply containerCorrect'; eauto.
        + rewrite fold_1, fold_left_fst_partition with (l' := []);
          try reflexivity.
          intros; apply containerCorrect; rewrite elements_mapsto_iff; auto.
    Qed.

    Lemma fold_left_fst_partition_update :
      forall search_term update_term (valid_update: ValidUpdate update_term) l l' l'',
      (forall (key0 : TKey) (bag : BagType),
                InA (@eq_key_elt _) (key0, bag) l ->
                RepInv bag /\
                (forall item : TItem,
                   List.In item (benumerate bag) ->
                   E.eq (projection item) key0))
      -> Permutation l''
                    (fst
                       (List.partition (fun item : TItem => bfind_matcher search_term item)
                                       l'))
        -> Permutation
             (fold_left
                (fun (a : list TItem) (p : key * BagType) =>
                   fst (bupdate (snd p) search_term update_term) ++ a) l l'')
          (fst
             (List.partition (fun item : TItem => bfind_matcher search_term item)
                             (l' ++ (flatten
                                      ((List.map benumerate (List.map snd l))))))).
    Proof.
      induction l; simpl; intros.
      rewrite app_nil_r; eauto.
      rewrite app_assoc.
      rewrite <- IHl; f_equiv.
      intros; eapply H; constructor 2; eauto.
      rewrite H0, partition_app; simpl.
      rewrite Permutation_app_comm; f_equiv.
      apply bupdate_correct.
      destruct a; eapply H; repeat constructor; eauto.
      assumption.
    Qed.

    Lemma IndexedBag_BagUpdateCorrect :
      BagUpdateCorrect IndexedBag_RepInv IndexedBag_ValidUpdate
                       IndexedBag_bfind IndexedBag_bfind_matcher
                       IndexedBag_benumerate bupdate_transform IndexedBag_bupdate.
    Proof.
      hnf.
      destruct search_term as [option_key search_term];
      destruct option_key as [ key | ];
      unfold IndexedBag_benumerate, IndexedBag_bfind_matcher; simpl.

      (* Key provided *)

      - case_eq (find key container); simpl; intros.
          destruct valid_update as [valid_update valid_update'].

        + rewrite partition_filter_neq.
          repeat rewrite <- flat_map_flatten;
            rewrite filter_flat_map; repeat rewrite flat_map_flatten.
          pose proof (bupdate_correct b search_term update_term); intuition.
          repeat rewrite Permutation_map_Values.
          destruct (bupdate b search_term update_term); simpl in *.
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
          destruct H0. eapply containerCorrect; rewrite find_mapsto_iff; eauto. intuition.
          repeat rewrite flatten_app; simpl; rewrite H0.
          rewrite app_nil_r, !app_assoc, Permutation_app; eauto.
          * rewrite Permutation_map_filter_negb; rewrite consist'; f_equiv.
            rewrite <- Permutation_map_Values,
            Permuation_filter_flatten, Permutation_map_Values,
            Permutation_map_filter, consist4, H.
            rewrite partition_filter_neq; reflexivity.
            eauto.
            eauto.
          *  rewrite partition_filter_eq, partition_filter_eq.
             rewrite filter_and, flatten_filter, consist, H; eauto.
          * eapply containerCorrect; rewrite find_mapsto_iff; eauto.
          * destruct (bupdate b search_term update_term); simpl in *.
            destruct H0. eapply containerCorrect; rewrite find_mapsto_iff; eauto. intuition.
            rewrite H1; rewrite partition_filter_eq, partition_filter_eq.
            rewrite filter_and, flatten_filter, consist, H; eauto.
        + rewrite partition_filter_neq, flatten_filter,
          partition_filter_eq, filter_and, flatten_filter,
          consist, H; simpl; eauto; rewrite app_nil_r.
          pose proof (alt_IndexedBag_RepInv _ containerCorrect) as containerCorrect'.
          rewrite <- not_find_in_iff in H.
          rewrite elements_in_iff in H.
          unfold Values; induction (elements container); simpl; intuition.
          rewrite <- (fun x y => proj1 (IHl x y)); f_equiv.
          assert (forall item : TItem,
                    List.In item (benumerate (snd a)) -> E.eq (projection item) (fst a))
            by (intros; eapply containerCorrect'; eauto; repeat constructor; reflexivity).
          assert (~ E.eq key (fst a))
            by (unfold not; intros; apply H; eexists; repeat econstructor; eauto).
          revert H0 H1.
          clear; induction (benumerate (snd a)); simpl; intros.
          constructor.
          case_eq (KeyFilter key a0); simpl.
          intros; apply KeyFilter_true in H; rewrite <- H in H1.
          exfalso; apply H1; apply H0; eauto.
          rewrite <- IHl; eauto.
          unfold not; intros H1; apply H; destruct H1;
          econstructor; constructor 2; eauto.
          intros; eapply containerCorrect'; eauto.
      - unfold IndexedBag_benumerate, IndexedBag_bfind_matcher; simpl; intros.
        rewrite fold_pair with (f := fun _ y => bupdate y search_term update_term).
        unfold Values; simpl; intuition.
        + rewrite !FMap_Insert_fold_add, elements_empty, app_nil_r by
              eauto using empty_In.
          rewrite !List.map_map; simpl.
          pose proof (alt_IndexedBag_RepInv _ containerCorrect) as containerCorrect'.
          induction (elements container); simpl.
          * constructor.
          * rewrite IHl, partition_app; simpl.
            destruct valid_update as [valid_update valid_update'].
            rewrite Permutation_app by
                (try (apply bupdate_correct; try eassumption;
                      destruct a; eapply containerCorrect'; repeat constructor; eauto);
                 eauto).
            rewrite <- !app_assoc.
            apply Permutation_app;
              [f_equiv
              | rewrite Permutation_app_comm, <- app_assoc].
            apply Permutation_app;
              [f_equiv
              | rewrite Permutation_app_comm, map_app; f_equiv].
            intros; apply containerCorrect'; constructor 2; eauto.
        + rewrite fold_1; rewrite fold_left_fst_partition_update with (l' := []);
          try reflexivity; try apply valid_update.
          intros; apply containerCorrect; rewrite elements_mapsto_iff; auto.
    Qed.

  End TreeBagDefinitions.

  Global Instance IndexedBagAsBag
           {BagType TItem SearchTermType UpdateTermType : Type}
           (TBag : Bag BagType TItem SearchTermType UpdateTermType)
           projection
  : Bag IndexedBag TItem ((option TKey) * (SearchTermType)) UpdateTermType :=
    {|

       bempty            := IndexedBag_bempty;
       bfind_matcher     := IndexedBag_bfind_matcher TBag projection;
       bupdate_transform := bupdate_transform;

       benumerate := IndexedBag_benumerate TBag;
       bfind      := IndexedBag_bfind TBag;
       binsert    := IndexedBag_binsert TBag projection;
       bcount     := IndexedBag_bcount TBag;
       bdelete    := IndexedBag_bdelete TBag;
       bupdate    := IndexedBag_bupdate TBag |}.


  Global Instance IndexedBagAsCorrectBag
           {BagType TItem SearchTermType UpdateTermType : Type}
           (TBag : Bag BagType TItem SearchTermType UpdateTermType)
           (RepInv : BagType -> Prop)
           (ValidUpdate : UpdateTermType -> Prop)
           (CorrectTBag : CorrectBag RepInv ValidUpdate TBag)
           projection
  : CorrectBag (IndexedBag_RepInv _ RepInv projection)
               (IndexedBag_ValidUpdate _ ValidUpdate projection)
               (IndexedBagAsBag TBag projection ) :=
    {
       bempty_RepInv     := IndexedBag_Empty_RepInv TBag RepInv projection;
       binsert_RepInv    := IndexedBag_binsert_Preserves_RepInv TBag _ _ _ projection;
       bdelete_RepInv    := IndexedBag_bdelete_Preserves_RepInv TBag _ _ _ projection;
       bupdate_RepInv    := IndexedBag_bupdate_Preserves_RepInv TBag _ _ _ projection;

       binsert_enumerate := IndexedBag_BagInsertEnumerate TBag RepInv _ CorrectTBag projection;
       benumerate_empty  := IndexedBag_BagEnumerateEmpty TBag projection;
       bfind_correct     := IndexedBag_BagFindCorrect TBag _ _ CorrectTBag projection;
       bcount_correct    := IndexedBag_BagCountCorrect TBag _ _ CorrectTBag projection;
       bdelete_correct   := IndexedBag_BagDeleteCorrect TBag _ _ CorrectTBag projection;
       bupdate_correct   := IndexedBag_BagUpdateCorrect TBag _ _ CorrectTBag projection
    }.

End TreeBag.
