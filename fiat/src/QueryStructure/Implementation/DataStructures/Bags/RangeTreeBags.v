Require Export Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsInterface
        Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsProperties.

Require Import
        Coq.FSets.FMapInterface
        Coq.FSets.FMapFacts
        Coq.FSets.FMapAVL
        Fiat.Common
        Fiat.Common.List.ListFacts
        Fiat.Common.List.FlattenList
        Fiat.Common.SetEqProperties
        Fiat.Common.FMapExtensions
        Fiat.Common.List.PermutationFacts.

Module RangeTreeBag (X : OrderedType).
  Module Import XMap := FMapAVL.Make X.

  Module Import XMapFacts := WFacts_fun X XMap.
  Module Import XMapProperties := WProperties_fun X XMap.
  Module Import MoreXMapFacts := FMapExtensions_fun X XMap.

  Definition X_le_dec (x y : X.t) :=
    match (X.compare x y) with
      | LT _ => true
      | EQ _ => true
      | GT _ => false
    end.

  Theorem X_le_sound : forall x y, X_le_dec x y = true <-> X.eq x y \/ X.lt x y.
  Proof.
    intros x y; unfold X_le_dec.
    destruct (X.compare x y); intuition.
    - apply X.lt_not_eq in l; eauto.
    - apply Raw.Proofs.L.PX.MO.lt_le in l; eauto.
  Qed.

  Lemma X_le_dec_trans :
    forall x y z, X_le_dec x y = true -> X_le_dec y z = true -> X_le_dec x z = true.
  Proof.
    unfold X_le_dec; intros;
    destruct (X.compare x y); destruct (X.compare y z); intuition.
    - apply X_le_sound; right; eapply X.lt_trans; eauto.
    - apply X_le_sound; right; eapply Raw.Proofs.L.PX.MO.lt_eq; eauto.
    - apply X_le_sound; right; eapply Raw.Proofs.L.PX.MO.eq_lt; eauto.
    - apply X_le_sound; left; eapply X.eq_trans; eauto.
  Qed.

  Section RangeTreeDefinition.
    Context {BagType TItem SearchTermType UpdateTermType : Type}
            (TBag : Bag BagType TItem SearchTermType UpdateTermType)
            (RepInv : BagType -> Prop)
            (ValidUpdate : UpdateTermType -> Prop)
            (TBagCorrect : CorrectBag RepInv ValidUpdate TBag)
            (projection: TItem -> TKey).

    Definition RangeTreeBag := t BagType.
    Definition RawRangeTreeBag := Raw.tree BagType.

    Definition RangeTreeBag_bempty : RangeTreeBag := empty BagType.

    Definition Range_Min_le_Value (key : option TKey) (value : TKey) :=
      match key with
        | None => true
        | Some key' => X_le_dec key' value
      end.

    Lemma Range_Min_le_Value_trans :
      forall key value value',
        Range_Min_le_Value key value = true -> X_le_dec value value' = true ->
        Range_Min_le_Value key value' = true.
    Proof.
      intros key value value' H_kv H_vv'.
      destruct key; intuition; simpl in *; eapply X_le_dec_trans; eauto.
    Qed.

    Definition Range_Value_le_Max (value : TKey) (key : option TKey) :=
      match key with
        | None => true
        | Some key' => X_le_dec value key'
      end.

    Lemma Range_Value_le_Max_trans :
      forall key value value',
        X_le_dec value' value = true -> Range_Value_le_Max value key = true ->
        Range_Value_le_Max value' key = true.
    Proof.
      intros key value value' H_v'v H_vk.
      destruct key; intuition; simpl in *; eapply X_le_dec_trans; eauto.
    Qed.

    Definition Range_InRange (key: (option TKey) * (option TKey)) (value : TKey) :=
      Range_Min_le_Value (fst key) value &&
      Range_Value_le_Max value (snd key).

    Definition RangeTreeBag_bfind_matcher
               (key_searchterm : ((option TKey) * (option TKey)) * SearchTermType)
               (item : TItem) :=
      Range_InRange (fst key_searchterm) (projection item) && (bfind_matcher (snd key_searchterm) item).

    Definition RangeTreeBag_bcollect (container : RawRangeTreeBag) : list (TKey * BagType) :=
      Raw.elements container.

    Definition RangeTreeBag_benumerate (container : RangeTreeBag) : list TItem :=
      flatten (List.map benumerate (Values container)).

    Fixpoint RangeTreeBag_btraverse_left
             (container : RawRangeTreeBag)
             (min_key : option TKey) : list (TKey * BagType) :=
      match container with
        | Raw.Leaf => []
        | Raw.Node l key' bag r _ =>
          if Range_Min_le_Value min_key key' then
            RangeTreeBag_btraverse_left l min_key ++
              (key', bag) :: RangeTreeBag_bcollect r
          else
            RangeTreeBag_btraverse_left r min_key
      end.

    Fixpoint RangeTreeBag_btraverse_right
             (container : RawRangeTreeBag)
             (max_key : option TKey) : list (TKey * BagType) :=
      match container with
        | Raw.Leaf => []
        | Raw.Node l key' bag r _ =>
          if Range_Value_le_Max key' max_key then
            (* if the key is less than or equal to max_key, we collect it and the left subtree then go right *)
            RangeTreeBag_bcollect l ++ (key', bag) :: RangeTreeBag_btraverse_right r max_key
          else
            (* otherwise when key is greater than max_key, we just go left *)
            RangeTreeBag_btraverse_right l max_key
      end.

    Fixpoint RangeTreeBag_btraverse
             (container : RawRangeTreeBag)
             (key : (option TKey) * (option TKey)) : list (TKey * BagType) :=
      let (min_key, max_key) := key in
      match container with
        | Raw.Leaf => []
        | Raw.Node l key' bag r _ =>
          if Range_Min_le_Value min_key key' then
            if Range_Value_le_Max key' max_key then
              RangeTreeBag_btraverse_left l min_key ++ (key', bag) :: RangeTreeBag_btraverse_right r max_key
            else
              RangeTreeBag_btraverse l key
          else
            RangeTreeBag_btraverse r key
      end.

    Definition RangeTreeBag_bfind
               (container : RangeTreeBag)
               (key_searchterm : ((option TKey) * (option TKey)) * SearchTermType) : list TItem :=
      let (key, searchterm) := key_searchterm in
      flatten (List.map (fun key_bag => bfind (snd key_bag) searchterm) (RangeTreeBag_btraverse container key)).

    Definition RangeTreeBag_bcount
               (container : RangeTreeBag)
               (key_searchterm : ((option TKey) * (option TKey)) * SearchTermType) : nat :=
      let (key, searchterm) := key_searchterm in
      List.fold_right (fun key_bag acc => acc + bcount (snd key_bag) searchterm)
                      0 (RangeTreeBag_btraverse container key).

    Definition RangeTreeBag_binsert
               (container : RangeTreeBag)
               (item : TItem) : RangeTreeBag :=
      let key := projection item in
      let bag := FindWithDefault key bempty container in
      add key (binsert bag item) container.

    Definition RangeTreeBag_bdelete
               (container : RangeTreeBag)
               (key_searchterm : ((option TKey) * (option TKey)) * SearchTermType) : (list TItem) * RangeTreeBag :=
      let (key, searchterm) := key_searchterm in
      let key_bags := RangeTreeBag_btraverse container key in
      List.fold_right (fun (key_bag : TKey * BagType) (res : (list TItem) * RangeTreeBag) =>
                         let (key, bag) := (fst key_bag, snd key_bag) in
                         let (deleted, bag') := (fst (bdelete bag searchterm), snd (bdelete bag searchterm)) in
                         ((fst res) ++ deleted, add key bag' (snd res))
                      ) ([], container) key_bags.

    Definition RangeTreeBag_bupdate
               (container : RangeTreeBag)
               (key_searchterm : ((option TKey) * (option TKey)) * SearchTermType)
               (update_term : UpdateTermType) : (list TItem) * RangeTreeBag :=
      let (key, searchterm) := key_searchterm in
      let key_bags := RangeTreeBag_btraverse container key in
      List.fold_right (fun (key_bag : TKey * BagType) (res : (list TItem) * RangeTreeBag) =>
                         let (key, bag) := (fst key_bag, snd key_bag) in
                         let (deleted, bag') := (fst (bupdate bag searchterm update_term), snd (bupdate bag searchterm update_term)) in
                         ((fst res) ++ deleted, add key bag' (snd res))
                      ) ([], container) key_bags.

    Definition RangeTreeBag_RepInv (fmap : RangeTreeBag) :=
      forall (key : TKey) (bag : BagType),
         MapsTo key bag fmap ->
         (RepInv bag /\ forall (item : TItem), List.In item (benumerate bag) -> X.eq (projection item) key).

    Definition RangeTreeBag_ValidUpdate (update_term : UpdateTermType) :=
      ValidUpdate update_term /\
      forall (key : TKey) (item : TItem),
        X.eq (projection item) key -> X.eq (projection (bupdate_transform update_term item)) key.

    Theorem RangeTreeBag_Empty_RepInv :
      RangeTreeBag_RepInv RangeTreeBag_bempty.
    Proof.
      unfold RangeTreeBag_RepInv;
      intros; rewrite empty_mapsto_iff in *; exfalso; trivial.
    Qed.

    Lemma RangeTreeBag_bcollect_correct :
      forall container key bag,
        InA (@eq_key_elt _) (key, bag) (RangeTreeBag_bcollect container.(this)) <->
        MapsTo key bag container.
    Proof.
      unfold RangeTreeBag_bcollect.
      intros container key' bag'.
      change (Raw.elements container) with (elements container).
      split; intro H.
      - rewrite elements_mapsto_iff. assumption.
      - apply elements_1 in H.
        remember (elements (elt := BagType) container) as ls. clear Heqls.
        induction ls; simpl; inversion H; subst.
        + left. assumption.
        + assumption.
    Qed.

    Lemma RangeTreeBag_btraverse_left_correct :
      forall container minkey key bag,
        InA (@eq_key_elt _) (key, bag) (RangeTreeBag_btraverse_left container.(this) minkey) <->
        MapsTo key bag container /\ Range_Min_le_Value minkey key = true.
    Proof.
      intros [ ctn_raw ctn_proof ] minkey key bag; split; intro hyp.
      {
        induction ctn_raw; intros; simpl in *.
        - inversion hyp.
        - inversion ctn_proof; subst.
          specialize (IHctn_raw1 H3); specialize (IHctn_raw2 H5).
          destruct (Range_Min_le_Value minkey k) eqn: min_cmp.
          + rewrite InA_app_iff in hyp; try apply eqke_equiv. rewrite InA_cons in hyp.
            destruct hyp as [ hyp_l | [ hyp_s | hyp_r ] ].
            * apply IHctn_raw1 in hyp_l. split. apply Raw.MapsLeft. tauto. tauto.
            * inversion hyp_s. simpl in *. subst.
              split. econstructor. eauto.
              destruct minkey; intuition; unfold Range_Min_le_Value in *.
              apply X_le_sound in min_cmp; apply X_le_sound.
              destruct min_cmp. eauto.
              right; apply X.eq_sym in H; eapply Raw.Proofs.L.PX.MO.lt_eq; eauto.
            * inversion ctn_proof; subst.
              pose ({| this := ctn_raw2; is_bst := H9 |}).
              change (ctn_raw2) with (b.(this)) in hyp_r.
              rewrite RangeTreeBag_bcollect_correct in hyp_r.
              split. apply Raw.MapsRight. eauto.
              apply Raw.Proofs.MapsTo_In in hyp_r.
              specialize (H11 _ hyp_r).
              eapply Range_Min_le_Value_trans; eauto.
              rewrite X_le_sound; eauto.
          + apply IHctn_raw2 in hyp. split. apply Raw.MapsRight. tauto. tauto.
      }
      {
        destruct hyp as [ hyp_m hyp_r ]; induction ctn_raw; intros; simpl in *.
        - inversion hyp_m.
        - inversion ctn_proof; subst.
          specialize (IHctn_raw1 H3); specialize (IHctn_raw2 H5).
          destruct (Range_Min_le_Value minkey k) eqn: min_cmp.
          + apply InA_app_iff; try apply eqke_equiv; rewrite InA_cons.
            inversion hyp_m; subst.
            * right; left. econstructor; eauto.
            * left. apply IHctn_raw1. eauto.
            * right; right.
              change ctn_raw2 with {| this := ctn_raw2; is_bst := H5 |}.(this).
              rewrite RangeTreeBag_bcollect_correct. eauto.
          + apply IHctn_raw2.
            inversion hyp_m; subst; eauto; exfalso;
            destruct minkey; simpl in *; try discriminate.
            * rewrite <- not_true_iff_false in *.
              rewrite X_le_sound in *. intuition eauto.
            * apply Raw.Proofs.MapsTo_In in H0.
              specialize (H6 _ H0). rewrite <- not_true_iff_false in *.
              rewrite X_le_sound in *; intuition eauto.
      }
    Qed.

    Lemma RangeTreeBag_btraverse_right_correct :
      forall container maxkey key bag,
        InA (@eq_key_elt _) (key, bag) (RangeTreeBag_btraverse_right container.(this) maxkey) <->
        MapsTo key bag container /\ Range_Value_le_Max key maxkey = true.
    Proof.
      intros [ ctn_raw ctn_proof ] maxkey key bag; split; intro hyp.
      {
        induction ctn_raw; intros; simpl in *.
        - inversion hyp.
        - inversion ctn_proof; subst.
          specialize (IHctn_raw1 H3); specialize (IHctn_raw2 H5).
          destruct (Range_Value_le_Max k maxkey) eqn: max_cmp.
          + rewrite InA_app_iff in hyp; try apply eqke_equiv. rewrite InA_cons in hyp.
            destruct hyp as [ hyp_l | [ hyp_s | hyp_r ] ].
            * inversion ctn_proof; subst.
              pose ({| this := ctn_raw1; is_bst := H4 |}).
              change (ctn_raw1) with (b.(this)) in hyp_l.
              rewrite RangeTreeBag_bcollect_correct in hyp_l.
              split. apply Raw.MapsLeft. eauto.
              apply Raw.Proofs.MapsTo_In in hyp_l.
              specialize (H10 _ hyp_l).
              eapply Range_Value_le_Max_trans; eauto.
              rewrite X_le_sound; eauto.
            * inversion hyp_s. simpl in *. subst.
              split. econstructor. eauto.
              destruct maxkey; intuition; unfold Range_Value_le_Max in *.
              apply X_le_sound in max_cmp; apply X_le_sound.
              destruct max_cmp; eauto.
            * apply IHctn_raw2 in hyp_r. split. apply Raw.MapsRight. tauto. tauto.
          + apply IHctn_raw1 in hyp. split. apply Raw.MapsLeft. tauto. tauto.
      }
      {
        destruct hyp as [ hyp_m hyp_r ]; induction ctn_raw; intros; simpl in *.
        - inversion hyp_m.
        - inversion ctn_proof; subst.
          specialize (IHctn_raw1 H3); specialize (IHctn_raw2 H5).
          destruct (Range_Value_le_Max k maxkey) eqn: max_cmp.
          + apply InA_app_iff; try apply eqke_equiv; rewrite InA_cons.
            inversion hyp_m; subst.
            * right; left. econstructor; eauto.
            * left.
              change ctn_raw1 with {| this := ctn_raw1; is_bst := H3 |}.(this).
              rewrite RangeTreeBag_bcollect_correct. eauto.
            * right; right. apply IHctn_raw2; eauto.
          + apply IHctn_raw1.
            inversion hyp_m; subst; eauto; exfalso;
            destruct maxkey; simpl in *; try discriminate.
            * rewrite <- not_true_iff_false in *.
              rewrite X_le_sound in *. intuition.
              eapply H1; eapply X.eq_trans; eauto.
              eapply H2; eapply X.eq_sym in H0; eapply Raw.Proofs.L.PX.MO.eq_lt; eauto.
            * apply Raw.Proofs.MapsTo_In in H0.
              specialize (H7 _ H0). rewrite <- not_true_iff_false in *.
              rewrite X_le_sound in *; intuition eauto.
      }
    Qed.

    Lemma RangeTreeBag_btraverse_correct :
      forall container searchkey key bag,
        InA (@eq_key_elt _) (key, bag) (RangeTreeBag_btraverse container.(this) searchkey) <->
        MapsTo key bag container /\ Range_InRange searchkey key = true.
    Proof.
      intros [ ctn_raw ctn_proof ] [ minkey maxkey ] key bag; split; intro hyp.
      {
        induction ctn_raw; intros; simpl in *.
        - inversion hyp.
        - inversion ctn_proof; subst.
          specialize (IHctn_raw1 H3); specialize (IHctn_raw2 H5).
          destruct (Range_Min_le_Value minkey k) eqn: min_cmp; destruct (Range_Value_le_Max k maxkey) eqn: max_cmp.
          + apply InA_app_iff in hyp; try apply eqke_equiv; rewrite InA_cons in hyp.
            inversion hyp as [ hyp_l | [ hyp_m | hyp_r ] ].
            * change ctn_raw1 with {| this := ctn_raw1; is_bst := H3 |}.(this) in hyp_l.
              rewrite RangeTreeBag_btraverse_left_correct in hyp_l; destruct hyp_l; split.
              apply Raw.MapsLeft; assumption.
              unfold Range_InRange. simpl. rewrite H0. simpl.
              apply Raw.Proofs.MapsTo_In in H. specialize (H6 _ H).
              eapply Range_Value_le_Max_trans; try eapply X_le_sound; eauto.
            * inversion hyp_m. simpl in *. subst. split.
              econstructor; eauto.
              unfold Range_InRange. simpl. apply andb_true_intro. split.
              destruct minkey; auto; simpl in *; rewrite X_le_sound in *; inversion min_cmp;
              [ left | right; eapply Raw.Proofs.L.PX.MO.lt_eq ]; eauto.
              destruct maxkey; auto; simpl in *; rewrite X_le_sound in *; inversion max_cmp;
              [ left | right; eapply Raw.Proofs.L.PX.MO.lt_eq ]; eauto.
            * change ctn_raw2 with {| this := ctn_raw2; is_bst := H5 |}.(this) in hyp_r.
              rewrite RangeTreeBag_btraverse_right_correct in hyp_r; destruct hyp_r; split.
              apply Raw.MapsRight; assumption.
              unfold Range_InRange. simpl. rewrite H0. rewrite andb_true_r.
              apply Raw.Proofs.MapsTo_In in H. specialize (H7 _ H).
              eapply Range_Min_le_Value_trans; try eapply X_le_sound; eauto.
          + apply IHctn_raw1 in hyp; intuition; apply Raw.MapsLeft; eauto.
          + apply IHctn_raw2 in hyp; intuition; apply Raw.MapsRight; eauto.
          + apply IHctn_raw2 in hyp; intuition; apply Raw.MapsRight; eauto.
      }
      {
        destruct hyp as [ hyp_m hyp_r ]; induction ctn_raw; intros; simpl in *.
        - inversion hyp_m.
        - inversion ctn_proof; subst.
          specialize (IHctn_raw1 H3); specialize (IHctn_raw2 H5).
          destruct (Range_Min_le_Value minkey k) eqn: min_cmp; [ destruct (Range_Value_le_Max k maxkey) eqn: max_cmp | ].
          + apply InA_app_iff; try apply eqke_equiv; rewrite InA_cons.
            inversion hyp_m as [ hyp_mm | hyp_ml | hyp_mr ]; subst.
            * right; left; econstructor; eauto.
            * left. change ctn_raw1 with {| this := ctn_raw1; is_bst := H3 |}.(this).
              rewrite RangeTreeBag_btraverse_left_correct; intuition.
              unfold Range_InRange in hyp_r. rewrite andb_true_iff in hyp_r. tauto.
            * right; right. change ctn_raw2 with {| this := ctn_raw2; is_bst := H5 |}.(this).
              rewrite RangeTreeBag_btraverse_right_correct; intuition.
              unfold Range_InRange in hyp_r. rewrite andb_true_iff in hyp_r. tauto.
          + apply IHctn_raw1; inversion hyp_m; subst; eauto;
            unfold Range_InRange in hyp_r; apply andb_prop in hyp_r; destruct hyp_r; simpl in *;
            [ apply X.eq_sym in H0; eapply or_introl in H0; eapply X_le_sound in H0 |
              apply Raw.Proofs.MapsTo_In in H0; specialize (H7 _ H0);
              eapply or_intror in H7; eapply X_le_sound in H7 ];
            eapply Range_Value_le_Max_trans with (value' := k) in H1; auto;
            rewrite H1 in max_cmp; discriminate.
          + apply IHctn_raw2; inversion hyp_m; subst; eauto;
            unfold Range_InRange in hyp_r; apply andb_prop in hyp_r; destruct hyp_r; simpl in *;
            [ eapply or_introl in H0; eapply X_le_sound in H0 |
              apply Raw.Proofs.MapsTo_In in H0; specialize (H6 _ H0);
              eapply or_intror in H6; eapply X_le_sound in H6 ];
            eapply Range_Min_le_Value_trans with (value' := k) in H; auto;
            rewrite H in min_cmp; discriminate.
      }
    Qed.

    Corollary RangeTreeBag_btraverse_closed :
      forall container searchkey key bag,
        InA (@eq_key_elt _) (key, bag) (RangeTreeBag_btraverse container.(this) searchkey) ->
        MapsTo key bag container.
    Proof.
      intros container searchkey key' bag' H.
      rewrite RangeTreeBag_btraverse_correct in H.
      tauto.
    Qed.

    Theorem RangeTreeBag_binsert_Preserves_RepInv :
      binsert_Preserves_RepInv RangeTreeBag_RepInv RangeTreeBag_binsert.
    Proof.
      unfold binsert_Preserves_RepInv, RangeTreeBag_RepInv.
      intros ? item' ? k' bag' maps_to.
      unfold RangeTreeBag_binsert in maps_to.
      rewrite add_mapsto_iff in maps_to;
        destruct maps_to as [(is_eq & refreshed) | (neq & maps_to)];
        subst; intuition; intros.
      - destruct (FindWithDefault_dec (projection item') bempty container)
          as [ [bag' (mapsto & equality)] | (not_found & equality) ];
        rewrite equality in *; eauto using binsert_RepInv.
        eapply binsert_RepInv; eapply containerCorrect; eauto.
        eapply binsert_RepInv; eapply bempty_RepInv.
      - rewrite <- is_eq.
        rewrite binsert_enumerate_weak with (RepInv0 := RepInv) (ValidUpdate0 := ValidUpdate) in H;
          intuition; subst.
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

    Theorem RangeTreeBag_bdelete_Preserves_RepInv :
      bdelete_Preserves_RepInv RangeTreeBag_RepInv RangeTreeBag_bdelete.
    Proof.
      unfold bdelete_Preserves_RepInv, RangeTreeBag_RepInv, RangeTreeBag_bdelete.
      intros container key_searchterm containerCorrect key' bag' inv'.
      destruct key_searchterm as [ filter searchterm ].
      pose proof (RangeTreeBag_btraverse_closed container filter) as Hc.
      remember (RangeTreeBag_btraverse container filter) as ls; clear Heqls.
      induction ls as [ | [ key bag ] ls' ]; intros; simpl in inv'.
      - eauto.
      - destruct (bdelete bag searchterm) as [ bdelete_del bdelete_bag ] eqn: bdelete_des; simpl in inv'.
        rewrite add_mapsto_iff in inv'.
        inversion inv' as [ [ inv'_eq inv'_next ] | [ inv'_neq inv'_ind ] ]; clear inv'; subst.
        + specialize (Hc key bag).
          assert (InA (eq_key_elt (elt:=BagType)) (key, bag) ((key, bag) :: ls')).
          repeat constructor; apply X.eq_refl.
          apply Hc in H.
          apply containerCorrect in H; destruct H as [ cont_rep cont_in ].
          pose proof (bdelete_RepInv bag searchterm cont_rep) as bdel_rep.
          rewrite bdelete_des in bdel_rep. simpl in bdel_rep. intuition.
          pose proof (bdelete_correct bag searchterm cont_rep) as [ bdel_correct_snd _ ].
          rewrite bdelete_des in bdel_correct_snd. simpl in bdel_correct_snd.
          pose proof (Permutation_in _ bdel_correct_snd H).
          pose proof (In_partition (bfind_matcher searchterm) (benumerate bag) item) as [ _ inp ].
          eapply X.eq_trans; eauto.
        + eauto.
    Qed.

    Theorem RangeTreeBag_bupdate_Preserves_RepInv :
      bupdate_Preserves_RepInv RangeTreeBag_RepInv RangeTreeBag_ValidUpdate RangeTreeBag_bupdate.
    Proof.
      unfold bupdate_Preserves_RepInv, RangeTreeBag_RepInv, RangeTreeBag_bupdate.
      intros container key_searchterm updateterm containerCorrect [ validupdate_rep validupdate_rt ] key' bag' inv'.
      destruct key_searchterm as [ filter searchterm ].
      pose proof (RangeTreeBag_btraverse_closed container filter) as Hc.
      remember (RangeTreeBag_btraverse container filter) as ls; clear Heqls.
      induction ls as [ | [ key bag ] ls' ]; intros; simpl in inv'.
      - eauto.
      - induction (bupdate bag searchterm updateterm) as [ bupdate_upd bupdate_bag ] eqn: bupdate_des.
        simpl in inv'. rewrite add_mapsto_iff in inv'.
        inversion inv' as [ [ inv'_eq inv'_next ] | [ inv'_neq inv'_ind ] ]; clear inv'; subst.
        + specialize (Hc key bag).
          assert (InA (eq_key_elt (elt:=BagType)) (key, bag) ((key, bag) :: ls')).
          repeat constructor; apply X.eq_refl.
          apply Hc in H.
          apply containerCorrect in H; destruct H as [ cont_rep cont_in ].
          pose proof (bupdate_RepInv bag searchterm updateterm cont_rep) as bupdate_rep.
          rewrite bupdate_des in bupdate_rep. simpl in bupdate_rep. intuition.
          pose proof (bupdate_correct bag searchterm updateterm cont_rep validupdate_rep) as [ bupdate_correct_snd _ ].
          rewrite bupdate_des in bupdate_correct_snd. simpl in bupdate_correct_snd.
          pose proof (Permutation_in _ bupdate_correct_snd H0) as E; apply in_app_or in E; destruct E as [ E | E ].
          * pose proof (In_partition (bfind_matcher searchterm) (benumerate bag) item) as [ _ inp ].
            eapply X.eq_trans; eauto.
          * rewrite in_map_iff in E. destruct E as [ item' [ item'_eq In_item' ] ]. subst.
            apply validupdate_rt. eapply X.eq_trans with key; auto.
            apply cont_in.
            pose proof (In_partition (bfind_matcher searchterm) (benumerate bag) item') as [ _ inp ]; eauto.
        + eauto.
    Qed.

    Theorem RangeTreeBag_BagInsertEnumerate :
      BagInsertEnumerate RangeTreeBag_RepInv RangeTreeBag_benumerate RangeTreeBag_binsert.
    Proof.
      unfold BagInsertEnumerate, RangeTreeBag_benumerate, RangeTreeBag_binsert.
      intros; simpl in *.
      match goal with
        | [ |- context[FindWithDefault ?a ?b ?c] ] =>
          destruct (FindWithDefault_dec a b c)
            as [ [ result (maps_to & _eq) ] | (find_none & _eq) ];
            rewrite _eq; clear _eq
      end.
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
      rewrite <- not_find_in_iff in find_none.
      rewrite values_add_not_in by assumption.
      simpl.
      rewrite binsert_enumerate.
      rewrite benumerate_empty_eq_nil with (RepInv0 := RepInv) (ValidUpdate0 := ValidUpdate); eauto.
      apply bempty_RepInv.
    Qed.

    Theorem RangeTreeBag_BagCountCorrect :
      BagCountCorrect RangeTreeBag_RepInv RangeTreeBag_bcount RangeTreeBag_bfind.
    Proof.
      unfold BagCountCorrect, RangeTreeBag_RepInv, RangeTreeBag_bcount, RangeTreeBag_bfind.
      intros. destruct search_term as [ [ minkey maxkey ] searchterm ].
      remember (RangeTreeBag_btraverse container (minkey, maxkey)) as bs.
      pose proof (RangeTreeBag_btraverse_closed container (minkey, maxkey)).
      rewrite <- Heqbs in H; clear Heqbs.
      rewrite length_flatten.
      setoid_rewrite Plus.plus_comm at 1.
      replace (fun (y : TKey * BagType) (x : nat) => bcount (snd y) searchterm + x)
      with (compose plus (fun (y : TKey * BagType) => bcount (snd y) searchterm)) by reflexivity.
      rewrite !foldright_compose.
      symmetry; setoid_rewrite <- rev_involutive at 1.
      rewrite rev_involutive.
      pose proof bcount_correct; unfold BagCountCorrect in H0.
      induction bs as [ | [ key bag ] bs' ]; simpl.
      - reflexivity.
      - assert (forall k b, InA (eq_key_elt (elt:=BagType)) (k, b) bs' -> MapsTo k b container).
        intros; eapply H; eapply InA_cons_tl; eauto.
        specialize (IHbs' H1); clear H1.
        assert (InA (eq_key_elt (elt:=BagType)) (key, bag) ((key, bag) :: bs')) by
            (econstructor; econstructor; auto).
        specialize (H _ _ H1); clear H1; specialize (containerCorrect _ _ H).
        destruct containerCorrect; specialize (H0 _ searchterm H1).
        rewrite H0. rewrite IHbs'. reflexivity.
    Qed.

    Theorem RangeTreeBag_BagEnumerateEmpty :
      BagEnumerateEmpty RangeTreeBag_benumerate RangeTreeBag_bempty.
    Proof.
      unfold BagEnumerateEmpty, RangeTreeBag_benumerate, RangeTreeBag_bempty, flatten. auto.
    Qed.

    Lemma RangeTreeBag_bcollect_nodup :
      forall container, NoDupA (@eq_key _) (RangeTreeBag_bcollect container.(this)).
    Proof.
      unfold RangeTreeBag_bcollect.
      intro container.
      change (Raw.elements container) with (elements container).
      eapply Raw.Proofs.elements_nodup.
      exact (container.(is_bst)).
    Qed.

    Lemma InA_eqk_eqke :
      forall (elt : Type) (k : X.t) (e : elt) (ls : list (key * elt)),
        InA (eq_key (elt := elt)) (k, e) ls -> exists e', InA (eq_key_elt (elt := elt)) (k, e') ls.
    Proof.
      induction ls; intros; inversion H; subst.
      - destruct a. exists e0. constructor.
        unfold eq_key, Raw.Proofs.PX.eqk in H1. simpl in H1.
        unfold eq_key_elt, Raw.Proofs.PX.eqke. tauto.
      - specialize (IHls H1).
        destruct IHls.
        exists x. apply InA_cons_tl. exact H0.
    Qed.

    Lemma RangeTreeBag_btraverse_left_nodup :
      forall container keys, NoDupA (@eq_key _) (RangeTreeBag_btraverse_left container.(this) keys).
    Proof.
      intros [ ctn_raw ctn_proof ] key. induction ctn_raw.
      - constructor.
      - simpl. inversion ctn_proof. subst.
        specialize (IHctn_raw1 H3). specialize (IHctn_raw2 H5).
        destruct (Range_Min_le_Value key k).
        + apply NoDupA_app; try apply eqk_equiv; try apply NoDupA_cons; auto; unfold not; intros.
          * apply InA_eqk_eqke in H; destruct H.
            change ctn_raw2 with {| this := ctn_raw2; is_bst := H5 |}.(this) in H.
            rewrite RangeTreeBag_bcollect_correct in H.
            apply Raw.Proofs.MapsTo_In in H; specialize (H7 _ H).
            apply Raw.Proofs.MX.lt_antirefl in H7; eauto.
          * change ctn_raw2 with {| this := ctn_raw2; is_bst := H5 |}.(this).
            apply RangeTreeBag_bcollect_nodup.
          * change ctn_raw1 with {| this := ctn_raw1; is_bst := H3 |}.(this) in H.
            destruct x as [ x_key x_bag ].
            apply InA_eqk_eqke in H; destruct H.
            apply InA_eqk_eqke in H0; destruct H0.
            rewrite RangeTreeBag_btraverse_left_correct in H; destruct H.
            apply Raw.Proofs.MapsTo_In in H; specialize (H6 _ H).
            inversion H0; clear H0; subst.
            { unfold eq_key_elt, Raw.Proofs.PX.eqke in H4.
              apply X.lt_not_eq in H6. tauto. }
            { change ctn_raw2 with {| this := ctn_raw2; is_bst := H5 |}.(this) in H4.
              rewrite RangeTreeBag_bcollect_correct in H4.
              apply Raw.Proofs.MapsTo_In in H4; specialize (H7 _ H4).
              apply Raw.Proofs.L.PX.MO.lt_le in H6; eauto. }
        + exact IHctn_raw2.
    Qed.

    Lemma RangeTreeBag_btraverse_right_nodup :
      forall container keys, NoDupA (@eq_key _) (RangeTreeBag_btraverse_right container.(this) keys).
    Proof.
      intros [ ctn_raw ctn_proof ] key. induction ctn_raw.
      - constructor.
      - simpl. inversion ctn_proof. subst.
        specialize (IHctn_raw1 H3). specialize (IHctn_raw2 H5).
        destruct (Range_Value_le_Max k key).
        + apply NoDupA_app; try apply eqk_equiv; try apply NoDupA_cons; auto; unfold not; intros.
          * change ctn_raw1 with {| this := ctn_raw1; is_bst := H3 |}.(this).
            apply RangeTreeBag_bcollect_nodup.
          * apply InA_eqk_eqke in H; destruct H.
            change ctn_raw2 with {| this := ctn_raw2; is_bst := H5 |}.(this) in H.
            rewrite RangeTreeBag_btraverse_right_correct in H; destruct H.
            apply Raw.Proofs.MapsTo_In in H; specialize (H7 _ H).
            apply Raw.Proofs.MX.lt_antirefl in H7; eauto.
          * change ctn_raw1 with {| this := ctn_raw1; is_bst := H3 |}.(this) in H.
            destruct x as [ x_key x_bag ].
            apply InA_eqk_eqke in H; destruct H.
            apply InA_eqk_eqke in H0; destruct H0.
            rewrite RangeTreeBag_bcollect_correct in H; apply Raw.Proofs.MapsTo_In in H; specialize (H6 _ H).
            inversion H0; clear H0; subst.
            { unfold eq_key_elt, Raw.Proofs.PX.eqke in H2.
              apply X.lt_not_eq in H6. tauto. }
            { change ctn_raw2 with {| this := ctn_raw2; is_bst := H5 |}.(this) in H2.
              rewrite RangeTreeBag_btraverse_right_correct in H2; destruct H2.
              apply Raw.Proofs.MapsTo_In in H0; specialize (H7 _ H0).
              apply Raw.Proofs.L.PX.MO.lt_le in H6; eauto. }
        + exact IHctn_raw1.
    Qed.

    Lemma RangeTreeBag_btraverse_nodup :
      forall container keys, NoDupA (@eq_key _) (RangeTreeBag_btraverse container.(this) keys).
    Proof.
      intros [ ctn_raw ctn_proof ] [ minkey maxkey ]. induction ctn_raw; simpl.
      - constructor.
      - simpl; inversion ctn_proof. subst.
        specialize (IHctn_raw1 H3). specialize (IHctn_raw2 H5).
        destruct (Range_Min_le_Value minkey k); simpl.
        + destruct (Range_Value_le_Max k maxkey); simpl.
          * apply NoDupA_app; try apply eqk_equiv; try apply NoDupA_cons; unfold not; intros.
            { change ctn_raw1 with {| this := ctn_raw1; is_bst := H3 |}.(this).
              apply RangeTreeBag_btraverse_left_nodup. }
            { apply InA_eqk_eqke in H; destruct H.
              change ctn_raw2 with {| this := ctn_raw2; is_bst := H5 |}.(this) in H.
              rewrite RangeTreeBag_btraverse_right_correct in H; destruct H.
              apply Raw.Proofs.MapsTo_In in H; specialize (H7 _ H).
              apply Raw.Proofs.MX.lt_antirefl in H7; eauto. }
            { change ctn_raw2 with {| this := ctn_raw2; is_bst := H5 |}.(this).
              apply RangeTreeBag_btraverse_right_nodup. }
            { destruct x as [ x_key x_bag ].
              apply InA_eqk_eqke in H; destruct H.
              change ctn_raw1 with {| this := ctn_raw1; is_bst := H3 |}.(this) in H.
              rewrite RangeTreeBag_btraverse_left_correct in H; destruct H.
              apply Raw.Proofs.MapsTo_In in H; specialize (H6 _ H).
              inversion H0; clear H0; subst.
              { unfold eq_key, Raw.Proofs.PX.eqk in H4.
                apply X.lt_not_eq in H6. tauto. }
              { apply InA_eqk_eqke in H4; destruct H4.
                change ctn_raw2 with {| this := ctn_raw2; is_bst := H5 |}.(this) in H0.
                rewrite RangeTreeBag_btraverse_right_correct in H0; destruct H0.
                apply Raw.Proofs.MapsTo_In in H0; specialize (H7 _ H0).
                apply Raw.Proofs.L.PX.MO.lt_le in H6; eauto. } }
          * apply IHctn_raw1.
        + apply IHctn_raw2.
    Qed.

    Lemma NoDupA_filter :
      forall (A : Type) (eqA : A -> A -> Prop) (f : A -> bool) (ls : list A),
        NoDupA eqA ls -> NoDupA eqA (List.filter f ls).
    Proof.
      intros. induction ls.
      - constructor.
      - simpl. inversion H. subst. destruct (f a).
        + eapply NoDupA_cons; eauto. clear IHls H H3.
          intro. apply H2. clear H2.
          induction ls. inversion H.
          simpl in *. destruct (f a0).
          inversion H; clear H; subst.
          apply InA_cons_hd; eauto.
          apply InA_cons_tl; eapply IHls; eauto.
          apply InA_cons_tl; eauto.
        + eauto.
    Qed.

    Lemma X_le_change_left :
      forall x x' y, X.eq x x' -> X_le_dec x y = X_le_dec x' y.
    Proof.
      intros. destruct (X_le_dec x y) eqn: eq.
      - rewrite X_le_sound in eq; inversion eq; clear eq.
        + symmetry. rewrite X_le_sound. left. eapply X.eq_trans; eauto.
        + symmetry. rewrite X_le_sound. right. symmetry in H. eapply Raw.Proofs.MX.eq_lt; eauto.
      - symmetry. rewrite <- not_true_iff_false. intro.
        rewrite <- not_true_iff_false in eq.
        rewrite X_le_sound in eq, H0.
        inversion H0; clear H0.
        + pose proof (X.eq_trans H H1). tauto.
        + pose proof (Raw.Proofs.MX.eq_lt H H1). tauto.
    Qed.

    Lemma X_le_change_right :
      forall x y y', X.eq y y' -> X_le_dec x y = X_le_dec x y'.
      intros. destruct (X_le_dec x y) eqn: eq.
      - rewrite X_le_sound in eq; inversion eq; clear eq.
        + symmetry. rewrite X_le_sound. left. eapply X.eq_trans; eauto.
        + symmetry. rewrite X_le_sound. right. eapply Raw.Proofs.MX.eq_lt; eauto.
      - symmetry. rewrite <- not_true_iff_false. intro.
        rewrite <- not_true_iff_false in eq.
        rewrite X_le_sound in eq, H0.
        inversion H0; clear H0.
        + symmetry in H. pose proof (X.eq_trans H1 H). tauto.
        + symmetry in H. pose proof (Raw.Proofs.MX.lt_eq H1 H). tauto.
    Qed.

    Lemma InRange_Proper :
      forall keys v v', X.eq v v' -> Range_InRange keys v = Range_InRange keys v'.
    Proof.
      intros.
      unfold Range_InRange, Range_Min_le_Value, Range_Value_le_Max.
      destruct keys as [ min max ]; destruct min as [ min | ]; destruct max as [ max | ]; auto; simpl;
      repeat rewrite X_le_change_left with (x := v) (x' := v') by assumption;
      repeat rewrite X_le_change_right with (y := v) (y' := v') by assumption; reflexivity.
    Qed.

    Lemma RangeTreeBag_btraverse_bcollect :
      forall container keys,
        Permutation
          (List.map snd (RangeTreeBag_btraverse container.(this) keys))
          (List.map snd (List.filter (fun item => Range_InRange keys (fst item)) (RangeTreeBag_bcollect container.(this)))).
    Proof.
      intros; eapply Permutation_InA_cons;
      [ eapply NoDupA_filter; eapply RangeTreeBag_bcollect_nodup |
        eapply RangeTreeBag_btraverse_nodup | ].

      intros.
      rewrite filter_InA; [ | solve [ apply eqke_equiv ].. | ].
      rewrite RangeTreeBag_btraverse_correct, RangeTreeBag_bcollect_correct.

      reflexivity.

      unfold Proper, respectful.
      unfold eq_key_elt, Raw.Proofs.PX.eqke.
      intros; eapply InRange_Proper; tauto.
    Qed.

    Lemma InList_ind_helper :
      forall (A : Type) (P : A -> Prop) (x : A) (xs : list A),
        (forall k, List.In k (x :: xs) -> P k) -> (P x /\ (forall k, List.In k xs -> P k)).
    Proof.
      intros; split; intros; eapply H; simpl; eauto.
    Qed.

    Theorem RangeTreeBag_BagFindCorrect :
      BagFindCorrect RangeTreeBag_RepInv RangeTreeBag_bfind RangeTreeBag_bfind_matcher RangeTreeBag_benumerate.
    Proof.
      hnf; intros.
      unfold RangeTreeBag_bfind, RangeTreeBag_benumerate, RangeTreeBag_bfind_matcher.
      unfold Values, elements; change (Raw.elements container) with (RangeTreeBag_bcollect container.(this)).
      unfold RangeTreeBag_RepInv in containerCorrect.
      destruct search_term as [ keys searchterm ].
      rewrite filter_and.
      rewrite !flatten_filter; simpl.
      pose proof (fun c k b => proj1 (RangeTreeBag_bcollect_correct c k b)) as rc_c.
      rewrite <- map_map with (l := (RangeTreeBag_btraverse container keys)) (f := snd) (g := fun bag => bfind bag searchterm).
      rewrite RangeTreeBag_btraverse_bcollect.
      remember (RangeTreeBag_bcollect container) as ls.
      specialize (rc_c container).
      rewrite <- Heqls in rc_c; clear Heqls.
      induction ls as [ | [ key bag ] ls' ]; simpl in *.
      reflexivity.
      assert (InA (eq_key_elt (elt:=BagType)) (key, bag) ((key, bag) :: ls')) as sc_c by
          (repeat constructor; apply X.eq_refl); apply rc_c in sc_c.
      assert (forall k b, InA (eq_key_elt (elt:=BagType)) (k, b) ls' -> MapsTo k b container) by
          (intros; eapply rc_c; eapply InA_cons_tl; eauto); specialize (IHls' H); clear H rc_c.
      specialize (containerCorrect key bag sc_c); destruct containerCorrect as [ cc_rev cc_eq ]; clear sc_c.
      pose proof (bfind_correct bag searchterm cc_rev) as bf_c; clear cc_rev.
      rewrite IHls'; clear IHls'.
      remember (benumerate bag) as xs; clear Heqxs.
      destruct (Range_InRange keys key) eqn: eqk; simpl.
      - f_equiv.
        rewrite <- bf_c; clear bf_c.
        induction xs as [ | item xs' ]; simpl.
        + constructor.
        + pose proof (InList_ind_helper _ cc_eq) as [ cc_eq_h cc_eq_t ]; clear cc_eq.
          specialize (IHxs' cc_eq_t); clear cc_eq_t.
          erewrite InRange_Proper; eauto. rewrite eqk.
          simpl. destruct (bfind_matcher searchterm item).
          apply Permutation_cons; try reflexivity. apply IHxs'.  apply IHxs'.
      - assert (List.filter (bfind_matcher searchterm) (List.filter (fun a : TItem => Range_InRange keys (projection a)) xs) = nil).
        rewrite filter_commute.
        apply filter_all_false; intros.
        rewrite InRange_Proper with (v' := key); auto.
        apply cc_eq. rewrite filter_In in H. tauto.
        rewrite H. reflexivity.
    Qed.

    Lemma InA_ind_helper :
      forall (P : TKey -> BagType -> Prop) (x : TKey) (y : BagType) (xs : list (TKey * BagType)),
        (forall k b, InA (eq_key_elt (elt:=BagType)) (k, b) ((x, y) :: xs) -> P k b) ->
        (P x y /\ (forall k b, InA (eq_key_elt (elt:=BagType)) (k, b) xs -> P k b)).
    Proof.
      intros; split; intros; eapply H.
      - eapply InA_cons_hd. reflexivity.
      - eapply InA_cons_tl. exact H0.
    Qed.

    Add Parametric Morphism {A B} (f : A -> list B) :
      (fold_right (fun a b => b ++ f a) [])
    with signature (@Permutation A ==> @Permutation B) as permutation_foldr_app.
    Proof.
      induction 1; auto.
      - simpl. rewrite IHPermutation. reflexivity.
      - simpl. rewrite <- !app_assoc. f_equiv. apply Permutation_app_comm.
      - rewrite IHPermutation1. exact IHPermutation2.
    Qed.

    Lemma snd_fold_right {A B A'} (f : B -> A * A' -> A) (g : B -> A' -> A') a a' ls
    : snd (fold_right (fun b aa' => (f b aa', g b (snd aa'))) (a, a') ls)
      = fold_right g a' ls.
    Proof.
      induction ls; simpl; trivial.
      rewrite IHls; reflexivity.
    Qed.

    Lemma InA_map_perm {A B} (eqB : B -> B -> Prop) (f : A -> B) (e : B) :
      forall ls ls', Permutation ls ls' -> (InA eqB e (List.map f ls) <-> InA eqB e (List.map f ls')).
    Proof.
      induction 1; intuition.
      - inversion H2; subst.
        apply InA_cons_hd. auto.
        simpl. apply InA_cons_tl. apply H0. auto.
      - inversion H2; subst.
        apply InA_cons_hd. auto.
        simpl. apply InA_cons_tl. apply H1. auto.
      - inversion H; subst; simpl.
        apply InA_cons_tl. apply InA_cons_hd. auto.
        inversion H1; subst; simpl.
        apply InA_cons_hd. auto.
        apply InA_cons_tl. apply InA_cons_tl. auto.
      - inversion H; subst; simpl.
        apply InA_cons_tl. apply InA_cons_hd. auto.
        inversion H1; subst; simpl.
        apply InA_cons_hd. auto.
        apply InA_cons_tl. apply InA_cons_tl. auto.
    Qed.

    Lemma InA_map_app {A B} (eqB : B -> B -> Prop) (f : A -> B) (e : B) :
      forall ls ls', InA eqB e (List.map f (ls ++ ls')) <-> InA eqB e (List.map f ls) \/ InA eqB e (List.map f ls').
    Proof.
      induction ls'; split; intros.
      - left. rewrite app_nil_r in H. auto.
      - destruct H.
        + rewrite app_nil_r. auto.
        + inversion H.
      - rewrite <- (InA_map_perm eqB f e (Permutation_middle ls ls' a)) in H.
        simpl in *. inversion H; subst.
        right. apply InA_cons_hd. assumption.
        rewrite IHls' in H1. inversion H1. left. assumption. right. apply InA_cons_tl. assumption.
      - rewrite <- (InA_map_perm eqB f e (Permutation_middle ls ls' a)).
        specialize (fun x => proj2 IHls' (or_introl x)).
        specialize (fun x => proj2 IHls' (or_intror x)).  intros.
        simpl in *. inversion H.
        apply InA_cons_tl. eauto.
        inversion H2; subst. apply InA_cons_hd. eauto. apply InA_cons_tl. eauto.
    Qed.

    Lemma map_if_filter_eq {A B} (f f' : A -> B) (dec : A -> bool) :
      forall ls, List.map (fun x => if dec x then f x else f' x) (List.filter dec ls) =
                 List.map (fun x => f x) (List.filter dec ls).
    Proof.
      induction ls. reflexivity. simpl. destruct (dec a) eqn: eq.
      simpl. rewrite eq. rewrite IHls. reflexivity.
      exact IHls.
    Qed.

    Lemma map_if_filter_neg {A B} (f f' : A -> B) (dec : A -> bool) :
      forall ls, List.map (fun x => if dec x then f x else f' x) (List.filter (fun x => negb (dec x)) ls) =
                 List.map (fun x => f' x) (List.filter (fun x => negb (dec x)) ls).
    Proof.
      induction ls. reflexivity. simpl. destruct (dec a) eqn: eq.
      simpl. exact IHls.
      simpl. rewrite IHls. rewrite eq. reflexivity.
    Qed.

    Lemma map_id {A} : forall (ls : list A), List.map id ls = ls.
    Proof.
      induction ls. reflexivity. simpl. rewrite IHls. unfold id. reflexivity.
    Qed.

    Lemma Permutation_partition {A} (f : A -> bool) :
      forall (ls : list A), Permutation ls ((List.filter f ls) ++ (List.filter (fun x => negb (f x)) ls)).
    Proof.
      intros. induction ls.
      - constructor.
      - simpl. destruct (f a); simpl.
        + constructor. assumption.
        + rewrite <- Permutation_middle. constructor. assumption.
    Qed.

    Lemma fst_if_eq {A B} :
      forall (dec : bool) (a : A) (b b' : B), fst (if dec then (a, b) else (a, b')) = a.
    Proof.
      destruct dec; eauto.
    Qed.

    Lemma InA_map_forall {A B} :
      forall eqA eqB (f : A -> B) ls ls',
        Equivalence eqA ->
        Equivalence eqB ->
        Proper (eqA ==> eqB) f ->
        (forall a, InA eqA a ls -> InA eqA a ls') ->
        (forall b, InA eqB b (List.map f ls) -> InA eqB b (List.map f ls')).
    Proof.
      intros eqA eqB f ls ls' eqvA eqvB proper Hfa b H.
      unfold Proper, respectful in proper.
      generalize dependent ls'. generalize dependent ls.
      induction ls; intros.
      - inversion H.
      - inversion H; clear H; subst.
        + specialize (Hfa a (InA_cons_hd ls (reflexivity _))). induction Hfa.
          * simpl. constructor. rewrite H1. f_equiv. assumption.
          * simpl. constructor 2. assumption.
        + eauto.
    Qed.

    Lemma InA_InRange_bcollect_btraverse :
      forall k v keys container,
       InA (eq_key_elt (elt:=BagType)) (k, v)
           (List.filter (fun x : TKey * BagType => Range_InRange keys (fst x))
                        (RangeTreeBag_bcollect container.(this))) <->
       InA (eq_key_elt (elt:=BagType)) (k, v)
           (List.filter (fun x : TKey * BagType => Range_InRange keys (fst x))
                        (RangeTreeBag_btraverse container.(this) keys)).
    Proof.
      intros k v keys container.
      rewrite !filter_InA; try solve [ apply eqke_equiv ].
      - rewrite RangeTreeBag_btraverse_correct, RangeTreeBag_bcollect_correct in *.
        intuition.
      - unfold Proper, respectful; intros; apply InRange_Proper.
        unfold eq_key_elt, Raw.Proofs.PX.eqke in *; intuition.
      - unfold Proper, respectful; intros; apply InRange_Proper.
        unfold eq_key_elt, Raw.Proofs.PX.eqke in *; intuition.
    Qed.

    Lemma RangeTreeBag_BagDeleteUpdateCorrect' :
      forall (container : RangeTreeBag) keys f,
        Permutation
          (List.map snd
                    (Raw.elements
                       (fold_right
                          (fun (y : TKey * BagType) (x : RangeTreeBag) =>
                             add (fst y) (f (snd y)) x) container
                          (RangeTreeBag_btraverse container keys))))
          (List.map snd
                    (List.map
                       (fun (key_bag : TKey * BagType) =>
                          if Range_InRange keys (fst key_bag) then
                            (fst key_bag, f (snd key_bag))
                          else
                            key_bag)
                    (RangeTreeBag_bcollect container))).
    Proof.
      intros; eapply Permutation_InA_cons; intros.
      {
        pose proof (RangeTreeBag_bcollect_nodup container).
        remember (RangeTreeBag_bcollect container) as ls. clear Heqls. induction ls.
        - constructor.
        - inversion H. subst. specialize (IHls H3). clear H3.
          simpl. constructor; eauto; intro.
          apply H2. clear H2 IHls H. destruct a. simpl in *. induction ls. inversion H0.
          simpl in *. inversion H0; subst.
          apply InA_cons_hd. unfold eq_key, Raw.Proofs.PX.eqk in *. clear H0 IHls. repeat find_if_inside; auto.
          apply InA_cons_tl. eauto.
      }
      { apply elements_3w. }
      rewrite (InA_map_perm _ _ _ (Permutation_partition (fun x => Range_InRange keys (fst x)) _)).
      rewrite InA_map_app.
      split; intro H.
      {
        rewrite map_if_filter_eq.
        assert (forall P Q R : Prop, (P -> R) -> P \/ Q -> R \/ Q) as E by tauto; eapply E; clear E.
        eapply @InA_map_forall with
            (eqA := eq_key_elt (elt:=BagType))
            (ls := (List.filter (fun x : TKey * BagType => Range_InRange keys (fst x)) (RangeTreeBag_btraverse container keys)));
          try solve [ apply eqke_equiv ].
        { unfold Proper, respectful, eq_key_elt, Raw.Proofs.PX.eqke; intros; destruct x; destruct y.
          unfold eq_key_elt, Raw.Proofs.PX.eqke in H0; destruct H0; simpl in *; subst.
          destruct (Range_InRange keys k0); tauto. }
        { pose proof (fun x => proj2 (InA_InRange_bcollect_btraverse (fst x) (snd x) keys container)).
          intro a. replace a with (fst a, snd a). generalize dependent a. exact H0. destruct a. reflexivity. }

        destruct (Range_InRange keys k) eqn: eq.
        - left.
          assert (InA (eq_key_elt (elt:=BagType)) (k, v)
                      (Raw.elements
                         (fold_right
                            (fun (y : TKey * BagType) (x : RangeTreeBag) =>
                               add (fst y) (f (snd y)) x) RangeTreeBag_bempty
                            (RangeTreeBag_btraverse container keys)))).
          {
            pose proof (fun k b => RangeTreeBag_btraverse_correct container keys k b) as Htraverse.
            pose proof (RangeTreeBag_btraverse_nodup container keys) as Htraverse_nodup.
            remember (RangeTreeBag_btraverse container keys) as ls. clear Heqls.
            generalize dependent container.
            induction ls; intros.
            - simpl in *. rewrite Raw.Proofs.elements_mapsto in H.
              specialize (proj2 (Htraverse k v) (conj H eq)). inversion 1.
            - destruct a. inversion Htraverse_nodup; subst.
              specialize (IHls H3 (remove t0 container)); clear H3.
              simpl in H. rewrite Raw.Proofs.elements_mapsto in *.
              pose proof (F.add_mapsto_iff). unfold MapsTo, add in H0. simpl in H0. apply H0 in H. clear H0.
              intuition. simpl. rewrite H1. apply Raw.Proofs.add_1. assumption.
              simpl. apply Raw.Proofs.add_2. intuition. rewrite <- Raw.Proofs.elements_mapsto. apply IHls.
              generalize H H1; clear. induction ls; intros; simpl in *.
              + destruct container. apply Raw.Proofs.remove_2; eauto.
              + pose proof (F.add_mapsto_iff). unfold MapsTo, add in H0. simpl in H0. apply H0 in H1. apply H0. clear H0. intuition.
              + setoid_rewrite remove_mapsto_iff. intuition.
                apply H2. symmetry in H3. eapply InA_eqke_eqk; eauto.
                eapply Htraverse. constructor 2. assumption.
                eapply Htraverse. constructor 2. eassumption.
                specialize (proj2 (Htraverse k0 b0) (conj H5 H4)). inversion 1; eauto.
          }
          clear H. rename H0 into H.
          pose proof (fun k b => proj1 (RangeTreeBag_btraverse_correct container keys k b)) as Htraverse.
          pose proof (RangeTreeBag_btraverse_nodup container keys) as Htraverse_nodup.
          remember (RangeTreeBag_btraverse container keys) as ls; clear Heqls.
          induction ls.
          + simpl in *. inversion H.
          + simpl in *. rewrite Raw.Proofs.elements_mapsto in H.
            pose proof (F.add_mapsto_iff). unfold MapsTo, add in H0. simpl in H0. apply H0 in H. clear H0.
            intuition.
            erewrite InRange_Proper; eauto 2. rewrite eq. simpl. apply InA_cons_hd.
            unfold eq_key_elt, Raw.Proofs.PX.eqke in *. intuition.
            find_if_inside; simpl. apply InA_cons_tl. apply IHls. rewrite Raw.Proofs.elements_mapsto. assumption.
            destruct a. apply InA_ind_helper in Htraverse. intuition. inversion Htraverse_nodup. auto.
            apply IHls. rewrite Raw.Proofs.elements_mapsto. assumption.
            destruct a. apply InA_ind_helper in Htraverse. intuition. inversion Htraverse_nodup. auto.
        - right.
          pose proof (fun k b => proj1 (RangeTreeBag_btraverse_correct container keys k b)) as Htraverse.
          remember (RangeTreeBag_btraverse container keys) as ls; clear Heqls.
          induction ls.
          + simpl in *. unfold RangeTreeBag_bcollect. induction (Raw.elements container). inversion H.
            simpl. inversion H; subst; clear H. destruct H1; simpl in *. symmetry in H.
            erewrite InRange_Proper; eauto 2. rewrite eq; simpl.
            erewrite InRange_Proper; eauto 2. rewrite eq; simpl. constructor. unfold eq_key_elt, Raw.Proofs.PX.eqke. intuition.
            find_if_inside. simpl. constructor 2. apply IHl. assumption.
            apply IHl. assumption.
          + simpl in H. apply IHls.
            rewrite Raw.Proofs.elements_mapsto in *.
            pose proof (F.add_mapsto_iff). unfold MapsTo, add in H0. simpl in H0. apply H0 in H. clear H0.
            intuition. specialize (Htraverse (fst a) (snd a)). destruct Htraverse.
            constructor. destruct a; reflexivity. erewrite InRange_Proper in H2; eauto 2. congruence.
            destruct a. apply InA_ind_helper in Htraverse. intuition.
      }
      {
        destruct H as [H | H].
        {
          rewrite map_if_filter_eq in H.
          pose proof (fun x => proj1 (InA_InRange_bcollect_btraverse (fst x) (snd x) keys container)) as InA_ct.
          eapply @InA_map_forall with
            (eqA := eq_key_elt (elt:=BagType))
            (ls' := (List.filter (fun x : TKey * BagType => Range_InRange keys (fst x)) (RangeTreeBag_btraverse container keys))) in H;
            try solve [ apply eqke_equiv ].
          pose proof (filter_map (fun x => Range_InRange keys (fst x))
                                 (fun x => (fst x, f (snd x))) (RangeTreeBag_btraverse container keys));
            simpl in H0; fold TKey in *; rewrite <- H0 in H; clear H0.
          rewrite filter_InA in H;
            try solve [ apply eqke_equiv ].
          - destruct H as [H_in H_range].
            pose proof (fun k b => proj1 (RangeTreeBag_btraverse_correct container keys k b)) as Htraverse.
            pose proof (RangeTreeBag_btraverse_nodup container keys) as Htraverse_nodup.
            remember (RangeTreeBag_btraverse container keys) as ls; clear Heqls InA_ct.
            induction ls as [ | [k' v'] ls'].
            + inversion H_in.
            + simpl in *; inversion H_in; clear H_in; subst.
              * rewrite Raw.Proofs.elements_mapsto in *.
                unfold eq_key_elt, Raw.Proofs.PX.eqke in H0. destruct H0. simpl in *. subst.
                apply Raw.Proofs.add_1; auto.
              * inversion Htraverse_nodup; subst.
                apply InA_ind_helper in Htraverse. destruct Htraverse as [Htraverse_s Htraverse_c].
                specialize (IHls' H0 Htraverse_c H3); clear Htraverse_c.
                destruct (X.eq_dec k  k').
                {
                  rewrite InA_Map in H0. destruct H0.
                  exfalso. apply H2. rewrite InA_alt.
                  exists x. destruct H.
                  unfold eq_key_elt, Raw.Proofs.PX.eqke in H. destruct H. simpl in *.
                  split. unfold eq_key, Raw.Proofs.PX.eqk. simpl. etransitivity; eauto.
                  assumption.
                }
                {
                  rewrite Raw.Proofs.elements_mapsto in *.
                  apply Raw.Proofs.add_2; auto.
                }
          - unfold Proper, respectful; intros; apply InRange_Proper.
            unfold eq_key_elt, Raw.Proofs.PX.eqke in *; intuition.
          - unfold Proper, respectful; intros.
            unfold eq_key_elt, Raw.Proofs.PX.eqke in *; intuition; simpl.
            f_equiv. assumption.
          - intro. replace a with ((fst a, snd a)). apply InA_ct.
            destruct a; auto.
        }
        {
          rewrite map_if_filter_neg, map_id, filter_InA in H;
          try solve [ apply eqke_equiv ].
          - destruct H as [H_in H_range].
            pose proof (fun k b => proj1 (RangeTreeBag_btraverse_correct container keys k b)) as Htraverse.
            remember (RangeTreeBag_btraverse container keys) as ls; clear Heqls.
            induction ls as [ | [k'' v''] ls'].
            + apply H_in.
            + apply RangeTreeBag_bcollect_correct in H_in.
              apply InA_ind_helper in Htraverse. destruct Htraverse as [Htraverse_s Htraverse_c].
              specialize (IHls' Htraverse_c); clear Htraverse_c. simpl in *.
              rewrite negb_true_iff in H_range.
              rewrite Raw.Proofs.elements_mapsto in *.
              apply Raw.Proofs.add_2.
              intro. apply InRange_Proper with (keys := keys) in H.
              rewrite H_range in H. destruct Htraverse_s. rewrite H1 in H. discriminate.
              assumption.
          - unfold Proper, respectful; intros; f_equal; apply InRange_Proper.
            unfold eq_key_elt, Raw.Proofs.PX.eqke in *; intuition.
        }
      }
    Qed.

    Theorem RangeTreeBag_BagDeleteCorrect :
      BagDeleteCorrect RangeTreeBag_RepInv RangeTreeBag_bfind RangeTreeBag_bfind_matcher
                       RangeTreeBag_benumerate RangeTreeBag_bdelete.
    Proof.
      hnf; intros.
      unfold RangeTreeBag_bdelete, RangeTreeBag_benumerate, RangeTreeBag_bfind_matcher.
      unfold Values, elements. change (Raw.elements container) with (RangeTreeBag_bcollect container.(this)).
      unfold RangeTreeBag_RepInv in containerCorrect.
      destruct search_term as [ keys searchterm ].
      simpl. split.
      {
        rewrite partition_filter_neq.
        rewrite !flatten_filter.

        remember (RangeTreeBag_btraverse container keys) as ls.
        pose proof (snd_fold_right
                      (fun (y : TKey * BagType) (x : list TItem * RangeTreeBag) =>
                         (fst x) ++ (fst (bdelete (snd y) searchterm)))
                      (fun (y : TKey * BagType) (x : RangeTreeBag) =>
                         add (fst y) (snd (bdelete (snd y) searchterm)) x)
                      [] container ls) as snd_foldr.
        fold RangeTreeBag in *; rewrite snd_foldr; clear snd_foldr; subst.
        rewrite RangeTreeBag_BagDeleteUpdateCorrect' with (f := fun x => snd (bdelete x searchterm)).

        pose proof (fun k b => proj1 (RangeTreeBag_bcollect_correct container k b)) as bcol_correct.
        remember (RangeTreeBag_bcollect container) as ls; clear Heqls.

        induction ls as [ | [ key bag ] ls' ]. reflexivity.
        apply InA_ind_helper in bcol_correct; destruct bcol_correct as [ bcol_hd bcol_tl ].
        simpl; rewrite (IHls' bcol_tl); clear bcol_tl IHls'.
        destruct (containerCorrect key bag bcol_hd) as [ cc_rep cc_eq ]; clear bcol_hd containerCorrect.
        f_equiv.

        pose proof (bdelete_correct bag searchterm cc_rep) as [ bdel_c _ ].
        remember (benumerate bag) as xs.
        destruct (Range_InRange keys key) eqn: eqk; simpl.
        {
          rewrite bdel_c, partition_filter_neq; clear bdel_c.
          clear Heqxs.
          induction xs. reflexivity. simpl.
          apply InList_ind_helper in cc_eq; destruct cc_eq as [ cc_eq_hd cc_eq_tl ].
          specialize (IHxs cc_eq_tl); clear cc_eq_tl.
          erewrite InRange_Proper; eauto; clear cc_eq_hd.
          rewrite eqk; simpl.
          destruct (negb (bfind_matcher searchterm a)); simpl.
          apply Permutation_cons; eauto. eauto.
        }
        {
          rewrite <- Heqxs; clear Heqxs. clear bdel_c.
          induction xs. reflexivity. simpl.
          apply InList_ind_helper in cc_eq; destruct cc_eq as [ cc_eq_hd cc_eq_tl ].
          specialize (IHxs cc_eq_tl); clear cc_eq_tl.
          erewrite InRange_Proper; eauto; clear cc_eq_hd.
          rewrite eqk; simpl. eauto.
        }
      }
      {
        rewrite partition_filter_eq.
        rewrite filter_and.
        rewrite !flatten_filter.

        remember (RangeTreeBag_btraverse container keys) as ls.
        pose proof (fst_fold_right
                      (fun (y : TKey * BagType) (x : list TItem) =>
                         x ++ (fst (bdelete (snd y) searchterm)))
                      (fun (y : TKey * BagType) (x : list TItem * RangeTreeBag) =>
                         add (fst y) (snd (bdelete (snd y) searchterm)) (snd x))
                      [] container ls) as fst_foldr.
        fold RangeTreeBag in *. rewrite fst_foldr. clear fst_foldr.

        pose proof (Common.fold_right_map
                      snd
                      (fun (y : BagType) (x : list TItem) => x ++ fst (bdelete y searchterm))
                      [] ls) as map_foldr; unfold compose in map_foldr.
        rewrite <- map_foldr; clear map_foldr.
        subst.
        rewrite RangeTreeBag_btraverse_bcollect.

        pose proof bdelete_correct as bdel_correct; unfold BagDeleteCorrect in bdel_correct.
        pose proof (fun key bag => proj1 (RangeTreeBag_bcollect_correct container key bag)) as bcol_correct.
        remember (RangeTreeBag_bcollect container) as ls; clear Heqls.

        induction ls as [ | [ key bag ] ls' ].
        constructor.
        apply InA_ind_helper in bcol_correct; destruct bcol_correct as [ bcol_hd bcol_tl ].
        specialize (IHls' bcol_tl); clear bcol_tl.
        specialize (containerCorrect _ _ bcol_hd); destruct containerCorrect as [ rep xeq ]; clear bcol_hd.
        simpl. rewrite <- IHls'. clear IHls'.
        specialize (bdel_correct bag searchterm rep); destruct bdel_correct as [ _ bdel_correct ].
        remember (benumerate bag) as xs. clear Heqxs.

        destruct (Range_InRange keys key) eqn: eqk; simpl.
        - rewrite Permutation_app_comm. f_equiv.
          rewrite bdel_correct. clear bdel_correct.
          rewrite partition_filter_eq.
          induction xs. reflexivity. simpl.
          pose proof (InList_ind_helper _ xeq) as [ xeq_h xeq_t ]; clear xeq.
          specialize (IHxs xeq_t); clear xeq_t.
          erewrite InRange_Proper; eauto.
          rewrite eqk. simpl. destruct (bfind_matcher searchterm a).
          constructor. assumption. assumption.
        - assert (List.filter (bfind_matcher searchterm) (List.filter (fun a : TItem => Range_InRange keys (projection a)) xs) = []).
          rewrite filter_commute.
          apply filter_all_false; intros.
          rewrite InRange_Proper with (v' := key); auto.
          apply xeq. rewrite filter_In in H. tauto.
          rewrite H. reflexivity.
      }
    Qed.

    Theorem RangeTreeBag_BagUpdateCorrect :
      BagUpdateCorrect RangeTreeBag_RepInv RangeTreeBag_ValidUpdate RangeTreeBag_bfind
                       RangeTreeBag_bfind_matcher RangeTreeBag_benumerate bupdate_transform RangeTreeBag_bupdate.
    Proof.
            hnf; intros.
      unfold RangeTreeBag_bupdate, RangeTreeBag_benumerate, RangeTreeBag_bfind_matcher.
      unfold Values, elements. change (Raw.elements container) with (RangeTreeBag_bcollect container.(this)).
      unfold RangeTreeBag_RepInv in containerCorrect.
      destruct search_term as [ keys searchterm ].
      simpl. split.
      {
        rewrite partition_filter_neq. rewrite partition_filter_eq.
        rewrite !flatten_filter.

        remember (RangeTreeBag_btraverse container keys) as ls.
        pose proof (snd_fold_right
                      (fun (y : TKey * BagType) (x : list TItem * RangeTreeBag) =>
                         (fst x) ++ (fst (bupdate (snd y) searchterm update_term)))
                      (fun (y : TKey * BagType) (x : RangeTreeBag) =>
                         add (fst y) (snd (bupdate (snd y) searchterm update_term)) x)
                      [] container ls) as snd_foldr.
        fold RangeTreeBag in *; rewrite snd_foldr; clear snd_foldr; subst.
        rewrite RangeTreeBag_BagDeleteUpdateCorrect' with (f := fun x => snd (bupdate x searchterm update_term)).

        pose proof (fun k b => proj1 (RangeTreeBag_bcollect_correct container k b)) as bcol_correct.
        remember (RangeTreeBag_bcollect container) as ls; clear Heqls.

        induction ls as [ | [ key bag ] ls' ]. reflexivity.
        apply InA_ind_helper in bcol_correct; destruct bcol_correct as [ bcol_hd bcol_tl ].
        simpl; rewrite (IHls' bcol_tl); clear bcol_tl IHls'.
        destruct (containerCorrect key bag bcol_hd) as [ cc_rep cc_eq ]; clear bcol_hd containerCorrect.
        rewrite app_assoc. rewrite map_app. rewrite app_assoc. f_equiv.
        assert (forall X (a b c : list X), Permutation ((a ++ b) ++ c) ((a ++ c) ++ b)) as E.
        {
          intros. induction a. simpl. apply Permutation_app_comm.
          simpl. constructor. auto.
        }
        rewrite E; clear E; f_equiv.
        destruct valid_update as [ valid_update1 valid_update2 ].

        pose proof (bupdate_correct bag searchterm update_term cc_rep valid_update1) as [ bupd_c _ ].
        remember (benumerate bag) as xs.
        destruct (Range_InRange keys key) eqn: eqk; simpl.
        {
          rewrite bupd_c, partition_filter_neq, partition_filter_eq; clear bupd_c.
          clear Heqxs.
          induction xs. reflexivity. simpl.
          apply InList_ind_helper in cc_eq; destruct cc_eq as [ cc_eq_hd cc_eq_tl ].
          specialize (IHxs cc_eq_tl); clear cc_eq_tl.
          erewrite InRange_Proper; eauto; clear cc_eq_hd.
          rewrite eqk; simpl.
          destruct (bfind_matcher searchterm a) eqn: eqb; simpl.
          assert (forall X x (a b : list X), Permutation (a ++ x :: b) (x :: a ++ b)) as E.
          {
            intros. induction a0. auto.
            simpl. rewrite perm_swap. auto.
          }
          rewrite !E. auto. auto.
        }
        {
          rewrite <- Heqxs; clear Heqxs. clear bupd_c.
          induction xs. reflexivity. simpl.
          apply InList_ind_helper in cc_eq; destruct cc_eq as [ cc_eq_hd cc_eq_tl ].
          specialize (IHxs cc_eq_tl); clear cc_eq_tl.
          erewrite InRange_Proper; eauto; clear cc_eq_hd.
          rewrite eqk; simpl. eauto.
        }
      }
      {
        rewrite partition_filter_eq.
        rewrite filter_and.
        rewrite !flatten_filter.

        remember (RangeTreeBag_btraverse container keys) as ls.
        pose proof (fst_fold_right
                      (fun (y : TKey * BagType) (x : list TItem) =>
                         x ++ (fst (bupdate (snd y) searchterm update_term)))
                      (fun (y : TKey * BagType) (x : list TItem * RangeTreeBag) =>
                         add (fst y) (snd (bupdate (snd y) searchterm update_term)) (snd x))
                      [] container ls) as fst_foldr.
        fold RangeTreeBag in *. rewrite fst_foldr. clear fst_foldr.

        pose proof (Common.fold_right_map
                      snd
                      (fun (y : BagType) (x : list TItem) => x ++ fst (bupdate y searchterm update_term))
                      [] ls) as map_foldr; unfold compose in map_foldr.
        rewrite <- map_foldr; clear map_foldr.
        subst.
        rewrite RangeTreeBag_btraverse_bcollect.

        pose proof bupdate_correct as bupd_correct; unfold BagUpdateCorrect in bupd_correct.
        pose proof (fun key bag => proj1 (RangeTreeBag_bcollect_correct container key bag)) as bcol_correct.
        remember (RangeTreeBag_bcollect container) as ls; clear Heqls.

        induction ls as [ | [ key bag ] ls' ].
        constructor.
        apply InA_ind_helper in bcol_correct; destruct bcol_correct as [ bcol_hd bcol_tl ].
        specialize (IHls' bcol_tl); clear bcol_tl.
        specialize (containerCorrect _ _ bcol_hd); destruct containerCorrect as [ rep xeq ]; clear bcol_hd.
        simpl. rewrite <- IHls'. clear IHls'.
        destruct valid_update as [ valid_update_1 valid_update_2 ].
        specialize (bupd_correct bag searchterm update_term rep valid_update_1); destruct bupd_correct as [ _ bdel_correct ].
        remember (benumerate bag) as xs. clear Heqxs.

        destruct (Range_InRange keys key) eqn: eqk; simpl.
        - rewrite Permutation_app_comm. f_equiv.
          rewrite bdel_correct. clear bdel_correct.
          rewrite partition_filter_eq.
          induction xs. reflexivity. simpl.
          pose proof (InList_ind_helper _ xeq) as [ xeq_h xeq_t ]; clear xeq.
          specialize (IHxs xeq_t); clear xeq_t.
          erewrite InRange_Proper; eauto.
          rewrite eqk. simpl. destruct (bfind_matcher searchterm a).
          constructor. assumption. assumption.
        - assert (List.filter (bfind_matcher searchterm) (List.filter (fun a : TItem => Range_InRange keys (projection a)) xs) = []).
          rewrite filter_commute.
          apply filter_all_false; intros.
          rewrite InRange_Proper with (v' := key); auto.
          apply xeq. rewrite filter_In in H. tauto.
          rewrite H. reflexivity.
      }
    Qed.
  End RangeTreeDefinition.

  Global Instance RangeTreeBagAsBag
         {BagType TItem SearchTermType UpdateTermType : Type}
         (TBag : Bag BagType TItem SearchTermType UpdateTermType)
         projection
  : Bag RangeTreeBag TItem (((option TKey) * (option TKey)) * (SearchTermType)) UpdateTermType :=
    {| bempty            := RangeTreeBag_bempty;
       bfind_matcher     := RangeTreeBag_bfind_matcher TBag projection;
       bupdate_transform := bupdate_transform;

       benumerate := RangeTreeBag_benumerate TBag;
       bfind      := RangeTreeBag_bfind TBag;
       binsert    := RangeTreeBag_binsert TBag projection;
       bcount     := RangeTreeBag_bcount TBag;
       bdelete    := RangeTreeBag_bdelete TBag;
       bupdate    := RangeTreeBag_bupdate TBag |}.

  Global Instance RangeTreeBagAsCorrectBag
         {BagType TItem SearchTermType UpdateTermType : Type}
         (TBag : Bag BagType TItem SearchTermType UpdateTermType)
         (RepInv : BagType -> Prop)
         (ValidUpdate : UpdateTermType -> Prop)
         (CorrectTBag : CorrectBag RepInv ValidUpdate TBag)
         projection
  : CorrectBag (RangeTreeBag_RepInv _ RepInv projection)
               (RangeTreeBag_ValidUpdate _ ValidUpdate projection)
               (RangeTreeBagAsBag TBag projection) :=
    { bempty_RepInv     := RangeTreeBag_Empty_RepInv TBag RepInv projection;
      binsert_RepInv    := RangeTreeBag_binsert_Preserves_RepInv CorrectTBag (projection := projection);
      bdelete_RepInv    := RangeTreeBag_bdelete_Preserves_RepInv CorrectTBag (projection := projection);
      bupdate_RepInv    := RangeTreeBag_bupdate_Preserves_RepInv CorrectTBag (projection := projection);

      binsert_enumerate := RangeTreeBag_BagInsertEnumerate CorrectTBag (projection := projection);
      benumerate_empty  := RangeTreeBag_BagEnumerateEmpty (TBag := TBag);
      bfind_correct     := RangeTreeBag_BagFindCorrect CorrectTBag (projection := projection);
      bcount_correct    := RangeTreeBag_BagCountCorrect CorrectTBag (projection := projection);
      bdelete_correct   := RangeTreeBag_BagDeleteCorrect CorrectTBag (projection := projection);
      bupdate_correct   := RangeTreeBag_BagUpdateCorrect CorrectTBag (projection := projection) }.
End RangeTreeBag.
