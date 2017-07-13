Require Export Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsInterface
        Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsProperties.
Require Import
        Coq.Arith.Peano_dec
        Coq.Structures.OrdersEx
        Coq.FSets.FMapInterface
        Coq.FSets.FMapFacts
        Coq.FSets.FMapAVL
        Coq.omega.Omega
        Fiat.Common
        Fiat.Common.String_as_OT
        Fiat.Common.List.ListFacts
        Fiat.Common.List.FlattenList
        Fiat.Common.SetEqProperties
        Fiat.Common.FMapExtensions
        Fiat.Common.List.PermutationFacts
        Fiat.QueryStructure.Specification.SearchTerms.ListInclusion.

Module InvertedIndexBag (MKeys : WS) (MValues : WSfun Nat_as_OT).

  Module Import MKeysFacts := WFacts_fun MKeys.E MKeys.
  Module Import MKeysProperties := WProperties_fun MKeys.E MKeys.
  Module Import MoreMKeysFacts := FMapExtensions_fun MKeys.E MKeys.

  Module Import MValuesFacts := WFacts_fun Nat_as_OT MValues.
  Module Import MValuesProperties := WProperties_fun Nat_as_OT MValues.
  Module Import MoreMValuesFacts := FMapExtensions_fun Nat_as_OT MValues.
  Module E := MKeys.E.

  Section InvertedIndexBagDefinitions.

    Definition IndexSearchTermT := list E.t.

    Context {TItem : Type}
            {UpdateTermType : Type}
            {Dec : DecideableEnsembles.Query_eq E.t}
            (bupdate_transform : UpdateTermType -> TItem -> TItem).

    Definition ItemSearchTermT := TItem -> bool.
    Definition ItemSearchTermMatcher : ItemSearchTermT -> TItem -> bool := id.

    Definition SearchTerm := prod IndexSearchTermT ItemSearchTermT.

    Context (projection: TItem -> IndexSearchTermT).

    Definition InvertedIndex_bfind_matcher
               (st : SearchTerm) (item: TItem) :=
      andb (if IncludedInA_dec (X_eq_dec := E.eq_dec) (fst st) (projection item) then true else false)
           (snd st item).

    Definition KeyMapT := MKeys.t (list nat).
    Definition ValuesMapT := MValues.t TItem.

    Record InvertedIndexMap :=
      { KeyMap : KeyMapT;
        ValuesMap : ValuesMapT;
        NumValues : nat }.

    Coercion KeyMap : InvertedIndexMap >-> KeyMapT.
    Coercion ValuesMap : InvertedIndexMap >-> ValuesMapT.
    (* Emptiness *)

    Definition InvertedIndex_bempty := {| KeyMap := MKeys.empty _;
                                          ValuesMap := MValues.empty _;
                                          NumValues := 0 |}.

    Definition InvertedIndex_benumerate
             (it : InvertedIndexMap)
    : list TItem := map snd (MValues.elements (ValuesMap it)).

    Fixpoint Find_MatchingIndexes
             (Mkey : KeyMapT)
             (st : IndexSearchTermT)
             (MValues : ValuesMapT)
    : ValuesMapT :=
      match st with
        | [ ] => MValues
        | i :: st' =>
          match MKeys.find i Mkey with
            | Some indexes =>
              Find_MatchingIndexes
                Mkey st'
                (filter (fun k _ => List.In_dec eq_nat_dec k (indexes)) MValues)

            | None => MValues.empty _
          end
      end.

    Definition InvertedIndex_bfind
             (it : InvertedIndexMap)
             (st : SearchTerm)
    : list TItem :=
      let matched_items := Find_MatchingIndexes it (fst st) it in
      List.filter (ItemSearchTermMatcher (snd st))
               (List.map snd (MValues.elements matched_items)).

    Definition InvertedIndex_bcount
               (it : InvertedIndexMap)
               (st : SearchTerm)
    : nat :=
      let matched_items := Find_MatchingIndexes it (fst st) it in
      fold_right (fun _ n => 1 + n)
                 0
                (List.filter (fun item => ItemSearchTermMatcher (snd st) (snd item))
                             (MValues.elements matched_items)).

    Definition UpdateKeyMap
               (index : nat)
               (key : E.t)
               (Mkey : KeyMapT)
      := match MKeys.find key Mkey with
           | Some l => MKeys.add key (index :: l) Mkey
           | _ => MKeys.add key [index] Mkey
         end.

    Definition InvertedIndex_binsert
             (it : InvertedIndexMap)
             (item : TItem) : InvertedIndexMap :=
      {| KeyMap :=
           (* Partition the existing key map to find the keys already in the map. *)
           let (includedKeys, notIncludedKeys) :=
               MKeysProperties.partition
                 (fun key _ =>
                    if (InA_dec E.eq_dec key (projection item))
                    then true
                    else false)
                 (KeyMap it) in
           (* Keys already in the map *)
           let oldKeys := map fst (MKeys.elements includedKeys) in
           (* Keys not already in the map *)
           let newKeys := List.filter (fun key : E.t =>
                                         if InA_dec E.eq_dec key oldKeys then
                                           false else true) (projection item) in
           MKeysProperties.update
             (* Add pointer for the old keys into the key map *)
             (MKeysProperties.update notIncludedKeys
                                     (MKeys.map (cons (NumValues it)) includedKeys))
             (* Add pointer for the new keys to the key map *)
             (fold_left (fun m k => MKeys.add k [NumValues it] m) newKeys (MKeys.empty _));

         (* Update Value Map *)
         ValuesMap := MValues.add (NumValues it) item (ValuesMap it);
         NumValues :=  S (NumValues it) |}.

    Definition InvertedIndex_bdelete
             (it : InvertedIndexMap)
             (st : SearchTerm)
    : (list TItem) * InvertedIndexMap :=
      let (matchedItems, unmatchedItems) :=
          MValuesProperties.partition (fun _ => InvertedIndex_bfind_matcher st) (ValuesMap it) in
      (map snd (MValues.elements matchedItems),
       {| KeyMap :=
            let matchedKeys := map fst (MValues.elements matchedItems) in
            MKeys.map (List.filter (fun key => if (List.In_dec eq_nat_dec key matchedKeys) then false else true)) (KeyMap it);
          ValuesMap := unmatchedItems;
          NumValues :=  NumValues it |}).

    Definition InvertedIndex_bupdate
             (it : InvertedIndexMap)
             (st : SearchTerm)
             (updateTerm : UpdateTermType)
    : (list TItem) * InvertedIndexMap :=
      let (matchedItems, unmatchedItems) :=
          MValuesProperties.partition (fun _ => InvertedIndex_bfind_matcher st) (ValuesMap it) in
      (map snd (MValues.elements matchedItems),
       {| KeyMap := KeyMap it;
          ValuesMap := MValuesProperties.update
                         (MValues.map (bupdate_transform updateTerm) matchedItems)
                         unmatchedItems;
          NumValues :=  NumValues it |}).

    Definition InvertedIndex_RepInv (it : InvertedIndexMap)
      := (forall key indexes,
            MKeys.MapsTo key indexes (KeyMap it) ->
            forall idx,
              List.In idx indexes
              -> exists item,
                   MValues.MapsTo idx item (ValuesMap it)
                   /\ InA E.eq key (projection item))
         /\ (forall idx item,
               MValues.MapsTo idx item (ValuesMap it)
               -> forall key,
                    InA E.eq key (projection item)
                    -> exists indexes,
                         MKeys.MapsTo key indexes (KeyMap it)
                         /\ List.In idx indexes)
         /\ forall idx,
             NumValues it <= idx
             -> ~ MValues.In idx (ValuesMap it).

    Definition InvertedIndex_ValidUpdate (update_term : UpdateTermType) :=
      forall item,
        projection item = projection (bupdate_transform update_term item).

    Lemma InvertedIndex_Empty_RepInv :
      InvertedIndex_RepInv (InvertedIndex_bempty).
    Proof.
      unfold InvertedIndex_RepInv; intros; repeat split; simpl; intros.
      - elimtype False; eapply MKeys.empty_1; eauto.
      - elimtype False; eapply MValues.empty_1; eauto.
      - intro H'; destruct H'; eapply MValues.empty_1; eauto.
    Qed.

    Ltac case_InA :=
       match goal with
       | H : context[InA_dec ?A ?B ?C] |- _ =>
            destruct (InA_dec A B C)
       | |- context[InA_dec ?A ?B ?C] =>
            destruct (InA_dec A B C)
          end.

    Lemma MKeys_elements_in_iff:
      forall (elt : Type) (m : MKeys.t elt) (x : MKeys.key),
        MKeys.In x m <->
        (InA E.eq x (map fst (MKeys.elements m))).
    Proof.
      unfold MKeys.In.
      setoid_rewrite MoreMKeysFacts.BasicFacts.elements_mapsto_iff.
      intros; induction (MKeys.elements m); split; simpl; intros.
      - destruct_ex; inversion H.
      - inversion H.
      - destruct_ex; inversion H; subst.
        constructor; apply H1.
        constructor 2; eapply IHl; eauto.
      - inversion H; subst.
        eexists (snd a); constructor; destruct a; split; simpl; eauto.
        apply IHl in H1; destruct_ex; eexists; eauto.
    Qed.

    Lemma inA_map :
      forall (A B : Type) eqA eqB (f : A -> B) (l : list A) (x : A),
        Proper (eqA ==> eqB) f
        -> InA eqA x l -> InA eqB (f x) (map f l).
    Proof.
      induction l; simpl; intros; inversion H0; subst.
      - econstructor; apply H; eauto.
      - econstructor 2; eauto.
    Qed.

    Lemma inA_map' :
      forall (A B : Type) eqA eqB (f : A -> B) (l : list A) (x : B),
        Reflexive eqA
        -> Proper (eqA ==> eqB) f
        -> InA eqB x (map f l)
        -> exists x',
            InA eqA x' l /\ eqB x (f x').
    Proof.
      induction l; simpl; intros; inversion H1; subst.
      - eexists; split; eauto.
      - destruct (IHl _ H H0 H3); intuition.
        eexists; eauto.
    Qed.

    Lemma FMap_fold_add_MapsTo_In
      : forall (Value : Type)
               (l : list (MKeys.key)) (k : MKeys.key)
               (v : Value) (bag' : MKeys.t Value) z,
        ~ InA E.eq k (map fst  (MKeys.elements bag'))
        -> (MKeys.MapsTo k v
          (fold_left
             (fun (a : MKeys.t Value) (p : MKeys.key) =>
              MKeys.add p z a) l bag') <->
         (InA E.eq k l /\ v = z)) .
    Proof.
      setoid_rewrite MoreMKeysFacts.BasicFacts.elements_mapsto_iff.
      induction l; simpl; split; intros; intuition.
      - elimtype False; apply H.
        eapply (inA_map (f := fst)) in H0; eauto using RelationPairs.fst_compat with typeclass_instances.
      - elimtype False; apply H.
        eapply (inA_map (f := fst)) in H0; eauto using RelationPairs.fst_compat with typeclass_instances.
      - inversion H1.
      - destruct (E.eq_dec k a).
        + eauto.
        + eapply IHl in H0; intuition.
          * apply H.
            let H1 := match goal with H1 : InA _ _ _ |- _ => constr:(H1) end in
            apply inA_map' with (eqA := @MKeys.eq_key_elt _) in H1;
              eauto using RelationPairs.fst_compat with typeclass_instances.
            destruct_ex; intuition.
            let H3 := match goal with H3 : E.eq _ _ |- _ => constr:(H3) end in
            rewrite H3.
            destruct x.
            let H2 := match goal with H2 : InA _ _ _ |- _ => constr:(H2) end in
            rewrite <- MoreMKeysFacts.BasicFacts.elements_mapsto_iff in H2.
            eapply inA_map with (eqA := @MKeys.eq_key_elt _);
              eauto using RelationPairs.fst_compat with typeclass_instances.
            let H2 := match goal with H2 : InA _ _ _ |- _ => constr:(H2) end in
            rewrite <- MoreMKeysFacts.BasicFacts.elements_mapsto_iff.
            let H2 := match goal with H2 : MKeys.MapsTo _ _ _ |- _ => constr:(H2) end in
            rewrite MoreMKeysFacts.BasicFacts.add_mapsto_iff in H2;
              intuition; subst.
            let H2 := match goal with H2 : MKeys.E.eq _ _ |- _ => constr:(H2) end in
            simpl in H3; rewrite H2 in n; intuition.
      - destruct (E.eq_dec k a).
        rewrite <- MoreMKeysFacts.BasicFacts.elements_mapsto_iff in H0.
        rewrite e in H0.
        assert (MKeys.MapsTo a z (MKeys.add a z bag')).
        apply MKeys.add_1; eauto.
        remember (MKeys.add a z bag') as bag''; clear Heqbag''.
        revert bag'' H1 H0; clear; induction l; simpl; intros.
        + eapply MoreMKeysFacts.BasicFacts.MapsTo_fun; eauto.
        + eapply (IHl (MKeys.add a0 z bag'')); eauto.
          eapply MoreMKeysFacts.BasicFacts.add_mapsto_iff; intuition.
          destruct (E.eq_dec a0 a); intuition.
        + eapply IHl with (bag' := MKeys.add a z bag'); eauto.
          intros.
          apply inA_map' with (eqA := @MKeys.eq_key_elt _) in H1;
            eauto using RelationPairs.fst_compat with typeclass_instances.
          destruct_ex; intuition.
          destruct x;
            rewrite <- MoreMKeysFacts.BasicFacts.elements_mapsto_iff in H2.
          rewrite MoreMKeysFacts.BasicFacts.add_mapsto_iff in H2;
            intuition; subst.
          simpl in *; rewrite H3 in n; intuition.
          apply H.
	rewrite MoreMKeysFacts.BasicFacts.elements_mapsto_iff in H4.
        eapply inA_map with (f := fst) in H4.
        simpl in *; rewrite H3; eauto.
        eauto using RelationPairs.fst_compat with typeclass_instances.
      - inversion H1; subst.
        + rewrite H3.
          rewrite <- MoreMKeysFacts.BasicFacts.elements_mapsto_iff.
          assert (MKeys.MapsTo a z (MKeys.add a z bag')).
          apply MKeys.add_1; eauto.
          remember (MKeys.add a z bag') as bag''; clear Heqbag''.
          revert bag'' H0; clear; induction l; simpl; intros; eauto.
          eapply IHl; eauto.
          destruct (E.eq_dec a a0).
          rewrite MoreMKeysFacts.BasicFacts.add_mapsto_iff; intuition.
          rewrite MoreMKeysFacts.BasicFacts.add_mapsto_iff; intuition.
        + destruct (E.eq_dec k a).
          * rewrite e.
            assert (MKeys.MapsTo a z (MKeys.add a z bag')).
            apply MKeys.add_1; eauto.
            remember (MKeys.add a z bag') as bag''; clear Heqbag''.
            generalize a bag'' H0; clear; induction l; simpl; intros.
            rewrite <- MoreMKeysFacts.BasicFacts.elements_mapsto_iff; eauto.
            eapply IHl; eauto.
            destruct (MKeys.E.eq_dec a0 a); intuition.
          * eapply IHl; eauto.
            intro.
            apply inA_map' with (eqA := @MKeys.eq_key_elt _) in H0;
            eauto using RelationPairs.fst_compat with typeclass_instances.
            destruct_ex; intuition.
            destruct x.
            rewrite <- MoreMKeysFacts.BasicFacts.elements_mapsto_iff in H2.
            apply H.
            rewrite MoreMKeysFacts.BasicFacts.add_mapsto_iff in H2;
              intuition.
            subst; simpl in *.
            rewrite H4, H2 in n; intuition.
            simpl in *.
            rewrite MoreMKeysFacts.BasicFacts.elements_mapsto_iff in H5.
            rewrite H4.
            eapply inA_map with (f := fst) in H5; simpl in *;
            eauto using RelationPairs.fst_compat with typeclass_instances.
    Qed.

    Lemma InvertedIndex_binsert_Preserves_RepInv :
      binsert_Preserves_RepInv InvertedIndex_RepInv InvertedIndex_binsert.
    Proof.
      unfold binsert_Preserves_RepInv, InvertedIndex_binsert, UpdateKeyMap;
      intros; repeat split; intros; simpl in *.
      rewrite MKeysProperties.update_mapsto_iff in H; intuition.
      - (* The key belongs to the inserted item and wasn't in the original key map. *)
        rewrite FMap_fold_add_MapsTo_In in H1.
        simpl in *; intuition; subst.
        simpl in *; intuition; subst.
        exists item; intuition eauto using MValues.add_1.
        eapply filter_InA; eauto with typeclass_instances.
        unfold Proper, respectful; intros.
        repeat case_InA; eauto.
        rewrite H0 in i; intuition.
        rewrite <- H0 in i; intuition.
        intro.
        apply MKeys_elements_in_iff in H; destruct H.
        eapply MKeys.empty_1; eauto.
      - rewrite MKeysProperties.update_mapsto_iff in H; intuition.
        + (* The key belongs to the inserted item and was in the original map.*)
          rewrite MoreMKeysFacts.BasicFacts.map_mapsto_iff in H1;
          destruct H1; intuition; subst; destruct H0; subst.
          exists item; intuition eauto using MValues.add_1.
          rewrite MKeysProperties.filter_iff in H3; intuition; eauto.
          case_InA; try discriminate; eauto.
          unfold Proper, respectful; intros.
          repeat case_InA; subst; eauto.
          rewrite H in i; intuition.
          rewrite <- H in i; intuition.
          destruct (eq_nat_dec idx (NumValues container)); subst.
          exists item; intuition eauto using MValues.add_1.
          rewrite MKeysProperties.filter_iff in H3; intuition; eauto.
          case_InA; try discriminate; eauto.
          unfold Proper, respectful; intros.
          repeat case_InA; subst; eauto.
          rewrite H0 in i; intuition.
          rewrite <- H0 in i; intuition.
          rewrite MKeysProperties.filter_iff in H3; intuition; eauto.
          case_InA; try discriminate; eauto.
          unfold InvertedIndex_RepInv in containerCorrect; intuition.
          destruct (H3 _ _ H0 _ H); intuition.
          eexists; split; eauto using MValues.add_2.
          unfold Proper, respectful; intros.
          repeat case_InA; subst; eauto.
          rewrite H0 in i; intuition.
          rewrite <- H0 in i; intuition.
        + rewrite MKeysProperties.filter_iff in H; intuition; eauto.
          case_InA; simpl in *; try discriminate.
          unfold InvertedIndex_RepInv in containerCorrect; intuition.
          destruct (H _ _ H1 _ H0); intuition.
          eexists; split; eauto.
          eapply MValues.add_2; eauto.
          intro; subst; eapply H7.
          reflexivity.
          eexists; eauto.
          unfold Proper, respectful; intros.
          repeat case_InA; subst; eauto.
          rewrite H1 in i; intuition.
          rewrite <- H1 in i; intuition.
      - rewrite MValuesFacts.add_mapsto_iff in H; intuition; subst.
        destruct (InA_dec E.eq_dec key
                    (let (includedKeys, notIncludedKeys) :=
               MKeysProperties.partition
                 (fun key _ =>
                    if (InA_dec E.eq_dec key (projection item0))
                    then true
                    else false)
                 (KeyMap container) in
           (* Keys already in the map *)
           let oldKeys := map fst (MKeys.elements includedKeys) in
           (* Keys not already in the map *)
           List.filter (fun key : E.t =>
                          if InA_dec E.eq_dec key oldKeys then
                            false else true) (projection item0)));
          simpl in *.
        + apply filter_InA in i; intuition.
          case_InA; try discriminate.
          eexists [NumValues container].
          rewrite MKeysProperties.update_mapsto_iff.
          split; simpl; eauto.
          left.
          eapply FMap_fold_add_MapsTo_In; intuition; eauto.
          apply MKeys_elements_in_iff in H2; destruct H2;
          eapply MKeys.empty_1; eauto.
          eapply filter_InA. eauto with typeclass_instances.
          unfold Proper, respectful; intros.
          repeat case_InA; subst; eauto.
          rewrite H2 in i; intuition.
          rewrite <- H2 in i; intuition.
          intuition; eauto.
          case_InA; eauto.
          unfold Proper, respectful; intros.
          repeat case_InA; subst; eauto.
          let H := match goal with H : E.eq _ _ |- _ => constr:(H) end in
          rewrite H in i0; intuition.
          let H := match goal with H : E.eq _ _ |- _ => constr:(H) end in
          rewrite <- H in i0; intuition.
        + assert (MKeys.In key (KeyMap container)).
          induction (projection item0); simpl in *.
          * inversion H0.
          * inversion H0; subst; eauto.
            case_InA.
            rewrite <- MKeys_elements_in_iff in i0.
            destruct i0.
            rewrite MKeysProperties.filter_iff in H; intuition; eauto.
            eexists x; rewrite H1; eauto.
            unfold Proper, respectful; intros.
            destruct (MoreMKeysFacts.BasicProperties.F.eq_dec x0 a);
            destruct (MoreMKeysFacts.BasicProperties.F.eq_dec y a); eauto.
            subst.
            rewrite H2 in e; intuition.
            repeat case_InA; eauto.
            rewrite H2 in i0; intuition.
            rewrite <- H2 in i0; intuition.
            elimtype False; apply n; econstructor; eauto.
            apply IHi; eauto.
            repeat case_InA.
            intro.
            apply filter_InA in H; intuition eauto with typeclass_instances.
            case_InA; try discriminate.
            apply n0.
            rewrite <- MKeys_elements_in_iff.
            rewrite <- MKeys_elements_in_iff in i0.
            destruct i0.
            rewrite MKeysProperties.filter_iff in H4; intuition; eauto.
            destruct (E.eq_dec key a).
            rewrite e; eauto.
            rewrite filter_InA in n; eauto with typeclass_instances.
            intuition.
            case_InA.
            apply MKeys_elements_in_iff in i0.
            destruct i0.
            rewrite MKeysProperties.filter_iff in H4; intuition.
            destruct (MoreMKeysFacts.BasicProperties.F.eq_dec key a).
            eexists.
            rewrite MKeysProperties.filter_iff; intuition; eauto.
            case_InA; eauto.
            rewrite e0 in H2; intuition.
            unfold Proper, respectful; intros.
            subst.
            repeat find_if_inside; try reflexivity.
            rewrite H4 in i0; intuition.
            rewrite H4 in i0; intuition.
            rewrite <- H4 in i0; intuition.
            rewrite <- H4 in i0; intuition.
            case_InA.
            eexists.
            rewrite MKeysProperties.filter_iff; intuition; eauto.
            discriminate.
            unfold Proper, respectful; intros.
            destruct (MoreMKeysFacts.BasicProperties.F.eq_dec x1 a);
              destruct (MoreMKeysFacts.BasicProperties.F.eq_dec y a);
              try reflexivity.
            rewrite H8 in e0; intuition.
            rewrite <- H8 in e0; intuition.
            repeat case_InA; try reflexivity.
            rewrite H8 in i1; intuition.
            rewrite <- H8 in i1; intuition.
            rewrite H8 in i0; intuition.
            rewrite <- H8 in i0; intuition.
            intuition.
            unfold Proper, respectful; intros.
            repeat case_InA; try reflexivity.
            rewrite H4 in i1; intuition.
            rewrite <- H4 in i1; intuition.
            rewrite H4 in i0; intuition.
            rewrite <- H4 in i0; intuition.
            rewrite filter_InA in n; eauto with typeclass_instances.
            intuition.
            case_InA.
            apply MKeys_elements_in_iff in i0.
            destruct i0.
            rewrite MKeysProperties.filter_iff in H4; intuition.
            destruct (MoreMKeysFacts.BasicProperties.F.eq_dec key a).
            intuition.
            case_InA.
            eexists.
            rewrite MKeysProperties.filter_iff; intuition; eauto.
            find_if_inside; eauto.
            unfold Proper, respectful; intros.
            subst.
            repeat find_if_inside; try reflexivity.
            rewrite H4 in i1; intuition.
            rewrite H4 in i1; intuition.
            rewrite <- H4 in i1; intuition.
            rewrite <- H4 in i1; intuition.
            discriminate.
            unfold Proper, respectful; intros.
            destruct (MoreMKeysFacts.BasicProperties.F.eq_dec x1 a);
              destruct (MoreMKeysFacts.BasicProperties.F.eq_dec y a);
              try reflexivity.
            rewrite H8 in e; intuition.
            rewrite <- H8 in e; intuition.
            repeat case_InA; try reflexivity.
            rewrite H8 in i1; intuition.
            rewrite <- H8 in i1; intuition.
            rewrite H8 in i0; intuition.
            rewrite <- H8 in i0; intuition.
            intuition.
            unfold Proper, respectful; intros.
            repeat case_InA; try reflexivity.
            rewrite H4 in i1; intuition.
            rewrite <- H4 in i1; intuition.
            rewrite H4 in i0; intuition.
            rewrite <- H4 in i0; intuition.
            unfold Proper, respectful; intros.
            destruct (MoreMKeysFacts.BasicProperties.F.eq_dec x0 a);
              destruct (MoreMKeysFacts.BasicProperties.F.eq_dec y a);
              try reflexivity.
            rewrite H5 in e; intuition.
            rewrite <- H5 in e; intuition.
            repeat case_InA; try reflexivity.
            rewrite H5 in i0; intuition.
            rewrite <- H5 in i0; intuition.
            unfold Proper, respectful; intros.
            repeat case_InA; try reflexivity.
            let H3 := match goal with H3 : E.eq _ _ |- _ => constr:(H3) end in
            rewrite H3 in i1; intuition.
            let H3 := match goal with H3 : E.eq _ _ |- _ => constr:(H3) end in
            rewrite <- H3 in i1; intuition.
            intro; eapply n.
            destruct (E.eq_dec key a).
            rewrite e; eauto.
            econstructor 2; eauto.
            apply filter_InA in H; intuition eauto with typeclass_instances.
            apply filter_InA.
            eauto with typeclass_instances.
            unfold Proper, respectful; intros.
            repeat case_InA; try reflexivity.
            rewrite H4 in i1; intuition.
            rewrite <- H4 in i1; intuition.
            rewrite H4 in i0; intuition.
            rewrite <- H4 in i0; intuition.
            intuition.
            repeat case_InA.
            discriminate.
            discriminate.
            rewrite <- MKeys_elements_in_iff in i0; destruct i0.
            rewrite MKeysProperties.filter_iff in H4.
            destruct H4.
            destruct (MoreMKeysFacts.BasicProperties.F.eq_dec key a).
            intuition.
            case_InA.
            destruct n2.
            rewrite <- MKeys_elements_in_iff.
            eexists; rewrite MKeysProperties.filter_iff.
            split; eauto.
            case_InA; eauto.
            unfold Proper, respectful; intros.
            repeat case_InA; try reflexivity.
            rewrite H6 in i1; intuition.
            rewrite <- H6 in i1; intuition.
            discriminate.
            unfold Proper, respectful; intros.
            destruct (MoreMKeysFacts.BasicProperties.F.eq_dec x0 a);
              destruct (MoreMKeysFacts.BasicProperties.F.eq_dec y a);
              try reflexivity.
            rewrite H5 in e; intuition.
            rewrite <- H5 in e; intuition.
            repeat case_InA; try reflexivity.
            rewrite H5 in i0; intuition.
            rewrite <- H5 in i0; intuition.
            reflexivity.
            unfold Proper, respectful; intros.
            repeat case_InA; try reflexivity.
            let H3 := match goal with H3 : E.eq _ _ |- _ => constr:(H3) end in
            rewrite H3 in i0; intuition.
            let H3 := match goal with H3 : E.eq _ _ |- _ => constr:(H3) end in
            rewrite <- H3 in i0; intuition.
          * unfold InvertedIndex_RepInv in containerCorrect; intuition.
            destruct H.
            eexists (NumValues container :: x); split; simpl; eauto.
            rewrite MKeysProperties.update_mapsto_iff; right.
            rewrite MKeysProperties.update_mapsto_iff; split.
            left.
            rewrite MoreMKeysFacts.BasicFacts.map_mapsto_iff;
              eexists; split; eauto.
            rewrite MKeysProperties.filter_iff.
            split; eauto.
            case_InA; eauto.
            unfold Proper, respectful; intros.
            repeat case_InA; eauto.
            rewrite H2 in i; intuition.
            rewrite <- H2 in i; intuition.
            unfold not; intros.
            apply n.
            eapply filter_InA; eauto with typeclass_instances.
            unfold Proper, respectful; intros.
            repeat case_InA; eauto.
            rewrite H5 in i; intuition.
            rewrite <- H5 in i; intuition.
            split; eauto.
            find_if_inside; try reflexivity.
            destruct H2; rewrite FMap_fold_add_MapsTo_In in H2.
            intuition.
            intro H'; apply MKeys_elements_in_iff in H'; destruct H';
            eapply MKeys.empty_1; eauto.
        + unfold InvertedIndex_RepInv in containerCorrect; intuition.
          destruct (H4 _ _ H2 _ H0); intuition.
          destruct (InA_dec E.eq_dec key (projection item)).
          * eexists (NumValues container :: x); split; simpl; eauto.
            rewrite MKeysProperties.update_mapsto_iff; right.
            rewrite MKeysProperties.update_mapsto_iff; split.
            left.
            rewrite MoreMKeysFacts.BasicFacts.map_mapsto_iff;
              eexists; split; eauto.
            rewrite MKeysProperties.filter_iff.
            split; eauto.
            case_InA; eauto.
            unfold Proper, respectful; intros.
            repeat case_InA; eauto.
            let H3 := match goal with H3 : E.eq _ _ |- _ => constr:(H3) end in
            rewrite H3 in i0; intuition.
            let H3 := match goal with H3 : E.eq _ _ |- _ => constr:(H3) end in
            rewrite <- H3 in i0; intuition.
            unfold not; intros.
            destruct H3; rewrite FMap_fold_add_MapsTo_In in H3.
            intuition.
            apply filter_InA in H8; intuition.
            case_InA; try discriminate.
            apply n.
            apply MKeys_elements_in_iff.
            eexists; apply MKeysProperties.filter_iff.
            unfold Proper, respectful; intros.
            repeat case_InA; try reflexivity.
            rewrite H8 in i0; intuition.
            rewrite <- H8 in i0; intuition.
            split; eauto.
            case_InA; eauto.
            unfold Proper, respectful; intros.
            repeat case_InA; try reflexivity.
            let H3 := match goal with H3 : E.eq _ _ |- _ => constr:(H3) end in
            rewrite H3 in i0; intuition.
            let H3 := match goal with H3 : E.eq _ _ |- _ => constr:(H3) end in
            rewrite <- H3 in i0; intuition.
            intro H'; apply MKeys_elements_in_iff in H'; destruct H';
            eapply MKeys.empty_1; eauto.
          * eexists x; split; simpl; eauto.
            rewrite MKeysProperties.update_mapsto_iff; right.
            rewrite MKeysProperties.update_mapsto_iff; split.
            right; split.
            apply MKeysProperties.filter_iff.
            unfold Proper, respectful; intros.
            repeat case_InA; try reflexivity.
            let H3 := match goal with H3 : E.eq _ _ |- _ => constr:(H3) end in
            rewrite H3 in i; intuition.
            let H3 := match goal with H3 : E.eq _ _ |- _ => constr:(H3) end in
            rewrite <- H3 in i; intuition.
            split; eauto.
            case_InA; intuition.
            intro H3; destruct H3;
            rewrite MoreMKeysFacts.BasicFacts.map_mapsto_iff in H3.
            destruct H3; intuition; subst.
            rewrite MKeysProperties.filter_iff in H9; intuition.
            case_InA; intuition.
            unfold Proper, respectful; intros.
            repeat case_InA; try reflexivity.
            let H3 := match goal with H3 : E.eq _ _ |- _ => constr:(H3) end in
            rewrite H3 in i; intuition.
            let H3 := match goal with H3 : E.eq _ _ |- _ => constr:(H3) end in
            rewrite <- H3 in i; intuition.
            intro; apply n.
            destruct H3; apply FMap_fold_add_MapsTo_In in H3; intuition.
            apply filter_InA in H8; intuition.
            unfold Proper, respectful; intros.
            repeat case_InA; try reflexivity.
            let H3 := match goal with H3 : E.eq _ _ |- _ => constr:(H3) end in
            rewrite H3 in i; intuition.
            let H3 := match goal with H3 : E.eq _ _ |- _ => constr:(H3) end in
            rewrite <- H3 in i; intuition.
            let H8 := match goal with H8 : InA _ _ _ |- _ => constr:(H8) end in
            apply MKeys_elements_in_iff in H8; destruct H8;
            eapply MKeys.empty_1; eauto.
      - inversion H; subst.
        unfold InvertedIndex_RepInv in *;
        intro H'; destruct H' as [x H'];
        rewrite add_mapsto_iff in H'; intuition.
        eapply (H3 (S (NumValues container))); eauto.
        eexists; eauto.
        unfold InvertedIndex_RepInv in *;
          intro H'; destruct H' as [x H'];
        rewrite add_mapsto_iff in H'; intuition.
        eapply (H4 (S m)); unfold MValues.In in *; eauto.
        omega.
        Grab Existential Variables.
        exact x0.
    Qed.

    Ltac case_In_dec :=
      match goal with
      | H : context[in_dec ?A ?B ?C] |- _ =>
        destruct (in_dec A B C)
      | |- context[in_dec ?A ?B ?C] =>
        destruct (in_dec A B C)
      end.

    Instance Proper_negb_InvertedIndex_bfind_matcher i
      : Proper (eq ==> eq ==> eq)
               (fun (_ : MValues.key) (e : TItem) =>
                  negb (InvertedIndex_bfind_matcher i e)).
    Proof.
      unfold Proper, respectful; intros; subst; eauto.
    Qed.

    Lemma MValues_elements_in_iff:
      forall (elt : Type) (m : MValues.t elt) (x : MValues.key),
        MValues.In x m <->
        (In x (map fst (MValues.elements m))).
    Proof.
      unfold MValues.In.
      setoid_rewrite MoreMValuesFacts.BasicFacts.elements_mapsto_iff.
      intros; induction (MValues.elements m); split; simpl; intros.
      - destruct_ex; inversion H.
      - inversion H.
      - destruct_ex; inversion H; subst.
        destruct H1; simpl in *; subst; eauto.
        right; eapply IHl; eauto.
      - inversion H; subst.
        eexists (snd a); constructor; destruct a; split; simpl; eauto.
        apply IHl in H0; destruct_ex; eexists; eauto.
    Qed.

    Lemma InvertedIndex_bdelete_Preserves_RepInv :
      bdelete_Preserves_RepInv InvertedIndex_RepInv InvertedIndex_bdelete.
    Proof.
      unfold bdelete_Preserves_RepInv, InvertedIndex_bdelete, InvertedIndex_RepInv; simpl.
      intros; destruct search_term; intuition.
      - rewrite MoreMKeysFacts.BasicFacts.map_mapsto_iff in H0;
        destruct H0; intuition; subst; apply filter_In in H3; intuition.
        case_In_dec; try discriminate.
        destruct (H _ _ H5 _ H0); intuition.
        eexists x0; split; eauto.
        apply filter_iff; intros; eauto with typeclass_instances.
        split; eauto.
        rewrite <- MValues_elements_in_iff in n.
        unfold InvertedIndex_bfind_matcher; simpl.
        destruct (IncludedInA_dec i (projection x0)); simpl; eauto.
        case_eq (i0 x0); intros; simpl; auto.
        destruct n; exists x0; rewrite filter_iff; eauto with typeclass_instances.
        intuition.
        unfold InvertedIndex_bfind_matcher; simpl.
        rewrite H3; destruct (IncludedInA_dec i (projection x0)); simpl; eauto.
      - rewrite filter_iff in H0; eauto with typeclass_instances; intuition.
        destruct (H1 _ _ H4 _ H3); intuition.
        eexists _; split.
        rewrite MoreMKeysFacts.BasicFacts.map_mapsto_iff.
        eexists _; split; eauto.
        apply filter_In; split; eauto.
        case_In_dec; eauto.
        rewrite <- MValues_elements_in_iff in i1; destruct i1.
        rewrite filter_iff in H0; eauto with typeclass_instances; intuition.
        rewrite (MoreMValuesFacts.BasicFacts.MapsTo_fun H8 H4) in *; rewrite H9 in H5;
        discriminate.
      - destruct H3.
        rewrite filter_iff in H3; eauto with typeclass_instances; intuition.
        eapply H2; eauto.
        eexists; eauto.
    Qed.

    Lemma InvertedIndex_bupdate_Preserves_RepInv :
      bupdate_Preserves_RepInv
        InvertedIndex_RepInv
        InvertedIndex_ValidUpdate
        InvertedIndex_bupdate.
    Proof.
      unfold bupdate_Preserves_RepInv, InvertedIndex_bupdate, InvertedIndex_RepInv; simpl.
      intros; destruct search_term; intuition.
      - destruct (H _ _ H0 _ H3); intuition.
        setoid_rewrite MValuesProperties.update_mapsto_iff.
        setoid_rewrite MoreMValuesFacts.BasicFacts.map_mapsto_iff.
        case_eq (InvertedIndex_bfind_matcher (i, i0) x); intros.
        + eexists _; split.
          right; split.
          eexists x; split; eauto.
          rewrite MValuesProperties.filter_iff; intuition; eauto.
          intro H'; destruct H' as [? H'];
          rewrite MValuesProperties.filter_iff in H'; intuition.
          rewrite (MoreMValuesFacts.BasicFacts.MapsTo_fun H7 H5) in *; rewrite H4 in H8;
          discriminate.
          unfold InvertedIndex_ValidUpdate in *.
          rewrite <- valid_update; eauto.
        + exists x; split; eauto.
          left; rewrite MValuesProperties.filter_iff; intuition.
          rewrite H4; reflexivity.
      - setoid_rewrite MValuesProperties.update_mapsto_iff in H0; intuition.
        + rewrite MValuesProperties.filter_iff in H4; intuition.
          destruct (H1 _ _ H0 _ H3); intuition; eauto.
        + setoid_rewrite MoreMValuesFacts.BasicFacts.map_mapsto_iff in H0;
          destruct_ex; intuition; subst.
          rewrite MValuesProperties.filter_iff in H6; intuition.
          rewrite <- valid_update in H3.
          destruct (H1 _ _ H0 _ H3); intuition; eauto.
      - destruct H3.
        setoid_rewrite MValuesProperties.update_mapsto_iff in H3;
          eauto with typeclass_instances; intuition.
        rewrite MValuesProperties.filter_iff in H4; intuition.
        eapply H2; unfold MValues.In; eauto.
        setoid_rewrite MoreMValuesFacts.BasicFacts.map_mapsto_iff in H3;
          destruct_ex; intuition; subst.
        rewrite MValuesProperties.filter_iff in H6; intuition.
        eapply H2; unfold MValues.In; eauto.
    Qed.

    Lemma InvertedIndex_BagEnumerateEmpty :
      BagEnumerateEmpty InvertedIndex_benumerate InvertedIndex_bempty.
    Proof.
      unfold BagEnumerateEmpty, InvertedIndex_benumerate,
      InvertedIndex_bempty; intros.
      simpl; intro.
      generalize H (elements_mapsto_iff (MValues.empty TItem)); clear.
      induction (MValues.elements (MValues.empty TItem)); simpl;
      intuition; subst.
      - destruct a; simpl in *.
        eapply MValues.empty_1; eapply H0.
        econstructor; eauto.
        reflexivity.
      - destruct a; simpl in *.
        eapply MValues.empty_1; eapply H0.
        econstructor; eauto.
        reflexivity.
    Qed.

    Lemma InvertedIndex_BagCountCorrect :
      BagCountCorrect InvertedIndex_RepInv InvertedIndex_bcount InvertedIndex_bfind.
    Proof.
      unfold BagCountCorrect, InvertedIndex_bcount, InvertedIndex_bfind;
      intros.
      induction (MValues.elements
                   (Find_MatchingIndexes container (fst search_term) container));
        simpl; eauto.
      find_if_inside; simpl; eauto.
    Qed.

    Lemma NoDupA_filter elt eq_elt
    : forall (f : elt -> bool) l,
        NoDupA eq_elt l
        -> NoDupA eq_elt (List.filter f l).
    Proof.
      induction l; intros; eauto; inversion H; subst.
      simpl; find_if_inside; eauto.
      econstructor; eauto.
      intro; eapply H2.
      revert H0; clear; induction l; simpl; intros.
      - inversion H0; subst.
      - find_if_inside.
        + inversion H0; subst.
          * econstructor; eauto.
          * econstructor 2; eauto.
        + econstructor 2; eauto.
    Qed.

    Lemma Proper_ItemSearchTermMatcher
          search_term
    : Proper (eq ==> eq ==> eq)
             (fun (_ : MValues.key) (item : TItem) =>
                ItemSearchTermMatcher search_term item).
    Proof.
      unfold Proper, respectful, ItemSearchTermMatcher; intros; subst;
      reflexivity.
    Qed.

    Lemma Proper_bfind_matcher
          (search_term : SearchTerm)
    : Proper (eq ==> eq ==> eq)
             (fun (_ : MValues.key) (item : TItem) =>
                andb
                  (if IncludedInA_dec (X_eq_dec := E.eq_dec) (fst search_term) (projection item)
                   then true
                   else false)
                  (ItemSearchTermMatcher (snd search_term) item)) .
    Proof.
      unfold Proper, respectful, ItemSearchTermMatcher; intros; subst;
      reflexivity.
    Qed.

    Lemma Find_MatchingIndexesOK_Subset
      : forall
        (st : IndexSearchTermT)
        (MKey : KeyMapT)
        (MValues : ValuesMapT)
        item idx,
        MValues.MapsTo idx item (Find_MatchingIndexes MKey st MValues) ->
        MValues.MapsTo idx item MValues.
    Proof.
      induction st; simpl; unfold inclA; intros; intuition.
      - case_eq (MKeys.find a MKey); intros; rewrite H0 in H.
        + apply IHst in H.
          rewrite MValuesProperties.filter_iff in H; intuition.
        + apply MValues.empty_1 in H; intuition.
    Qed.

    Add Parametric Morphism MKey st
      : (Find_MatchingIndexes MKey st)
        with signature (MValues.Equal ==> MValues.Equal)
          as Find_MatchingIndexes_Equal.
    Proof.
      unfold MValues.Equal.
      induction st; simpl; eauto.
      destruct (MKeys.find a MKey); eauto.
      intros; eapply IHst.
      intros; apply Equal_mapsto_iff.
      setoid_rewrite Equal_mapsto_iff in H.
      intros; rewrite !MValuesProperties.filter_iff by eauto with typeclass_instances.
      intuition; eapply H; eauto.
    Qed.

    Lemma Equal_filter_filter
      : forall f g (MValues : ValuesMapT),
        MValues.Equal (filter f (filter g MValues))
                      (filter (fun k x => f k x && g k x) MValues).
    Proof.
      intros; eapply Equal_mapsto_iff.
      intros; rewrite !MValuesProperties.filter_iff
        by eauto with typeclass_instances.
      intuition; destruct (f k e); destruct (g k e); eauto.
    Qed.

    Lemma Find_MatchingIndexesOK_InclA
      : forall
        (st : IndexSearchTermT)
        (MKey : KeyMapT)
        (MValues : ValuesMapT),
        (forall key indexes,
            MKeys.MapsTo key indexes MKey ->
            forall idx,
              List.In idx indexes
              -> exists item,
                MValues.MapsTo idx item MValues
                /\ InA E.eq key (projection item))
        -> forall item idx,
        MValues.MapsTo idx item (Find_MatchingIndexes MKey st MValues) ->
        inclA E.eq st (projection item).
    Proof.
      induction st; simpl; unfold inclA; intros; intuition.
      - inversion H1.
      - case_eq (MKeys.find a MKey); intros; rewrite H2 in H0.
        + inversion H1; subst.
          * rewrite H4; pose proof (Find_MatchingIndexesOK_Subset _ _ _ H0) as H'.
            rewrite MValuesProperties.filter_iff in H'; intuition.
            apply MKeys.find_2 in H2.
            destruct (H _ _ H2 idx); intuition.
            destruct (in_dec eq_nat_dec idx l); simpl in *; congruence.
            rewrite <- (MoreMValuesFacts.BasicFacts.MapsTo_fun H7 H3); eauto.
          * destruct (E.eq_dec x a).
            rewrite e; pose proof (Find_MatchingIndexesOK_Subset _ _ _ H0) as H'.
            rewrite MValuesProperties.filter_iff in H'; intuition.
            apply MKeys.find_2 in H2.
            destruct (H _ _ H2 idx); intuition.
            destruct (in_dec eq_nat_dec idx l); simpl in *; congruence.
            rewrite <- (MoreMValuesFacts.BasicFacts.MapsTo_fun H7 H3); eauto.
            apply MKeys.find_2 in H2.
            apply (IHst _ _ H item idx); eauto.
            generalize H0.
            remember (fun (k : MValues.key) (_ : TItem) => bool_of_sumbool (in_dec eq_nat_dec k l)) as f.
            unfold not in f; setoid_rewrite <- Heqf.
            generalize MValues f; clear -projection; induction st; simpl; intros; eauto.
            rewrite MValuesProperties.filter_iff in H; intuition.
            destruct (MKeys.find a MKey); simpl in *.
            setoid_rewrite Equal_filter_filter in H.
            eapply (IHst _ f).
            setoid_rewrite Equal_filter_filter.
            eapply Equal_mapsto_iff; eauto.
            repeat f_equiv.
            repeat (apply functional_extensionality; intros).
            apply andb_comm.
            eauto.
        + apply MValues.empty_1 in H0; intuition.
    Qed.

    Lemma Find_MatchingIndexesOK_Subset'
    : forall
        (st : IndexSearchTermT)
        (MKey : KeyMapT)
        (MValues : ValuesMapT),
        (forall key indexes,
           MKeys.MapsTo key indexes MKey ->
            forall idx,
              List.In idx indexes
              -> exists item,
                   MValues.MapsTo idx item MValues
                   /\ InA E.eq key (projection item))
        -> (forall idx item,
               MValues.MapsTo idx item MValues
               -> forall key,
                    InA E.eq key (projection item)
                    -> exists indexes,
                         MKeys.MapsTo key indexes MKey
                         /\ List.In idx indexes)
        -> forall item idx,
            MValues.MapsTo idx item MValues ->
            inclA E.eq st (projection item) ->
            MValues.MapsTo idx item (Find_MatchingIndexes MKey st MValues).
    Proof.
      induction st; simpl; intros; eauto.
      case_eq (MKeys.find a MKey); intros.
      - apply MKeys.find_2 in H3.
        assert (InA E.eq a (projection item)) by
            (eapply H2; econstructor; reflexivity).
        destruct (H0 _ _ H1 _ H4); intuition.
        rewrite <- (MoreMKeysFacts.BasicFacts.MapsTo_fun H6 H3); eauto.
        eapply IHst in H1; eauto.
        revert H7 H1; clear -projection;
        remember (fun (k : MValues.key) (_ : TItem) => bool_of_sumbool (in_dec eq_nat_dec k x)) as f; unfold not in Heqf; rewrite <- Heqf.
        intro.
        assert (forall v, f idx v = true) by
            (rewrite Heqf; destruct (in_dec eq_nat_dec idx x); simpl; eauto).
        generalize MValues f H; clear -projection.
        induction st.
        + simpl; intros.
          rewrite MValuesProperties.filter_iff; intuition.
        + simpl; intros.
          destruct (MKeys.find a MKey).
          * eapply (IHst _ f) in H1; eauto.
            setoid_rewrite Equal_filter_filter.
            setoid_rewrite Equal_filter_filter in H1.
            eapply Equal_mapsto_iff; eauto.
            repeat f_equiv.
            repeat (apply functional_extensionality; intros).
            apply andb_comm.
          * eauto.
        + unfold inclA; intros; apply H2; econstructor 2; eauto.
      - assert (InA E.eq a (projection item)) by
            (eapply H2; econstructor; reflexivity).
        destruct (H0 _ _ H1 _ H4); intuition.
        eapply MKeys.find_1 in H6; congruence.
    Qed.

    Lemma Find_MatchingIndexesOK_Subset_iff
    : forall
        (st : IndexSearchTermT)
        (MKey : KeyMapT)
        (MValues : ValuesMapT),
        (forall key indexes,
           MKeys.MapsTo key indexes MKey ->
            forall idx,
              List.In idx indexes
              -> exists item,
                   MValues.MapsTo idx item MValues
                   /\ InA E.eq key (projection item))
        -> (forall idx item,
               MValues.MapsTo idx item MValues
               -> forall key,
                    InA E.eq key (projection item)
                    -> exists indexes,
                         MKeys.MapsTo key indexes MKey
                         /\ List.In idx indexes)
        -> forall item idx,
            MValues.MapsTo idx item (Find_MatchingIndexes MKey st MValues)
            <-> MValues.MapsTo idx item MValues
                /\ inclA E.eq st (projection item).
    Proof.
      repeat split; intros.
      eapply Find_MatchingIndexesOK_Subset; eauto.
      eapply Find_MatchingIndexesOK_InclA; eauto.
      intuition;
        eapply Find_MatchingIndexesOK_Subset'; eauto.
    Qed.



      Lemma Not_inclA_NIn :
      forall l l',
        ~ inclA E.eq l l' ->
        exists e, InA E.eq e l /\ ~ InA E.eq e l'.
    Proof.
      induction l; simpl; intros.
      - elimtype False; eapply H; unfold inclA; intros; inversion H0.
      - unfold inclA in *.
        destruct (InA_dec E.eq_dec a l').
        + destruct (IHl l').
          intro; apply H; intros; inversion H1; subst; eauto.
          rewrite <- H3 in i; eauto.
          split_and.
          exists x; eauto.
        + exists a; eauto.
    Qed.

    Lemma InvertedIndex_BagFindCorrect :
      BagFindCorrect InvertedIndex_RepInv InvertedIndex_bfind InvertedIndex_bfind_matcher InvertedIndex_benumerate.
    Proof.
      unfold BagFindCorrect, InvertedIndex_bfind_matcher,
      InvertedIndex_bfind, InvertedIndex_benumerate;
      intros.
      unfold InvertedIndex_RepInv in *; intuition.
      rewrite !filter_map.
      rewrite <- Permutation_filter_elements
      with (f := fun (k : MValues.key) (item : TItem) =>
                   andb (if IncludedInA_dec (X_eq_dec := E.eq_dec) (fst search_term) (projection item)
                         then true
                         else false)
                        (ItemSearchTermMatcher (snd search_term) item));
        eauto using Proper_bfind_matcher.
      rewrite <- Permutation_filter_elements
      with (f := fun (k : MValues.key) (item : TItem) =>
                   ItemSearchTermMatcher (snd search_term) item);
        eauto using Proper_ItemSearchTermMatcher.
      eapply MoreMValuesFacts.Permutation_InA_cons;
      eauto using NoDupA_filter, MValues.elements_3w.
      intros; rewrite <- !elements_mapsto_iff.
      rewrite !filter_iff
        by (eauto using Proper_bfind_matcher,
            Proper_ItemSearchTermMatcher).
      intuition.
      - try find_if_inside; eauto.
        eapply Find_MatchingIndexesOK_Subset_iff; eauto.
        discriminate.
      - find_if_inside; eauto; discriminate.
      - eapply Find_MatchingIndexesOK_Subset_iff; eauto.
      - find_if_inside; eauto.
        apply Not_inclA_NIn in n; destruct n; split_and.
        eapply Find_MatchingIndexesOK_Subset_iff in H3; intuition eauto.
    Qed.

      Corollary InvertedIndex_BagInsertEnumerate :
      BagInsertEnumerate InvertedIndex_RepInv InvertedIndex_benumerate InvertedIndex_binsert.
    Proof.
      unfold BagInsertEnumerate, InvertedIndex_RepInv,
      InvertedIndex_binsert, InvertedIndex_benumerate;
      intros; simpl.
      eapply (@MoreMValuesFacts.Permutation_InA_cons
                _
                ((NumValues container, inserted) :: MValues.elements (ValuesMap container))).
      - econstructor; simpl; eauto using MValues.elements_3w.
        intuition.
        pose proof (@MValues.elements_2 _ (ValuesMap container) (NumValues container)) .
        eapply H3; revert H H1; clear; induction (MValues.elements (ValuesMap container)); simpl; intros; inversion H; subst; eauto.
        destruct a as [k v]; eexists v; eapply H1; econstructor; simpl.
        econstructor; simpl; eauto.
      - eauto using MValues.elements_3w.
      - intros; rewrite <- !elements_mapsto_iff, add_mapsto_iff; intuition;
        subst.
        + econstructor; reflexivity.
        + econstructor 2; rewrite <- elements_mapsto_iff; eauto.
        + inversion H0; subst; [left | right]; intuition.
          destruct H4; simpl in *; subst; eauto.
          destruct H4; simpl in *; subst; eauto.
          rewrite <- elements_mapsto_iff in H4; subst.
          eapply H2; eauto; eexists; eauto.
          rewrite <- elements_mapsto_iff in H4; eauto.
    Qed.

    Lemma Permutation_elements_filter B :
      forall (f : B -> bool) container,
        Permutation (map snd
                         (MValues.elements
                            (MValuesProperties.filter (fun _ => f) container)))
                    (map snd (List.filter (fun kv => f (snd kv))(MValues.elements container))).
    Proof.
      intros.
      intros; eapply Permutation_InA_cons.
      eapply NoDupA_filter; eapply MValues.elements_3w.
      eapply MValues.elements_3w.
      intros.
      rewrite filter_InA, <- !elements_mapsto_iff, MValuesProperties.filter_iff;
        eauto with typeclass_instances.
      unfold Proper, respectful; intros.
      destruct H; rewrite H0; reflexivity.
    Qed.

    Lemma Permutation_elements_map B C :
      forall (f : B -> C) container,
        Permutation (map snd
                         (MValues.elements
                            (MValues.map f container)))
                    (map snd (List.map (fun kv => (fst kv, f (snd kv))) (MValues.elements container))).
    Proof.
      intros.
      intros; eapply Permutation_InA_cons.
      - generalize (MValues.elements_3w container).
        induction (MValues.elements container); simpl; constructor.
        + inversion H; subst; intro; apply H2.
          revert H0; clear; induction l; simpl; intros; inversion H0; subst.
          * econstructor; eapply H1.
          * econstructor 2; eauto.
        + inversion H; subst; eauto.
      - eapply MValues.elements_3w.
      - intros.
        rewrite <- !elements_mapsto_iff, map_mapsto_iff.
        setoid_rewrite elements_mapsto_iff.
        induction (MValues.elements container); simpl; intuition.
        + destruct_ex; intuition; inversion H1.
        + inversion H.
        + destruct_ex; intuition; subst; inversion H3; subst.
          * simpl; econstructor 1.
            destruct H2; split; simpl in *; f_equal; eauto.
          * econstructor 2; eauto.
        + simpl in *; inversion H1; subst.
          *  eexists b; split.
             eapply H3.
             econstructor; destruct H3; split; simpl in *; eauto.
          * apply H0 in H3; destruct_ex; intuition; eexists; eauto.
    Qed.

    Lemma Permutation_elements_update B :
      forall m1 m2,
        (forall x, InA (@MValues.eq_key _) x (MValues.elements m1)
                   -> ~ InA (@MValues.eq_key _) x (MValues.elements m2))
        -> Permutation (map snd
                         (MValues.elements
                            (MValuesProperties.update (elt := B) m1 m2)))
                    (map snd (MValues.elements m1) ++ map snd (MValues.elements m2)).
    Proof.
      intros; rewrite <- map_app; apply Permutation_InA_cons.
      eapply NoDupA_app; eauto using MValues.elements_3w with typeclass_instances.
      eapply MValues.elements_3w.
      intros.
      rewrite InA_app_iff, <- !elements_mapsto_iff by (eauto with typeclass_instances).
      rewrite MValuesProperties.update_mapsto_iff; intuition.
      right; intuition.
      rewrite elements_mapsto_iff in H1; eapply H with (x := (k, v)); eauto.
      revert H1; clear; induction (MValues.elements m1); intros; inversion H1; subst; eauto.
      destruct H0; constructor; eauto.
      destruct H0; rewrite elements_mapsto_iff in H0; revert H0; clear;
      induction (MValues.elements m2); intros; inversion H0; subst; eauto.
      destruct H1; simpl in *; constructor; eauto.
    Qed.

    Lemma Permutation_filter_map_snd A B :
      forall (f : B -> bool) (l : list (A * B)),
        Permutation (map snd (List.filter (fun kv => f (snd kv)) l))
                    (List.filter f (map snd l)).
    Proof.
      intros.
      induction l; simpl; eauto.
      find_if_inside; simpl; eauto.
    Qed.

    Lemma Permutation_map_snd_swap A B C:
      forall (f : B -> C) (l : list (A * B)),
        Permutation (map snd (map (fun kv => (fst kv, f (snd kv))) l))
                    (map f (map snd l)).
    Proof.
      intros.
      induction l; simpl; eauto.
    Qed.

    Lemma InvertedIndex_BagDeleteCorrect :
      BagDeleteCorrect InvertedIndex_RepInv InvertedIndex_bfind
                       InvertedIndex_bfind_matcher
                       InvertedIndex_benumerate InvertedIndex_bdelete.
    Proof.
      unfold BagDeleteCorrect, InvertedIndex_bdelete, InvertedIndex_benumerate;
      simpl in *; intros; split.
      - rewrite Permutation_elements_filter.
        rewrite Permutation_filter_map_snd with (f := fun v => negb (_ v)).
        induction (MValues.elements (ValuesMap container)); simpl; eauto.
        rewrite <- partition_filter_neq.
        case_eq (InvertedIndex_bfind_matcher search_term (snd a)); intros; simpl in *.
        case_eq (List.partition (InvertedIndex_bfind_matcher search_term)
                                (map snd l)); intros; simpl; eauto.
        case_eq (List.partition (InvertedIndex_bfind_matcher search_term)
                                (map snd l)); intros; simpl; eauto.
      - rewrite Permutation_elements_filter, Permutation_filter_map_snd.
        induction (MValues.elements (ValuesMap container)); simpl; eauto.
        rewrite <- partition_filter_eq.
        case_eq (InvertedIndex_bfind_matcher search_term (snd a)); intros; simpl in *.
        case_eq (List.partition (InvertedIndex_bfind_matcher search_term)
                                (map snd l)); intros; simpl; eauto.
        case_eq (List.partition (InvertedIndex_bfind_matcher search_term)
                                (map snd l)); intros; simpl; eauto.
    Qed.

    Lemma InA_eq_key_eq_key_elt
      : forall k t l,
        InA (MValues.eq_key (elt:=TItem)) (k, t) l <->
        exists v, InA (@MValues.eq_key_elt _) (k, v) l.
    Proof.
      induction l; simpl; split; intros.
      - inversion H.
      - destruct_ex; inversion H.
      - inversion H; subst.
        + exists (snd a); destruct a; econstructor; simpl in *.
          split; simpl; eauto.
        + rewrite IHl in H1; destruct_ex;
          eexists; econstructor 2; eauto.
      - destruct_ex; inversion H; subst.
        + constructor; apply H1.
        + econstructor 2; apply IHl; eauto.
    Qed.

      Lemma InvertedIndex_BagUpdateCorrect :
      BagUpdateCorrect InvertedIndex_RepInv InvertedIndex_ValidUpdate
                       InvertedIndex_bfind InvertedIndex_bfind_matcher
                       InvertedIndex_benumerate
                       bupdate_transform InvertedIndex_bupdate.
    Proof.
      unfold BagUpdateCorrect, InvertedIndex_bupdate, InvertedIndex_benumerate;
      simpl in *; intros; split.
      - rewrite Permutation_elements_update, Permutation_elements_filter,
        Permutation_filter_map_snd with (f := fun v => negb (_ v)).
        rewrite Permutation_app_swap.
        f_equiv.
        + induction (MValues.elements (ValuesMap container)); simpl; eauto.
          rewrite <- partition_filter_neq.
          case_eq (InvertedIndex_bfind_matcher search_term (snd a)); intros; simpl in *.
          case_eq (List.partition (InvertedIndex_bfind_matcher search_term)
                                  (map snd l)); intros; simpl; eauto.
          case_eq (List.partition (InvertedIndex_bfind_matcher search_term)
                                  (map snd l)); intros; simpl; eauto.
        + rewrite Permutation_elements_map, Permutation_map_snd_swap,
          Permutation_elements_filter, Permutation_filter_map_snd.
          induction (MValues.elements (ValuesMap container)); simpl; eauto.
          rewrite <- partition_filter_eq.
          case_eq (InvertedIndex_bfind_matcher search_term (snd a)); intros; simpl in *.
          case_eq (List.partition (InvertedIndex_bfind_matcher search_term)
                                  (map snd l)); intros; simpl; eauto.
          case_eq (List.partition (InvertedIndex_bfind_matcher search_term)
                                  (map snd l)); intros; simpl; eauto.
        + intros; destruct x.
          intro; rewrite InA_eq_key_eq_key_elt in *; destruct_ex.
          rewrite <- !elements_mapsto_iff in *.
          rewrite !map_mapsto_iff in *; destruct_ex; intuition; subst.
          rewrite filter_iff in *; intuition eauto with typeclass_instances.
          rewrite <- (MoreMValuesFacts.BasicFacts.MapsTo_fun H H0) in H3.
          rewrite H3 in H1; discriminate.
      - rewrite Permutation_elements_filter, Permutation_filter_map_snd.
        induction (MValues.elements (ValuesMap container)); simpl; eauto.
        rewrite <- partition_filter_eq.
        case_eq (InvertedIndex_bfind_matcher search_term (snd a)); intros; simpl in *.
        case_eq (List.partition (InvertedIndex_bfind_matcher search_term)
                                (map snd l)); intros; simpl; eauto.
        case_eq (List.partition (InvertedIndex_bfind_matcher search_term)
                                (map snd l)); intros; simpl; eauto.
    Qed.

  End InvertedIndexBagDefinitions.

  Global Instance InvertedIndexAsBag
         {TItem UpdateTermType : Type}
         projection
         bupdate_transform
  : Bag InvertedIndexMap TItem SearchTerm UpdateTermType :=
    {|

      bempty            := InvertedIndex_bempty;

      bfind_matcher     := InvertedIndex_bfind_matcher projection;
      bupdate_transform := bupdate_transform;

      benumerate := InvertedIndex_benumerate;
      bfind      := InvertedIndex_bfind;
      binsert    := InvertedIndex_binsert projection;
      bcount     := InvertedIndex_bcount;
      bdelete    := InvertedIndex_bdelete projection;
      bupdate    := InvertedIndex_bupdate bupdate_transform projection |}.

  Global Instance InvertedIndexAsCorrectBag
         {TItem UpdateTermType : Type}
         projection
         bupdate_transform
  : CorrectBag (InvertedIndex_RepInv projection)
               (InvertedIndex_ValidUpdate _ projection)
               (InvertedIndexAsBag projection (UpdateTermType := UpdateTermType) bupdate_transform ) :=
    {
      bempty_RepInv     := InvertedIndex_Empty_RepInv projection;
      binsert_RepInv    := @InvertedIndex_binsert_Preserves_RepInv _ projection;
      bdelete_RepInv    := @InvertedIndex_bdelete_Preserves_RepInv _ projection;
      bupdate_RepInv    := @InvertedIndex_bupdate_Preserves_RepInv _ _ bupdate_transform projection;

      binsert_enumerate := @InvertedIndex_BagInsertEnumerate _ projection;
      benumerate_empty  := @InvertedIndex_BagEnumerateEmpty TItem;
      bfind_correct     := @InvertedIndex_BagFindCorrect _ projection;
      bcount_correct    := @InvertedIndex_BagCountCorrect _ projection;
      bdelete_correct   := @InvertedIndex_BagDeleteCorrect _ projection ;
      bupdate_correct   := @InvertedIndex_BagUpdateCorrect _ _ bupdate_transform projection
    }.

End InvertedIndexBag.
