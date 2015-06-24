Require Export Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsInterface
        Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsProperties.
Require Import
        Coq.Arith.Peano_dec
        Coq.Structures.OrdersEx
        Coq.FSets.FMapInterface
        Coq.FSets.FMapFacts
        Coq.FSets.FMapAVL
        Fiat.Common
        Fiat.Common.String_as_OT
        Fiat.Common.List.ListFacts
        Fiat.Common.List.FlattenList
        Fiat.Common.SetEqProperties
        Fiat.Common.FMapExtensions
        Fiat.Common.List.PermutationFacts
        Fiat.QueryStructure.Specification.SearchTerms.ListInclusion.

Module InvertedIndexBag (MKeys : WS) (MValues : WSfun Nat_as_OT ).

  Module Import MKeysFacts := WFacts_fun MKeys.E MKeys.
  Module Import MKeysProperties := WProperties_fun MKeys.E MKeys.
  Module Import MoreMKeysFacts := FMapExtensions_fun MKeys.E MKeys.

  Module Import MValuesFacts := WFacts_fun Nat_as_OT MValues.
  Module Import MValuesProperties := WProperties_fun Nat_as_OT MValues.
  Module Import MoreMValuesFacts := FMapExtensions_fun Nat_as_OT MValues.
  Module E := MKeys.E.

  Section InvertedIndexBagDefinitions.

    Context {TItem : Type}
            {UpdateTermType : Type}
            (bupdate_transform : UpdateTermType -> TItem -> TItem).

    Definition IndexSearchTermT := list E.t.
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
             (MValues : ValuesMapT)
             (st : IndexSearchTermT)
    : ValuesMapT :=
      match st with
        | [ ] => MValues
        | i :: st' =>
          match MKeys.find i Mkey with
            | Some indexes =>
              Find_MatchingIndexes
                Mkey (filter (fun k _ => List.In_dec eq_nat_dec k (indexes)) MValues)
                st'
            | None => MValues.empty _
          end
      end.

    Definition InvertedIndex_bfind
             (it : InvertedIndexMap)
             (st : SearchTerm)
    : list TItem :=
      let matched_items := Find_MatchingIndexes it it (fst st) in
      List.filter (ItemSearchTermMatcher (snd st))
               (List.map snd (MValues.elements matched_items)).

    Definition InvertedIndex_bcount
               (it : InvertedIndexMap)
               (st : SearchTerm)
    : nat :=
      let matched_items := Find_MatchingIndexes it it (fst st) in
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

    Fixpoint InvertedIndex_bdelete
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

    Fixpoint InvertedIndex_bupdate
             (it : InvertedIndexMap)
             (st : SearchTerm)
             (updateTerm : UpdateTermType)
    : (list TItem) * InvertedIndexMap :=
      let (matchedItems, unmatchedItems) :=
          MValuesProperties.partition (fun _ => InvertedIndex_bfind_matcher st) (ValuesMap it) in
      (map snd (MValues.elements matchedItems),
       {| KeyMap := (KeyMap it);
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
        eapply (inA_map (f := fst)) in H0; eauto with typeclass_instances.
      - elimtype False; apply H.
        eapply (inA_map (f := fst)) in H0; eauto with typeclass_instances.
      - inversion H1.
      - destruct (E.eq_dec k a).
        + eauto.
        + eapply IHl in H0; intuition.
          * apply H.
            apply inA_map' with (eqA := @MKeys.eq_key_elt _) in H1;
              eauto with typeclass_instances.
            destruct_ex; intuition.
            rewrite H3.
            destruct x.
            rewrite <- MoreMKeysFacts.BasicFacts.elements_mapsto_iff in H2.
            eapply inA_map with (eqA := @MKeys.eq_key_elt _);
              eauto with typeclass_instances.
            rewrite <- MoreMKeysFacts.BasicFacts.elements_mapsto_iff.
            rewrite MoreMKeysFacts.BasicFacts.add_mapsto_iff in H2;
              intuition; subst.
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
            eauto with typeclass_instances.
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
        eauto with typeclass_instances.
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
            eauto with typeclass_instances.
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
            eauto with typeclass_instances.
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
          rewrite H in i0; intuition.
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
            rewrite H3 in i1; intuition.
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
            rewrite H3 in i0; intuition.
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
            rewrite H3 in i0; intuition.
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
            rewrite H3 in i0; intuition.
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
            rewrite H3 in i; intuition.
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
            rewrite H3 in i; intuition.
            rewrite <- H3 in i; intuition.
            intro; apply n.
            destruct H3; apply FMap_fold_add_MapsTo_In in H3; intuition.
            apply filter_InA in H8; intuition.
            unfold Proper, respectful; intros.
            repeat case_InA; try reflexivity.
            rewrite H3 in i; intuition.
            rewrite <- H3 in i; intuition.
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

    Lemma InvertedIndex_bdelete_Preserves_RepInv :
      bdelete_Preserves_RepInv InvertedIndex_RepInv InvertedIndex_bdelete.
    Proof.
    Admitted.

    Lemma InvertedIndex_bupdate_Preserves_RepInv :
      bupdate_Preserves_RepInv
        InvertedIndex_RepInv
        InvertedIndex_ValidUpdate
        InvertedIndex_bupdate.
    Proof.
    Admitted.

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
                   (Find_MatchingIndexes container container (fst search_term)));
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
        MValues.MapsTo idx item (Find_MatchingIndexes MKey MValues st) <->
        MValues.MapsTo idx item MValues /\
        inclA E.eq st (projection item).
    Proof.
    Admitted.

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
        eapply Find_MatchingIndexesOK_Subset; eauto.
        discriminate.
      - find_if_inside; eauto; discriminate.
      - eapply Find_MatchingIndexesOK_Subset; eauto.
      - find_if_inside; eauto.
        apply Not_inclA_NIn in n; destruct n; split_and.
        eapply Find_MatchingIndexesOK_Subset in H3; intuition eauto.
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
        apply H3; revert H H1; clear; induction (MValues.elements (ValuesMap container)); simpl; intros; inversion H; subst; eauto.
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
          apply H2; eexists; eauto.
          rewrite <- elements_mapsto_iff in H4; eauto.
    Qed.

    Lemma InvertedIndex_BagDeleteCorrect :
      BagDeleteCorrect InvertedIndex_RepInv InvertedIndex_bfind
                       InvertedIndex_bfind_matcher
                       InvertedIndex_benumerate InvertedIndex_bdelete.
    Proof.
    Admitted.

    Lemma InvertedIndex_BagUpdateCorrect :
      BagUpdateCorrect InvertedIndex_RepInv InvertedIndex_ValidUpdate
                       InvertedIndex_bfind InvertedIndex_bfind_matcher
                       InvertedIndex_benumerate
                       bupdate_transform InvertedIndex_bupdate.
    Proof.
    Admitted.

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
    {|
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
    |}.

End InvertedIndexBag.
