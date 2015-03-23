Require Export ADTSynthesis.QueryStructure.Implementation.DataStructures.Bags.BagsInterface
        ADTSynthesis.QueryStructure.Implementation.DataStructures.Bags.BagsProperties.
Require Import
        Coq.Arith.Peano_dec
        Coq.Structures.OrdersEx
        Coq.FSets.FMapInterface
        Coq.FSets.FMapFacts
        Coq.FSets.FMapAVL
        ADTSynthesis.Common
        ADTSynthesis.Common.String_as_OT
        ADTSynthesis.Common.List.ListFacts
        ADTSynthesis.Common.List.FlattenList
        ADTSynthesis.Common.SetEqProperties
        ADTSynthesis.Common.FMapExtensions
        ADTSynthesis.Common.List.PermutationFacts.

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
    Record SearchTerm :=
      { IndexSearchTerm : IndexSearchTermT;
         ItemSearchTerm : ItemSearchTermT }.

    Context (projection: TItem -> IndexSearchTermT).
    Coercion IndexSearchTerm : SearchTerm >-> IndexSearchTermT.
    Coercion ItemSearchTerm : SearchTerm >-> ItemSearchTermT.

    Definition InvertedIndex_bfind_matcher
               (st : SearchTerm) (item: TItem) :=
      if IndexSearchTerm_included_dec st (projection item)  then
        ItemSearchTermMatcher st item
        else false.

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
      let matched_items := Find_MatchingIndexes it it st in
      List.filter (ItemSearchTermMatcher st)
               (List.map snd (MValues.elements matched_items)).

    Definition InvertedIndex_bcount
               (it : InvertedIndexMap)
               (st : SearchTerm)
    : nat :=
      let matched_items := Find_MatchingIndexes it it st in
      fold_right (fun _ n => 1 + n)
                 0
                (List.filter (fun item => ItemSearchTermMatcher st (snd item))
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
           let (includedKeys, notIncludedKeys) :=
               MKeysProperties.partition
                 (fun key _ =>
                    if (InA_dec E.eq_dec key (projection item))
                    then true
                    else false)
                 (KeyMap it) in
           let oldKeys := map fst (MKeys.elements includedKeys) in
           let newKeys := List.filter (fun key : E.t =>
                                         if InA_dec E.eq_dec key oldKeys then
                                           false else true) (projection item) in
           MKeysProperties.update
             (fold_left (fun m k => MKeys.add k [NumValues it] m) newKeys (MKeys.empty _))
             (MKeysProperties.update
                (MKeys.map (cons (NumValues it)) includedKeys)
                notIncludedKeys);
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
              /\ ~ MValues.In (NumValues it) (ValuesMap it).

    Definition InvertedIndex_ValidUpdate (update_term : UpdateTermType) :=
      forall item,
        projection item = projection (bupdate_transform update_term item).

    Lemma InvertedIndex_Empty_RepInv :
      InvertedIndex_RepInv (InvertedIndex_bempty).
    Proof.
      unfold InvertedIndex_RepInv; intros; repeat split; simpl; intros.
      - elimtype False; eapply MKeys.empty_1; eauto.
      - elimtype False; eapply MValues.empty_1; eauto.
      - intro; destruct H; eapply MValues.empty_1; eauto.
    Qed.

    Lemma InvertedIndex_binsert_Preserves_RepInv :
      binsert_Preserves_RepInv InvertedIndex_RepInv InvertedIndex_binsert.
    Proof.
      unfold binsert_Preserves_RepInv, InvertedIndex_binsert, UpdateKeyMap;
      intros; repeat split; intros; simpl in *.
    Admitted.

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
                   (Find_MatchingIndexes container container search_term));
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
                if IndexSearchTerm_included_dec search_term  (projection item)
                then ItemSearchTermMatcher search_term item
                else false).
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
                   if IndexSearchTerm_included_dec search_term  (projection item)
                   then ItemSearchTermMatcher search_term item
                   else false);
        eauto using Proper_bfind_matcher.
      rewrite <- Permutation_filter_elements
      with (f := fun (k : MValues.key) (item : TItem) =>
                   ItemSearchTermMatcher search_term item);
        eauto using Proper_ItemSearchTermMatcher.
      eapply MoreMValuesFacts.Permutation_InA_cons;
      eauto using NoDupA_filter, MValues.elements_3w.
      intros; rewrite <- !elements_mapsto_iff.
      rewrite !filter_iff
        by (eauto using Proper_bfind_matcher,
            Proper_ItemSearchTermMatcher).
      intuition.
      - try find_if_inside; eauto.
        eapply Find_MatchingIndexesOK_Suset; eauto.
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
