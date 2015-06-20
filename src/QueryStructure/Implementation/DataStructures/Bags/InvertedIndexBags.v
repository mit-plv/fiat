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
           fold_right
             (fun term container'  =>
                match MKeys.find term container' with
                | Some ns => MKeys.add term (NumValues it :: ns) container'
                | None => MKeys.add term [NumValues it] container'
                end) (KeyMap it) (projection item);
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
         /\ forall n, NumValues it <= n -> ~ MValues.In n (ValuesMap it).

    Definition InvertedIndex_ValidUpdate (update_term : UpdateTermType) :=
      forall item,
        projection item = projection (bupdate_transform update_term item).

    Lemma InvertedIndex_Empty_RepInv :
      InvertedIndex_RepInv (InvertedIndex_bempty).
    Proof.
      unfold InvertedIndex_RepInv; intros; repeat split; simpl; intros.
      - elimtype False; eapply MKeys.empty_1; eauto.
      - elimtype False; eapply MValues.empty_1; eauto.
      - intro; destruct H0; eapply MValues.empty_1; eauto.
    Qed.

    Lemma InvertedIndex_binsert_Preserves_RepInv :
      binsert_Preserves_RepInv InvertedIndex_RepInv InvertedIndex_binsert.
    Proof.
      unfold binsert_Preserves_RepInv, InvertedIndex_binsert, UpdateKeyMap;
      intros; repeat split; intros; simpl in *.
      - generalize dependent indexes; revert idx key container containerCorrect.
         remember (projection item).
         assert (forall term, InA E.eq term i -> InA E.eq term (projection item)) by (subst; eauto); clear Heqi.
         induction i; simpl in *; intros.
         + destruct containerCorrect.
           eapply (H2 key indexes) in H1; eauto.
           destruct H1 as [item0 [MapsToIdx InAKey]]; eexists; split; eauto.
           eapply MValues.add_2; eauto.
           intro; eapply H3; subst; eauto using MapsTo_In.
         + revert H0;
           case_eq (MKeys.find a
            (fold_right
               (fun (term : MKeys.key) (container' : MKeys.t (list nat)) =>
                match MKeys.find term container' with
                | Some ns =>
                    MKeys.add term (NumValues container :: ns) container'
                | None => MKeys.add term [NumValues container] container'
                end) (KeyMap container) i)); intros;
           eapply MoreMKeysFacts.BasicFacts.add_mapsto_iff in H2;
           intuition subst; simpl in *; intuition subst.
         * eexists; intuition.
         * eapply MoreMKeysFacts.BasicFacts.find_mapsto_iff in H0.
           setoid_rewrite <- H2; eauto.
         * eauto using MoreMKeysFacts.BasicFacts.find_mapsto_iff.
         * eexists; intuition.
         * eauto using MoreMKeysFacts.BasicFacts.not_find_mapsto_iff.
      - eapply MoreMValuesFacts.BasicFacts.add_mapsto_iff in H;
           intuition subst; simpl in *; eauto.
        + revert key container containerCorrect H0.
          remember (projection item0).
          assert (forall term, InA E.eq term i -> InA E.eq term (projection item0)) by (subst; eauto); clear Heqi.
          induction i; simpl in *; intros; inversion H0; subst; clear H0;
          eauto;
          case_eq (MKeys.find a
                              (fold_right
               (fun (term : MKeys.key) (container' : MKeys.t (list nat)) =>
                match MKeys.find term container' with
                | Some ns =>
                    MKeys.add term (NumValues container :: ns) container'
                | None => MKeys.add term [NumValues container] container'
                end) (KeyMap container) i)); intros.
          *  eapply MoreMKeysFacts.BasicFacts.find_mapsto_iff in H0.
             setoid_rewrite H2; eexists; split; simpl; eauto using MKeys.add_1;
             simpl; eauto.
          *  setoid_rewrite H2; eexists; split; simpl; eauto using MKeys.add_1;
         simpl; eauto.
          *  eapply IHi in H2; eauto.
             destruct_ex; intuition.
             destruct (E.eq_dec key a); eexists; try (solve [intuition]).
             split.
             eapply MoreMKeysFacts.BasicFacts.add_mapsto_iff; eauto.
             eauto.
          *  eapply IHi in H2; eauto.
             destruct_ex; intuition.
             destruct (E.eq_dec key a); eexists; try (solve [intuition]).
             split.
             eapply MoreMKeysFacts.BasicFacts.add_mapsto_iff; eauto.
             eauto.
        + revert key container containerCorrect H0 H H2.
          remember (projection item0).
          assert (forall term, InA E.eq term i -> InA E.eq term (projection item0)) by (subst; eauto); clear Heqi.
          induction i; simpl in *; intros; inversion H0; subst; clear H0;
          eauto.
          eapply containerCorrect in H2; eauto; destruct_ex; intuition.
          assert (InA E.eq key (projection item0)) by
              (eapply H; econstructor; eauto).
          revert H1 H2 H3; clear; induction (projection item); simpl; eauto.
          intros.
          case_eq (MKeys.find a
           (fold_right
              (fun (term : MKeys.key) (container' : MKeys.t (list nat)) =>
               match MKeys.find term container' with
               | Some ns =>
                   MKeys.add term (NumValues container :: ns) container'
               | None => MKeys.add term [NumValues container] container'
               end) (KeyMap container) i)); intros.
          * destruct (E.eq_dec key a).
            { setoid_rewrite e.
              eexists; split.
              - eapply MoreMKeysFacts.BasicFacts.add_mapsto_iff; eauto.
              - right; rewrite e in *; generalize a container l H H3 H2; clear;
                induction i; simpl; intros.
                + eapply MoreMKeysFacts.BasicFacts.find_mapsto_iff in H2.
                  rewrite H in H2; injections; eauto.
                + eapply MoreMKeysFacts.BasicFacts.find_mapsto_iff in H.
                  revert H.
                  case_eq (MKeys.find a
            (fold_right
               (fun (term : MKeys.key) (container' : MKeys.t (list nat)) =>
                match MKeys.find term container' with
                | Some ns =>
                    MKeys.add term (NumValues container :: ns) container'
                | None => MKeys.add term [NumValues container] container'
                end) (KeyMap container) i)); intros.
                  eapply MoreMKeysFacts.BasicFacts.add_mapsto_iff in H0; intuition.
                  * subst; right; eapply IHi; rewrite <- H0 in H2; eauto.
                  * eapply IHi; eauto; eapply MoreMKeysFacts.BasicFacts.find_mapsto_iff; eauto.
                  * eapply MoreMKeysFacts.BasicFacts.add_mapsto_iff in H0; intuition.
                    eapply MoreMKeysFacts.BasicFacts.not_find_mapsto_iff in H.
                    elimtype False; apply H.
                    unfold MKeys.In; setoid_rewrite H0; revert H2; clear; induction i; simpl; eauto.
                    destruct (MKeys.find a
           (fold_right
              (fun (term : MKeys.key) (container' : MKeys.t (list nat)) =>
               match MKeys.find term container' with
               | Some ns =>
                   MKeys.add term (NumValues container :: ns) container'
               | None => MKeys.add term [NumValues container] container'
               end) (KeyMap container) i)); intros.
                    { destruct (E.eq_dec a0 a).
                      setoid_rewrite e.
                      eexists; eapply MoreMKeysFacts.BasicFacts.add_mapsto_iff; eauto.
                      destruct (IHi H2).
                      eexists; eapply MoreMKeysFacts.BasicFacts.add_mapsto_iff; eauto.
                    }
                    { destruct (E.eq_dec a0 a).
                      setoid_rewrite e.
                      eexists; eapply MoreMKeysFacts.BasicFacts.add_mapsto_iff; eauto.
                      destruct (IHi H2).
                      eexists; eapply MoreMKeysFacts.BasicFacts.add_mapsto_iff; eauto.
                    }
                    eapply MoreMKeysFacts.BasicFacts.find_mapsto_iff in H4.
                    eapply IHi; eauto.
            }
            eapply IHi in H3; eauto.
            destruct_ex; eexists; split.
            eapply MoreMKeysFacts.BasicFacts.add_mapsto_iff; intuition eauto.
            eapply H0.
          * destruct (E.eq_dec key a).
            { setoid_rewrite e.
              eexists; split.
              - eapply MoreMKeysFacts.BasicFacts.add_mapsto_iff; eauto.
              - eapply MoreMKeysFacts.BasicFacts.not_find_mapsto_iff in H.
                elimtype False; apply H.
                unfold MKeys.In; setoid_rewrite <- e; revert H2; clear; induction i; simpl; eauto.
                    destruct (MKeys.find a
           (fold_right
              (fun (term : MKeys.key) (container' : MKeys.t (list nat)) =>
               match MKeys.find term container' with
               | Some ns =>
                   MKeys.add term (NumValues container :: ns) container'
               | None => MKeys.add term [NumValues container] container'
               end) (KeyMap container) i)); intros.
                    { destruct (E.eq_dec key a).
                      setoid_rewrite e.
                      eexists; eapply MoreMKeysFacts.BasicFacts.add_mapsto_iff; eauto.
                      destruct (IHi H2).
                      eexists; eapply MoreMKeysFacts.BasicFacts.add_mapsto_iff; eauto.
                    }
                    { destruct (E.eq_dec key a).
                      setoid_rewrite e.
                      eexists; eapply MoreMKeysFacts.BasicFacts.add_mapsto_iff; eauto.
                      destruct (IHi H2).
                      eexists; eapply MoreMKeysFacts.BasicFacts.add_mapsto_iff; eauto.
                    }
            }
            eapply IHi in H3; eauto.
            destruct_ex; eexists; split.
            eapply MoreMKeysFacts.BasicFacts.add_mapsto_iff; intuition eauto.
            eapply H0.
      - unfold not; intros; destruct H0.
        eapply MoreMValuesFacts.BasicFacts.add_mapsto_iff in H0; intuition eauto; subst.
        + omega.
        + eapply containerCorrect; unfold MValues.In;
          [ | eexists _ ; eassumption ].
          omega.
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
          eapply H2.
          * eauto.
          * eexists; eauto.
          * rewrite <- elements_mapsto_iff in H4; eauto.
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
