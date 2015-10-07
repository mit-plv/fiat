Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Computation ADT ADTRefinement ADTNotation BuildADTRefinements
        KVEnsembles CacheSpec CacheRefinements FMapCacheImplementation.

Section LRUCache.

(* Abstraction relation between Ensemble specification
 and FMap Implementation. *)

  Variable Value : Type. (* Type of cached values *)
  Variable Bound : nat. (* Bound on cache size *)

  Definition BoundedStringCacheADT_AbsR
             (spec : Ensemble (string * Value)
                     * Ensemble (string * nat))
             (impl : StringIndexedMap.t Value
                     * StringIndexedMap.t nat
                     * nat) :=
    EnsembleFMapEquivalence (fst spec) (fst (fst impl)) /\
    EnsembleFMapEquivalence (snd spec) (snd (fst impl)) /\
    FMapCommonKeys (fst (fst impl)) (snd (fst impl)) /\
    indexBound (snd (fst impl)) (snd impl).

  (* To keep the presentation clean for the paper, we'll
 split and rename the premise holding the abstraction. *)
  Ltac StartMethod :=
    match goal with
        H : CacheADTwLogIndex_AbsR _ _ |- _ =>
        let H' := fresh "Eq_or_nr" in
        let H'' := fresh "EquivKeys_H" in
        destruct H as [H' H'']; rewrite H' in *
    end.

  Definition BoundedStringCacheADT
  : Sharpened (@CacheSpec string Value).
  Proof.
    unfold CacheSpec.
    hone representation using (@CacheADTwLogIndex_AbsR string Value).
    hone constructor "EmptyCache".
    {
      simplify with monad laws.
      rewrite refine_LogIndexEmpty.
      finish honing.
    }
    hone method "AddKey".
    {
      StartMethod.
      setoid_rewrite refine_ReplaceUsedKeyAdd.
      setoid_rewrite refine_SubEnsembleInsert.
      autorewrite with monad laws.
      setoid_rewrite refine_pick_KeyToBeReplaced_min.
      setoid_rewrite refine_If_Then_Else_Bind.
      autorewrite with monad laws.
      setoid_rewrite refine_If_Opt_Then_Else_Bind.
      autorewrite with monad laws.
      setoid_rewrite refine_pick_CacheADTwLogIndex_AbsR.
      setoid_rewrite refine_pick_KVEnsembleInsertRemove
      with (1 := EquivKeys_H).
      setoid_rewrite refine_pick_KVEnsembleInsert
      with (1 := EquivKeys_H).
      autorewrite with monad laws; simpl.
      finish honing.
    }
    hone method "UpdateKey".
    {
      StartMethod.
      setoid_rewrite refine_pick_CacheADTwLogIndex_AbsR.
      setoid_rewrite refine_IgnoreUnusedKeyUpdate.
      autorewrite with monad laws.
      setoid_rewrite refine_pick_KVEnsembleUpdateKey
      with (1 := EquivKeys_H).
      autorewrite with monad laws; simpl.
      finish honing.
    }
    hone method "LookupKey".
    {
      StartMethod.
      setoid_rewrite refine_pick_CacheADTwLogIndex_AbsR.
      autorewrite with monad laws.
      setoid_rewrite (refine_pick_KVEnsemble EquivKeys_H).
      autorewrite with monad laws;  simpl.
      finish honing.
    }

    hone representation using BoundedStringCacheADT_AbsR.

    (* The section is a good example of manual optimization
       scripts, largely because we haven't implemented honing
       tactics for implementing caches. *)

    hone constructor "EmptyCache".
    { autorewrite with monad laws.
      refine pick val
             (StringIndexedMap.empty Value,
              StringIndexedMap.empty nat,
              0).
      finish honing.
      repeat split; intuition; simpl in *;
      try (eapply (StringIndexedMap.empty_1); eauto;
           eapply (StringIndexedMap.find_2); eauto).
      - elimtype False;
        eapply StringIndexedMap.empty_1; eauto.
      - elimtype False;
        eapply StringIndexedMap.empty_1; eauto.
      - unfold indexBound; intros;
        elimtype False;
        eapply (StringIndexedMap.empty_1);
        eapply (StringIndexedMap.find_2); eauto.
    }

    hone method "LookupKey".
    {
      autorewrite with monad laws.
      refine pick val (StringIndexedMap.find n (fst (fst r_n))).
      autorewrite with monad laws; simpl.
      rewrite refine_pick_val by eauto.
      autorewrite with monad laws.
      finish honing.
      unfold BoundedStringCacheADT_AbsR, ValidLookup in *;
        intuition.
      apply H1 in H5.
      rewrite H3 in H5; discriminate.
      apply H1; eauto.
    }

    hone method "UpdateKey".
    {
      unfold BoundedStringCacheADT_AbsR in *; split_and.
      autorewrite with monad laws.
      rewrite refine_pick_val by eauto using decides_usedKey.
      autorewrite with monad laws; simpl.
      refine pick val (snd r_n); unfold PickID; eauto;
      autorewrite with monad laws.
      etransitivity.
      apply refine_Pick_Some_dec with
      (P := fun b => StringIndexedMap.find (elt:=Value) (fst n) (fst (fst r_n)) = Some b); intros.
      {
        refine pick val
               (StringIndexedMap.add (fst n) ((snd n) b) (fst (fst r_n)),
                StringIndexedMap.add (fst n) (snd r_n) (snd (fst r_n)),
                S (snd r_n)).
        simplify with monad laws.
        rewrite H3.
        higher_order_1_reflexivity.
        simpl; intuition.
        eauto using AbsR_add_EnsembleUpdateKey.
        apply StringIndexedMap.find_2 in H3.
        apply H2 in H3; destruct_ex.
        eapply AbsR_add_EnsembleUpdateKey with (f := fun _ => snd r_n);
          eauto using StringIndexedMap.find_1.
        eauto using FMapCommonKeys_add.
        eauto using indexBound_add.
      }
      {
        refine pick val _; eauto.
        autorewrite with monad laws; simpl.
        reflexivity.
        caseEq (StringIndexedMap.find (elt:=Value) (fst n) (fst (fst r_n)));
          try solve [elimtype False; eapply H3; eauto];
          intuition; eauto using AbsR_add_EnsembleUpdateKey'.
        eapply AbsR_add_EnsembleUpdateKey'; eauto using FMapCommonKeys_find_None.
      }
      refine pick val (StringIndexedMap.find (elt:=Value) (fst n) (fst (fst r_n)));
        try (split; congruence).
      autorewrite with monad laws.
      finish honing.
    }

    hone method "AddKey".
    {
      unfold BoundedStringCacheADT_AbsR in *; split_and.
      autorewrite with monad laws.
      rewrite refine_pick_val by eauto using decides_usedKey.
      autorewrite with monad laws.
      setoid_rewrite refine_If_Then_Else_Bind.
      etransitivity.
      apply refine_If_Then_Else';
        caseEq (StringIndexedMap.find (elt:=Value) (fst n) (fst (fst r_n))); simpl; try discriminate.
      (* If the key is used, do this. *)
      + autorewrite with monad laws.
        refine pick val (snd r_n); unfold PickID; eauto.
        autorewrite with monad laws; simpl.
        refine pick val ((_, _), _);
          [ |
            simpl; intuition;
            simpl; eauto using
                         AbsR_add_EnsembleReplaceKey,
                   FMapCommonKeys_remove,
                   FMapCommonKeys_add,
                   AbsR_add_EnsembleInsertRemove,
                   indexBound_add].
        autorewrite with monad laws.
        reflexivity.
        eapply (AbsR_add_EnsembleInsertRemove (fst n, snd r_n) H0).
      + (* If the key is not used, do this. *)
        autorewrite with monad laws.
        (* Check to see if we've hit the bound. *)
        apply (refine_if (b := if (gt_dec (snd r_n) Bound)
                               then true
                               else false)); intros.
        (* If we have, then pick a key to remove. *)
        rewrite refine_pick_oldest; eauto.
        autorewrite with monad laws.
        rewrite refine_If_Opt_Then_Else_Bind.
        (* Should add a constaint that Bound is greater
             than zero- then we can do away with this check. *)
        apply refine_If_Opt_Then_Else.
        * unfold pointwise_relation; intros.
          refine pick val (snd r_n); unfold PickID; eauto.
          simplify with monad laws; simpl.
          refine pick val ((StringIndexedMap.add (elt:=Value) (fst n) (snd n) (StringIndexedMap.remove a (fst (fst r_n))), _), S (snd r_n));
            [ |
              simpl; split; [ | split; [ | split ] ];
              simpl; eauto using
                           AbsR_add_EnsembleInsertRemove,
                     FMapCommonKeys_remove,
                     AbsR_add_EnsembleInsert,
                     AbsR_remove_EnsembleRemoveKey,
                     StringIndexedMap_find_None_remove,
                     FMapCommonKeys_add,
                     indexBound_add_remove].
          simplify with monad laws; simpl.
          higher_order_1_reflexivity.
          apply (@AbsR_add_EnsembleInsert nat);
            eauto using
                  AbsR_add_EnsembleInsert, AbsR_remove_EnsembleRemoveKey,
            StringIndexedMap_find_None_remove.
          apply StringIndexedMap_find_None_remove.
          eapply FMapCommonKeys_find_None; eauto.
        * refine pick val (snd r_n); unfold PickID; eauto.
          autorewrite with monad laws; simpl.
          refine pick val ((_, _), S (snd r_n));
            [ |
              simpl; intuition
                       simpl; eauto using
                                    AbsR_add_EnsembleInsert,
                              FMapCommonKeys_add,
                              indexBound_add;
              eapply (AbsR_add_EnsembleInsert (_, _));
              simpl; eauto using FMapCommonKeys_find_None].
          autorewrite with monad laws.
          reflexivity.
        * refine pick val None; try discriminate.
          autorewrite with monad laws.
          refine pick val (snd r_n); unfold PickID; eauto.
          autorewrite with monad laws; simpl.
          refine pick val ((_, _), S (snd r_n));
            [ |
              simpl; intuition
                       simpl; eauto using
                                    AbsR_add_EnsembleInsert,
                              FMapCommonKeys_add,
                              indexBound_add;
              eapply (AbsR_add_EnsembleInsert (_, _));
              simpl; eauto using FMapCommonKeys_find_None].
          autorewrite with monad laws.
          reflexivity.
      + finish honing.
    }

    finish sharpening.
  Defined.

End LRUCache.
