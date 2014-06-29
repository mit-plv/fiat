Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation BuildADTRefinements.

Section CacheADT.

  Variable Key : Type.
  Variable Value : Type.

  Definition CacheSig : ADTSig :=
    ADTsignature {
        "EmptyCache"  : unit → rep,
        "AddKey" : rep × (Key * Value) → rep × bool,
        "UpdateKey" : rep × (Key * Value) → rep × bool,
        "LookupKey"   : rep × Key → rep × (option Value)
  }.

  Definition EnsembleInsert  {A} (a : A) (ens : Ensemble A) (a' : A)
    : Prop := a' = a \/ ens a'.

  Definition SubEnsembleInsert {A} (a : A) (ens ens' : Ensemble A)
  : Prop :=
    forall (a' : A), ens' a' -> EnsembleInsert a ens a'.

  Definition EnsembleRemove
             (k : Key)
             (ens : Ensemble (Key * Value))
             (k' : Key * Value)
  : Prop := (fst k' <> k /\ ens k').

  Definition EnsembleReplace
             (k : Key * Value)
             (ens : Ensemble (Key * Value))
             (k' : Key * Value)
  : Prop := k' = k \/
            (EnsembleRemove (fst k) ens k').

  Definition ValidLookup
             (r : Ensemble (Key * Value))
             (k : Key)
             (v : option Value)
  : Prop := forall v', v = Some v' -> r (k, v').

  Definition usedKey
             (r : Ensemble (Key * Value))
             (k : Key)
  : Prop := exists v, r (k, v).

  Definition CacheSpec : ADT CacheSig :=
    ADTRep (Ensemble (Key * Value)) {
        const "EmptyCache" (_ : unit) : rep :=
          ret (fun _ => False),
        meth "AddKey" (r : rep, kv : Key * Value) : bool :=
            { r' | (usedKey r (fst kv) -> snd r' = false) /\
                   (~ usedKey r (fst kv) -> (SubEnsembleInsert kv r (fst r'))
                                            /\ snd r' = true)},
        meth "UpdateKey" (r : rep, kv : Key * Value) : bool :=
              { r' | (usedKey r (fst kv) -> r' = (EnsembleReplace kv r, true)) /\
                     (~ usedKey r (fst kv) -> snd r' = false)},
        meth "LookupKey" (r : rep, k : Key) : option Value :=
                v <- {v | ValidLookup r k v};
        ret (r, v)
      }.

End CacheADT.

Require Import String_as_OT.
Require Import FMapAVL.

Module StringIndexedMap := FMapAVL.Make String_as_OT.
Definition MapStringNat := StringIndexedMap.t nat.

Section AddDuplicateKeyStrategies.

  Variable Key : Type.
  Variable Value : Type.

  (* Two strategies : replace the key*)

  Lemma refine_ReplaceUsedKey
  : forall (kv : Key * Value)
           (r : Ensemble (Key * Value)),
      refine { r' | (usedKey r (fst kv) -> snd r' = false) /\
                    (~ usedKey r (fst kv) -> (SubEnsembleInsert kv r (fst r'))
                                             /\ snd r' = true)}
             (b <- {b | decides b (usedKey r (fst kv))};
              r' <- { r' | if b then r' = EnsembleReplace kv r
                                else SubEnsembleInsert kv r r' };
              ret (r', negb b)).
  Proof.
    intros; rewrite refine_pick_decides.
    f_equiv; unfold pointwise_relation; intros.
    destruct a.
    - refine pick eq; rewrite refineEquiv_bind_unit;
      apply refine_pick_val; reflexivity.
    - refine pick pair.
      refine pick eq.
      simplify with monad laws.
      f_equiv.
  Qed.

  Lemma refine_IgnoreUsedKeyInsert
  : forall (kv : Key * Value)
           (r : Ensemble (Key * Value)),
      refine { r' | (usedKey r (fst kv) -> snd r' = false) /\
                    (~ usedKey r (fst kv) -> (SubEnsembleInsert kv r (fst r'))
                                             /\ snd r' = true)}
             (b <- {b | decides b (usedKey r (fst kv))};
              r' <- { r' | if b then r' = r
                                else SubEnsembleInsert kv r r' };
              ret (r', negb b)).
  Proof.
    intros; rewrite refine_pick_decides.
    f_equiv; unfold pointwise_relation; intros.
    destruct a.
    - refine pick eq; rewrite refineEquiv_bind_unit;
      apply refine_pick_val; reflexivity.
    - refine pick pair.
      refine pick eq.
      simplify with monad laws.
      f_equiv.
  Qed.

End AddDuplicateKeyStrategies.

Section CacheEvictionStrategies.

  Variable Key : Type.
  Variable Value : Type.

  Definition CacheADTwMetric_AbsR
             (or : Ensemble (Key * Value))
             (nr : Ensemble (Key * (Value * nat)))
    := forall kv, or (fst kv, fst (snd kv)) <-> nr kv.

  (* First refinement- determine if there is a key to be replaced. *)

  Lemma refine_SubEnsembleInsert
  : forall (k : Key)
           (v : Value)
           (idx : nat)
           (r : Ensemble (Key * (Value * nat))),
      refine { r' | (SubEnsembleInsert (k, (v, idx)) r r')}
             (kv_opt <- {kv_opt | forall kv',
                                    kv_opt = Some kv' -> r kv'};
              {r' | r' = match kv_opt with
                           | Some (kv', _) =>
                             EnsembleInsert (k, (v, idx))
                                            (EnsembleRemove kv' r)
                           | None => EnsembleInsert (k, (v, idx)) r
                         end} ).
  Proof.
    intros; rewrite refine_Pick_Some with
            (P := r).
    f_equiv; unfold pointwise_relation; intros.
    destruct a;
      [ higher_order_1_reflexivity 
      | reflexivity ].
    simpl; intros; refine pick eq;  apply refine_pick_val;
    destruct b; unfold SubEnsembleInsert, EnsembleInsert,
                EnsembleRemove; simpl; intros; intuition.
    simpl; intros; refine pick eq;  apply refine_pick_val;
    unfold SubEnsembleInsert, EnsembleInsert,
    EnsembleRemove; simpl; intros; intuition.
  Qed.

  Lemma refine_pick_KeyToBeReplaced_min
  : forall (r : Ensemble (Key * (Value * nat))),
      refine {kv_opt | forall kv',
                         kv_opt = Some kv' -> r kv'}
             {kv_opt | forall kv',
                         kv_opt = Some kv' -> 
                         (r kv' 
                          /\ (forall kv'', 
                                r kv'' -> (snd (snd kv')) <= snd (snd kv'')))
                             }.
  Proof.
    intros; apply refine_pick_pick; intros.
    eapply H; eauto.
  Qed.

  Lemma refine_pick_KeyToBeReplaced_max
  : forall (r : Ensemble (Key * (Value * nat))),
      refine {kv_opt | forall kv',
                         kv_opt = Some kv' -> r kv'}
             {kv_opt | forall kv',
                         kv_opt = Some kv' -> 
                         (r kv' 
                          /\ (forall kv'', 
                                r kv'' -> (snd (snd kv'')) <= snd (snd kv')))
                             }.
  Proof.
    intros; apply refine_pick_pick; intros.
    eapply H; eauto.
  Qed.


  Lemma refine_ReplaceUsedKey
  : forall (kv : Key * Value)
           (r : Ensemble (Key * Value)),
      refine { r' | (usedKey r (fst kv) -> snd r' = false) /\
                    (~ usedKey r (fst kv) -> (SubEnsembleInsert kv r (fst r'))
                                             /\ snd r' = true)}
             (b <- {b | decides b (usedKey r (fst kv))};
              r' <- { r' | if b then r' = EnsembleReplace kv r
                                else SubEnsembleInsert kv r r' };
              ret (r', negb b)).
  Proof.
    intros; rewrite refine_pick_decides.
    f_equiv; unfold pointwise_relation; intros.
    destruct a.
    - refine pick eq; rewrite refineEquiv_bind_unit;
      apply refine_pick_val; reflexivity.
    - refine pick pair.
      refine pick eq.
      simplify with monad laws.
      f_equiv.
  Qed.

  Lemma refine_IgnoreUsedKeyInsert
  : forall (kv : Key * Value)
           (r : Ensemble (Key * Value)),
      refine { r' | (usedKey r (fst kv) -> snd r' = false) /\
                    (~ usedKey r (fst kv) -> (SubEnsembleInsert kv r (fst r'))
                                             /\ snd r' = true)}
             (b <- {b | decides b (usedKey r (fst kv))};
              r' <- { r' | if b then r' = r
                                else SubEnsembleInsert kv r r' };
              ret (r', negb b)).
  Proof.
    intros; rewrite refine_pick_decides.
    f_equiv; unfold pointwise_relation; intros.
    destruct a.
    - refine pick eq; rewrite refineEquiv_bind_unit;
      apply refine_pick_val; reflexivity.
    - refine pick pair.
      refine pick eq.
      simplify with monad laws.
      f_equiv.
  Qed.


  Definition BoundedStringCacheADT_AbsR
             (or nr : Ensemble (Key * Value))
    := forall kv, (or kv <-> nr kv) /\
                  (forall kv', nr kv' -> fst kv' = fst kv).



  Lemma decides_usedKey
  : forall (or : Ensemble (string * Value))
           (nr : StringIndexedMap.t Value)
           (k : string),
      BoundedStringCacheADT_AbsR or nr ->
      decides (if StringIndexedMap.find k nr then
                 true else
                 false)
              (usedKey or k).
  Proof.
    unfold BoundedStringCacheADT_AbsR, usedKey; intros;
    pose proof (H k); intuition.
    find_if_inside; simpl; eauto.
    intuition; destruct_ex.
    destruct (H2 _ H0); discriminate.
  Qed.

  Lemma AbsR_add_EnsembleReplace
  : forall nr kv or v,
      BoundedStringCacheADT_AbsR or nr
      -> StringIndexedMap.find (elt:=Value) (fst kv) nr = Some v
      -> BoundedStringCacheADT_AbsR
           (EnsembleReplace kv or)
           (StringIndexedMap.add (fst kv) (snd kv) nr).
  Proof.
    unfold EnsembleReplace, EnsembleRemove,
    BoundedStringCacheADT_AbsR;
    intros; intuition.
    destruct (string_dec k (fst kv)); subst.
    left.
    rewrite (StringIndexedMap.find_1 (StringIndexedMap.add_1 nr (snd kv) (refl_equal (fst kv))))
      in *; destruct kv; simpl in *; f_equal; congruence.
    right; split; eauto.
    eapply H.
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_3,
    StringIndexedMap.find_2.
    subst; simpl in *.
    eexists; eauto using StringIndexedMap.find_1, StringIndexedMap.add_1.
    destruct (string_dec k (fst kv)); subst.
    eexists; eauto using StringIndexedMap.find_1, StringIndexedMap.add_1.
    destruct (H k).
    destruct (H4 _ H3).
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_2,
    StringIndexedMap.find_2.
  Qed.

  Lemma AbsR_add_EnsembleInsert
  : forall nr kv or,
      BoundedStringCacheADT_AbsR or nr
      -> StringIndexedMap.find (elt:=Value) (fst kv) nr = None
      -> BoundedStringCacheADT_AbsR
           (fun kv' => kv' = kv \/ or kv')
           (StringIndexedMap.add (fst kv) (snd kv) nr).
  Proof.
    unfold SubEnsembleInsert, BoundedStringCacheADT_AbsR;
    intros; intuition.
    destruct (string_dec k (fst kv)); subst.
    left.
    rewrite (StringIndexedMap.find_1 (StringIndexedMap.add_1 nr (snd kv) (refl_equal (fst kv))))
      in *; destruct kv; simpl in *; f_equal; congruence.
    right.
    pose proof (H k); intuition.
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_3,
    StringIndexedMap.find_2.
    subst; simpl in *.
    eexists; eauto using StringIndexedMap.find_1, StringIndexedMap.add_1.
    destruct (string_dec k (fst kv)); subst.
    eexists; eauto using StringIndexedMap.find_1, StringIndexedMap.add_1.
    destruct (H k).
    destruct (H3 _ H2).
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_2,
    StringIndexedMap.find_2.
  Qed.

  Lemma AbsR_add_EnsembleInsertRemove
  : forall nr or k kv,
      BoundedStringCacheADT_AbsR or nr
      -> StringIndexedMap.find (elt:=Value) (fst kv) nr = None
      -> BoundedStringCacheADT_AbsR
           (EnsembleInsert kv (EnsembleRemove k or))
           (StringIndexedMap.add (fst kv) (snd kv) (StringIndexedMap.remove k nr)).
  Proof.
    unfold SubEnsembleInsert, EnsembleRemove,
    EnsembleInsert, BoundedStringCacheADT_AbsR;
    intros; intuition.
    destruct (string_dec k0 (fst kv)); subst.
    left;
    rewrite (StringIndexedMap.find_1 (StringIndexedMap.add_1 _ (snd kv) (refl_equal (fst kv))))
      in H1; destruct kv; simpl in *; f_equal; congruence.
    right; destruct (string_dec k0 k); subst.
    elimtype False; eapply StringIndexedMap.remove_1 with (x := k); eauto.
    eapply StringIndexedMap.find_2 in H1.
    eapply StringIndexedMap.add_3 in H1; eauto.
    unfold StringIndexedMap.In, StringIndexedMap.Raw.In0; eauto.
    intuition.
    eapply H.
    eapply StringIndexedMap.find_1.
    eapply StringIndexedMap.remove_3; eauto.
    eapply StringIndexedMap.add_3; clear n0; eauto.
    eapply StringIndexedMap.find_2; eauto.
    subst; simpl.
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_1.
    destruct (string_dec k0 (fst kv)); subst.
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_1.
    destruct (H k0).
    destruct (H4 _ H3).
    eexists.
    eapply StringIndexedMap.find_2 in H5.
    eapply StringIndexedMap.remove_2 in H5.
    eapply StringIndexedMap.add_2 in H5; eauto.
    eapply StringIndexedMap.find_1; eauto.
    simpl in *; congruence.
  Qed.

  Definition BoundedStringCacheADT' :
    Sharpened (@CacheSpec string Value).
  Proof.
    unfold CacheSpec; simpl.
    hone representation using BoundedStringCacheADT_AbsR.

    hone constructor "EmptyCache".
    {
      simplify with monad laws.
      rewrite refine_pick_val with
      (A := StringIndexedMap.t Value)
      (a := StringIndexedMap.empty Value).
      finish honing.
      unfold BoundedStringCacheADT_AbsR; intros; intuition.
      eapply (StringIndexedMap.empty_1); eauto.
      eapply (StringIndexedMap.find_2); eauto.
    }

    hone method "LookupKey".
    {
      simplify with monad laws.
      refine pick val (StringIndexedMap.find n r_n).
      simplify with monad laws; simpl.
      rewrite refine_pick_val by eauto.
      simplify with monad laws.
      finish honing.
      unfold BoundedStringCacheADT_AbsR, ValidLookup in *;
        intros; pose proof (H0 n); intuition.
    }

    hone method "UpdateKey".
    {
      rewrite refine_pick_decides;
        simplify with monad laws.
      rewrite refine_pick_val by eauto using decides_usedKey.
      simplify with monad laws.
      eapply refine_if with
      (b := if StringIndexedMap.find (elt:=Value) (fst n) r_n then true else false).
      {
        (* If the Key is used, do this. *)
        caseEq (StringIndexedMap.find (elt:=Value) (fst n) r_n);
        try discriminate; simpl.
        rewrite refineEquiv_pick_eq; simplify with monad laws; simpl.
        rewrite refine_pick_val by
          eauto using AbsR_add_EnsembleReplace.
        simplify with monad laws.
        reflexivity.
      }
      {
        (* If the Key isn't in the cache, do this. *)
        caseEq (StringIndexedMap.find (elt:=Value) (fst n) r_n);
        try discriminate; simpl.
        erefine pick val (_, _).
        simplify with monad laws.
        rewrite refine_pick_val by eauto.
        simplify with monad laws; simpl; reflexivity.
      }
    }

    hone method "AddKey".
    {
      rewrite refine_pick_decides;
      simplify with monad laws.
      rewrite refine_pick_val by eauto using decides_usedKey.
      simplify with monad laws.
      eapply refine_if with
      (b := if StringIndexedMap.find (elt:=Value) (fst n) r_n then true else false).
      {
        (* If the Key is used, do nothing. *)
        caseEq (StringIndexedMap.find (elt:=Value) (fst n) r_n);
        try discriminate; simpl.
        erefine pick val (_, _).
        simplify with monad laws.
        rewrite refine_pick_val by eauto.
        simplify with monad laws; simpl; reflexivity.
      }
      {
        (* If the Key is not used, do this. *)
        caseEq (StringIndexedMap.find (elt:=Value) (fst n) r_n);
        try discriminate; simpl.
        refine pick_pair.
        setoid_rewrite refineEquiv_pick_eq; simplify with monad laws.
        (* Check if there is a key worth removing *)
        etransitivity;
          [ eapply (refine_Pick_Some (A := StringIndexedMap.t Value * bool)
                                     (fun kv => StringIndexedMap.find (fst kv) r_n = Some (snd kv)))
          | ].
        { (* If so, replace it. *)
          intros.
          refine pick val (EnsembleInsert n (EnsembleRemove (fst b) or)).
          simplify with monad laws; simpl.
          rewrite refine_pick_val
            by eauto using AbsR_add_EnsembleInsertRemove.
          simplify with monad laws.
          higher_order_1_reflexivity.
          unfold SubEnsembleInsert, EnsembleInsert, EnsembleRemove; eauto.
        }
        {
          (* If not, do a standard insert. *)
          refine pick val (EnsembleInsert n or).
          simplify with monad laws; simpl.
          rewrite refine_pick_val
            by eauto using AbsR_add_EnsembleInsert.
          simplify with monad laws.
          reflexivity.
          unfold SubEnsembleInsert, EnsembleInsert, EnsembleRemove; eauto.
        }
        (* Here's where we can decide how to pick the element to
         replace. Picking None lets the cache grow unboundedly. *)
        refine pick val (@None (StringIndexedMap.key * Value) ).
        try simplify with monad laws.
        reflexivity.
        intuition; try discriminate.
      }

    }

    finish sharpening.

  Defined.

End BoundedStringCacheADT.

Section BoundedStringCacheADT.

  Variable Value : Type.

  Definition BoundedStringCacheADT_AbsR
             (or : Ensemble (string * Value))
             (nr : StringIndexedMap.t Value) :=
    forall k,
      (forall v, StringIndexedMap.find k nr = Some v ->
                 or (k, v)) /\
      (forall v, or (k, v) ->
                 exists v',
                   StringIndexedMap.find k nr = Some v').

  Lemma decides_usedKey
  : forall (or : Ensemble (string * Value))
           (nr : StringIndexedMap.t Value)
           (k : string),
      BoundedStringCacheADT_AbsR or nr ->
      decides (if StringIndexedMap.find k nr then
                 true else
                 false)
              (usedKey or k).
  Proof.
    unfold BoundedStringCacheADT_AbsR, usedKey; intros;
    pose proof (H k); intuition.
    find_if_inside; simpl; eauto.
    intuition; destruct_ex.
    destruct (H2 _ H0); discriminate.
  Qed.

  Lemma AbsR_add_EnsembleReplace
  : forall nr kv or v,
      BoundedStringCacheADT_AbsR or nr
      -> StringIndexedMap.find (elt:=Value) (fst kv) nr = Some v
      -> BoundedStringCacheADT_AbsR
           (EnsembleReplace kv or)
           (StringIndexedMap.add (fst kv) (snd kv) nr).
  Proof.
    unfold EnsembleReplace, EnsembleRemove,
    BoundedStringCacheADT_AbsR;
    intros; intuition.
    destruct (string_dec k (fst kv)); subst.
    left.
    rewrite (StringIndexedMap.find_1 (StringIndexedMap.add_1 nr (snd kv) (refl_equal (fst kv))))
      in *; destruct kv; simpl in *; f_equal; congruence.
    right; split; eauto.
    eapply H.
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_3,
    StringIndexedMap.find_2.
    subst; simpl in *.
    eexists; eauto using StringIndexedMap.find_1, StringIndexedMap.add_1.
    destruct (string_dec k (fst kv)); subst.
    eexists; eauto using StringIndexedMap.find_1, StringIndexedMap.add_1.
    destruct (H k).
    destruct (H4 _ H3).
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_2,
    StringIndexedMap.find_2.
  Qed.

  Lemma AbsR_add_EnsembleInsert
  : forall nr kv or,
      BoundedStringCacheADT_AbsR or nr
      -> StringIndexedMap.find (elt:=Value) (fst kv) nr = None
      -> BoundedStringCacheADT_AbsR
           (fun kv' => kv' = kv \/ or kv')
           (StringIndexedMap.add (fst kv) (snd kv) nr).
  Proof.
    unfold SubEnsembleInsert, BoundedStringCacheADT_AbsR;
    intros; intuition.
    destruct (string_dec k (fst kv)); subst.
    left.
    rewrite (StringIndexedMap.find_1 (StringIndexedMap.add_1 nr (snd kv) (refl_equal (fst kv))))
      in *; destruct kv; simpl in *; f_equal; congruence.
    right.
    pose proof (H k); intuition.
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_3,
    StringIndexedMap.find_2.
    subst; simpl in *.
    eexists; eauto using StringIndexedMap.find_1, StringIndexedMap.add_1.
    destruct (string_dec k (fst kv)); subst.
    eexists; eauto using StringIndexedMap.find_1, StringIndexedMap.add_1.
    destruct (H k).
    destruct (H3 _ H2).
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_2,
    StringIndexedMap.find_2.
  Qed.

  Lemma AbsR_add_EnsembleInsertRemove
  : forall nr or k kv,
      BoundedStringCacheADT_AbsR or nr
      -> StringIndexedMap.find (elt:=Value) (fst kv) nr = None
      -> BoundedStringCacheADT_AbsR
           (EnsembleInsert kv (EnsembleRemove k or))
           (StringIndexedMap.add (fst kv) (snd kv) (StringIndexedMap.remove k nr)).
  Proof.
    unfold SubEnsembleInsert, EnsembleRemove,
    EnsembleInsert, BoundedStringCacheADT_AbsR;
    intros; intuition.
    destruct (string_dec k0 (fst kv)); subst.
    left;
    rewrite (StringIndexedMap.find_1 (StringIndexedMap.add_1 _ (snd kv) (refl_equal (fst kv))))
      in H1; destruct kv; simpl in *; f_equal; congruence.
    right; destruct (string_dec k0 k); subst.
    elimtype False; eapply StringIndexedMap.remove_1 with (x := k); eauto.
    eapply StringIndexedMap.find_2 in H1.
    eapply StringIndexedMap.add_3 in H1; eauto.
    unfold StringIndexedMap.In, StringIndexedMap.Raw.In0; eauto.
    intuition.
    eapply H.
    eapply StringIndexedMap.find_1.
    eapply StringIndexedMap.remove_3; eauto.
    eapply StringIndexedMap.add_3; clear n0; eauto.
    eapply StringIndexedMap.find_2; eauto.
    subst; simpl.
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_1.
    destruct (string_dec k0 (fst kv)); subst.
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_1.
    destruct (H k0).
    destruct (H4 _ H3).
    eexists.
    eapply StringIndexedMap.find_2 in H5.
    eapply StringIndexedMap.remove_2 in H5.
    eapply StringIndexedMap.add_2 in H5; eauto.
    eapply StringIndexedMap.find_1; eauto.
    simpl in *; congruence.
  Qed.

  Tactic Notation "refine" "pick" "val" constr(v) :=
    let T := type of v in
    rewrite refine_pick_val with
    (A := T)
      (a := v).

  Tactic Notation "erefine" "pick" "val" open_constr(v) :=
    let T := type of v in
    erewrite refine_pick_val with
    (A := T)
      (a := v) by reflexivity.

  Definition BoundedStringCacheADT' :
    Sharpened (@CacheSpec string Value).
  Proof.
    unfold CacheSpec; simpl.
    hone representation using BoundedStringCacheADT_AbsR.

    hone constructor "EmptyCache".
    {
      simplify with monad laws.
      rewrite refine_pick_val with
      (A := StringIndexedMap.t Value)
      (a := StringIndexedMap.empty Value).
      finish honing.
      unfold BoundedStringCacheADT_AbsR; intros; intuition.
      eapply (StringIndexedMap.empty_1); eauto.
      eapply (StringIndexedMap.find_2); eauto.
    }

    hone method "LookupKey".
    {
      simplify with monad laws.
      refine pick val (StringIndexedMap.find n r_n).
      simplify with monad laws; simpl.
      rewrite refine_pick_val by eauto.
      simplify with monad laws.
      finish honing.
      unfold BoundedStringCacheADT_AbsR, ValidLookup in *;
        intros; pose proof (H0 n); intuition.
    }

    hone method "UpdateKey".
    {
      rewrite refine_pick_decides;
        simplify with monad laws.
      rewrite refine_pick_val by eauto using decides_usedKey.
      simplify with monad laws.
      eapply refine_if with
      (b := if StringIndexedMap.find (elt:=Value) (fst n) r_n then true else false).
      {
        (* If the Key is used, do this. *)
        caseEq (StringIndexedMap.find (elt:=Value) (fst n) r_n);
        try discriminate; simpl.
        rewrite refineEquiv_pick_eq; simplify with monad laws; simpl.
        rewrite refine_pick_val by
          eauto using AbsR_add_EnsembleReplace.
        simplify with monad laws.
        reflexivity.
      }
      {
        (* If the Key isn't in the cache, do this. *)
        caseEq (StringIndexedMap.find (elt:=Value) (fst n) r_n);
        try discriminate; simpl.
        erefine pick val (_, _).
        simplify with monad laws.
        rewrite refine_pick_val by eauto.
        simplify with monad laws; simpl; reflexivity.
      }
    }

    hone method "AddKey".
    {
      rewrite refine_pick_decides;
      simplify with monad laws.
      rewrite refine_pick_val by eauto using decides_usedKey.
      simplify with monad laws.
      eapply refine_if with
      (b := if StringIndexedMap.find (elt:=Value) (fst n) r_n then true else false).
      {
        (* If the Key is used, do nothing. *)
        caseEq (StringIndexedMap.find (elt:=Value) (fst n) r_n);
        try discriminate; simpl.
        erefine pick val (_, _).
        simplify with monad laws.
        rewrite refine_pick_val by eauto.
        simplify with monad laws; simpl; reflexivity.
      }
      {
        (* If the Key is not used, do this. *)
        caseEq (StringIndexedMap.find (elt:=Value) (fst n) r_n);
        try discriminate; simpl.
        refine pick_pair.
        setoid_rewrite refineEquiv_pick_eq; simplify with monad laws.
        (* Check if there is a key worth removing *)
        etransitivity;
          [ eapply (refine_Pick_Some (A := StringIndexedMap.t Value * bool)
                                     (fun kv => StringIndexedMap.find (fst kv) r_n = Some (snd kv)))
          | ].
        { (* If so, replace it. *)
          intros.
          refine pick val (EnsembleInsert n (EnsembleRemove (fst b) or)).
          simplify with monad laws; simpl.
          rewrite refine_pick_val
            by eauto using AbsR_add_EnsembleInsertRemove.
          simplify with monad laws.
          higher_order_1_reflexivity.
          unfold SubEnsembleInsert, EnsembleInsert, EnsembleRemove; eauto.
        }
        {
          (* If not, do a standard insert. *)
          refine pick val (EnsembleInsert n or).
          simplify with monad laws; simpl.
          rewrite refine_pick_val
            by eauto using AbsR_add_EnsembleInsert.
          simplify with monad laws.
          reflexivity.
          unfold SubEnsembleInsert, EnsembleInsert, EnsembleRemove; eauto.
        }
        (* Here's where we can decide how to pick the element to
         replace. Picking None lets the cache grow unboundedly. *)
        refine pick val (@None (StringIndexedMap.key * Value) ).
        try simplify with monad laws.
        reflexivity.
        intuition; try discriminate.
      }

    }

    finish sharpening.

  Defined.

End BoundedStringCacheADT.
