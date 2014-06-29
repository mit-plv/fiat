Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation BuildADTRefinements.

Open Scope string.

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
              { r' | (usedKey r (fst kv) ->
                      (Same_set _ (fst r') (EnsembleReplace kv r)
                       /\ snd r' = true)) /\
                     (~ usedKey r (fst kv) -> snd r' = false)},
        meth "LookupKey" (r : rep, k : Key) : option Value :=
                v <- {v | ValidLookup r k v};
        ret (r, v)
      }.

End CacheADT.

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
              r' <- If_Then_Else b
                 (ret (EnsembleReplace kv r))
                 { r' | SubEnsembleInsert kv r r' };
              ret (r', negb b)).
  Proof.
    unfold If_Then_Else;
    intros; rewrite refine_pick_decides.
    f_equiv; unfold pointwise_relation; intros.
    destruct a.
    - rewrite refineEquiv_bind_unit;
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
              r' <- If_Then_Else b (ret r)
                 { r' | SubEnsembleInsert kv r r' };
              ret (r', negb b)).
  Proof.
    unfold If_Then_Else;
    intros; rewrite refine_pick_decides.
    f_equiv; unfold pointwise_relation; intros.
    destruct a.
    - rewrite refineEquiv_bind_unit;
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

  (* First refinement- determine if there is a key to be replaced. *)

  Lemma refine_SubEnsembleInsert
  : forall (kv : Key * Value)
           (r : Ensemble (Key * Value)),
      refine { r' | (SubEnsembleInsert kv r r')}
             (kv_opt <- {kv_opt | forall kv',
                                    kv_opt = Some kv' -> r kv'};
              {r' | Same_set _ r' match kv_opt with
                                    | Some (kv', _) =>
                                      EnsembleInsert kv
                                            (EnsembleRemove kv' r)
                                    | None => EnsembleInsert kv r
                                  end} ).
  Proof.
    intros; rewrite refine_Pick_Some with
            (P := r).
    f_equiv; unfold pointwise_relation; intros.
    destruct a;
      [ higher_order_1_reflexivity
      | reflexivity ].
    simpl; intros.
    apply refine_pick_pick; destruct b;
    unfold Same_set, Included, In, SubEnsembleInsert, EnsembleInsert,
    EnsembleRemove in *; simpl; intros; intuition.
    destruct (H2 _ H1); intuition.
    apply refine_pick_pick;
    unfold Same_set, Included, In, SubEnsembleInsert, EnsembleInsert,
    EnsembleRemove in *; simpl; intros; intuition.
  Qed.

  (* Never tab a key for replacement *)
  Lemma refine_pick_KeyToBeReplaced_never
  : forall (r : Ensemble (Key * Value)),
      refine {kv_opt | forall kv',
                         kv_opt = Some kv' -> r kv'}
             (ret None).
  Proof.
    intros; rewrite refine_pick_val;
    [ reflexivity
      | discriminate ].
  Qed.

  Section LogicalIndex.

    (* To define various replacement strategies, we're going to
       add a logical index to the pairs of keys and values. *)

    Definition KVEnsemble_EquivalentKeys {A B}
               (ens : Ensemble (Key * A))
               (ens' : Ensemble (Key * B)) :=
      (forall k a, ens (k, a) -> (exists b, ens' (k, b)))
      /\ (forall k b, ens' (k, b) -> (exists a, ens (k, a))).

    Definition CacheADTwLogIndex_AbsR
             (or : Ensemble (Key * Value))
             (nr : Ensemble (Key * Value) *
                   Ensemble (Key * nat))
      := or = (fst nr)
         /\ (KVEnsemble_EquivalentKeys (fst nr) (snd nr)).

    Definition DropLogIndex
               (nr : Ensemble (Key * Value) *
                     Ensemble (Key * nat))
    : Ensemble (Key * Value) :=
      fst nr.

  (* Pick the key with the lowest index for replacement *)
  Lemma refine_pick_KeyToBeReplaced_min
  : forall (r : Ensemble (Key * Value) *
                Ensemble (Key * nat)),
      refine {kv_opt | forall kv',
                         kv_opt = Some kv' -> fst r kv'}
             {kv_opt | forall kv',
                         kv_opt = Some kv' ->
                         (fst r kv'
                          /\ (forall idx ki,
                                snd r (fst kv', idx) ->
                                snd r ki ->
                                idx <= snd ki))
                             }.
  Proof.
    intros; apply refine_pick_pick; intros.
    eapply H; eauto.
  Qed.

  (* Pick the key with the highest index for replacement *)
  Lemma refine_pick_KeyToBeReplaced_max
  : forall (r : Ensemble (Key * Value) *
                Ensemble (Key * nat)),
      refine {kv_opt | forall kv',
                         kv_opt = Some kv' -> fst r kv'}
             {kv_opt | forall kv',
                         kv_opt = Some kv' ->
                         (fst r kv'
                          /\ (forall idx ki,
                                snd r (fst kv', idx) ->
                                snd r ki ->
                                snd ki <= idx))
                             }.
  Proof.
    intros; apply refine_pick_pick; intros.
    eapply H; eauto.
  Qed.

    Lemma refine_LogIndexEmpty
    : refine {nr' |
              CacheADTwLogIndex_AbsR (fun _ : Key * Value => False) nr'}
             (ret (fun _  => False, fun _ => False)).
    Proof.
      apply refine_pick_val;
      unfold CacheADTwLogIndex_AbsR, KVEnsemble_EquivalentKeys; intuition;
      destruct_ex; eauto.
    Qed.

    Lemma refine_LogIndexUsedKey
    : forall n or nr,
        CacheADTwLogIndex_AbsR or nr
        -> refine {b | decides b (usedKey or n)}
               {b | decides b (usedKey (fst nr) n)}.
    Proof.
      unfold CacheADTwLogIndex_AbsR, KVEnsemble_EquivalentKeys;
      intros; apply refine_pick_pick;
      unfold usedKey; simpl; intros; unfold decides;
      find_if_inside; simpl in * ; destruct_ex;
      unfold Same_set, Included, In in *; intuition; subst; eauto.
    Qed.

    Lemma refine_pick_CacheADTwLogIndex_AbsR or' :
          refine
            {nr' | CacheADTwLogIndex_AbsR or' nr'}
            (nr' <- {nr' | KVEnsemble_EquivalentKeys or' nr'};
             ret (or', nr')).
    Proof.
      unfold CacheADTwLogIndex_AbsR; intros.
      setoid_rewrite refineEquiv_pick_pair_snd_dep; simpl.
      refine pick val or'.
      simplify with monad laws; f_equiv.
      unfold Same_set, Included; eauto.
    Qed.

    Lemma refine_pick_KVEnsembleRemove {B} :
      forall (ens ens' : Ensemble (Key * B)) (a : Key),
        KVEnsemble_EquivalentKeys ens ens'
        -> refine
             {ens'' | KVEnsemble_EquivalentKeys (EnsembleRemove a ens) ens''}
             (ret (EnsembleRemove a ens')).
    Proof.
      intros; refine pick val _; try reflexivity.
      unfold KVEnsemble_EquivalentKeys, EnsembleRemove in *;
        simpl in *; intuition.
      apply H0 in H3; destruct_ex; eauto.
      apply H1 in H3; destruct_ex; eauto.
    Qed.

    Lemma refine_pick_KVEnsembleInsert {B} :
      forall (ens ens' : Ensemble (Key * B)) (ab : Key * B),
        KVEnsemble_EquivalentKeys ens ens'
        -> refine
             {ens'' | KVEnsemble_EquivalentKeys (EnsembleInsert ab ens) ens''}
             (b <- Pick (fun b : B => True);
              ret (EnsembleInsert (fst ab, b) ens')).
    Proof.
      unfold refine; intros.
      inversion_by computes_to_inv; subst.
      econstructor.
      unfold KVEnsemble_EquivalentKeys, EnsembleInsert in *;
        simpl in *; intuition; injections; eauto.
      apply H0 in H3; destruct_ex; eauto.
      apply H2 in H3; destruct_ex; eauto.
    Qed.

    Lemma refine_If_Then_Else_Bind {A B}
    : forall i (t e : Comp A) (b : A -> Comp B),
        refine (a <- If_Then_Else i t e; b a)
               (If_Then_Else i
                             (a <- t;
                              b a)
                             (a <- e;
                              b a)).
    Proof.
      intros; destruct i; simpl; reflexivity.
    Qed.


    Definition BoundedStringCacheADT' :
      Sharpened (@CacheSpec Key Value).
    Proof.
      unfold CacheSpec.
      hone representation using CacheADTwLogIndex_AbsR.
      hone constructor "EmptyCache".
      {
        simplify with monad laws.
        rewrite refine_LogIndexEmpty.
        finish honing.
      }
      hone method "AddKey".
      {
        destruct H0; subst.
        setoid_rewrite refine_pick_CacheADTwLogIndex_AbsR;
        simplify with monad laws.
        finish honing.
      }
      hone method "UpdateKey".
      {
        destruct H0; subst.
        setoid_rewrite refine_pick_CacheADTwLogIndex_AbsR;
        simplify with monad laws.
        finish honing.
      }
      hone method "LookupKey".
      {
        destruct H0; subst.
        setoid_rewrite refine_pick_CacheADTwLogIndex_AbsR;
        simplify with monad laws.
        finish honing.
      }
      hone method "AddKey".
      {
        setoid_rewrite refine_ReplaceUsedKey.
        setoid_rewrite refine_SubEnsembleInsert.
        simplify with monad laws.
        setoid_rewrite refine_pick_KeyToBeReplaced_min.
        simpl.
        setoid_rewrite refine_If_Then_Else_Bind.
        setoid_rewrite refineEquiv_bind_unit;
          setoid_rewrite refineEquiv_bind_bind.

        rewrite
        simpl.
        apply refine_bind.
        Focus 2.
        unfold pointwise_relation; intros.
        apply refine_bind.
        Focus.
        apply refine_If_Then_Else.
        reflexivity.
        apply refine_bind.

        apply refine_pick_KeyToBeReplaced_min.

        simplify with monad laws.
        eapply refine_LogIndexLookupSpec; eauto.
      }

    Lemma refine_LogIndexAddSpec
    : forall n or nr,
        CacheADTwLogIndex_AbsR or nr
        -> refine
             (or' <- {r'|
                      (usedKey or (fst n) -> snd r' = false) /\
                      (~ usedKey or (fst n) ->
                       SubEnsembleInsert n or (fst r') /\ snd r' = true)};
              nr' <- {nr' | CacheADTwLogIndex_AbsR (fst or') nr'};
              ret (nr', snd or'))
             ({r' |
               (usedKey (fst nr) (fst n) -> snd r' = false) /\
               (~ usedKey (fst nr) (fst n) ->
                SubEnsembleInsert (fst n, (snd n, idx))
                                    nr (fst r') /\ snd r' = true)}).
    Proof.
      unfold CacheADTwLogIndex_AbsR, usedKey; intros; split_and.
      unfold refine; intros; inversion_by computes_to_inv.
      econstructor 2 with (comp_a_value := (DropLogIndex (fst v), snd v));
        simpl.
      - econstructor; simpl; split.
        intros; destruct_ex.
        apply H0 in H; destruct_ex.
        eapply H2; eauto.
        intros; destruct H3.
        unfold not; intros; apply H;
        destruct_ex; destruct x; eexists; eapply H1; eauto.
        intuition.
        unfold SubEnsembleInsert, DropLogIndex, EnsembleInsert in *.
        intros; destruct_ex; simpl in *.
        destruct (H4 _ H3); destruct a'; destruct n; simpl in *.
        left; congruence.
        right; eauto.
      - econstructor 2 with (comp_a_value := fst v).
        unfold DropLogIndex; econstructor; split; intros; eauto.
        destruct v; eauto.
    Qed.

    Lemma LogIndexEnsembleReplace
    : forall k v idx or nr kvi,
        CacheADTwLogIndex_AbsR or nr
        -> EnsembleReplace (k, (v, idx)) nr kvi
        -> EnsembleReplace (k, v) or (fst kvi, fst (snd kvi)).
    Proof.
      unfold EnsembleReplace, CacheADTwLogIndex_AbsR;
      intros; simpl in *; intuition; subst; simpl; eauto.
      unfold EnsembleRemove in *; simpl in *; right; intuition.
      destruct kvi as [k' [v' i']]; eauto.
    Qed.

    Lemma LogIndexEnsembleReplace'
    : forall k v idx or nr kv,
        CacheADTwLogIndex_AbsR or nr
        -> EnsembleReplace (k, v) or kv
        -> exists idx',
               EnsembleReplace (k, (v, idx)) nr (fst kv, (snd kv, idx')).
    Proof.
      unfold EnsembleReplace, CacheADTwLogIndex_AbsR;
      intros; simpl in *; intuition; subst; simpl; eauto.
      unfold EnsembleRemove in *; simpl in *; intuition.
      destruct kv as [k' v']; simpl in *.
      destruct (H1 _ _ H3).
      exists x; simpl; eauto.
    Qed.

    Lemma refine_LogIndexUpdateSpec
    : forall n or nr,
        CacheADTwLogIndex_AbsR or nr
        -> refine
             (or' <- {r' |
                      (usedKey or (fst n) ->
                       (Same_set _ (fst r') (EnsembleReplace n or)
                        /\ snd r' = true))
                      /\ (~ usedKey or (fst n) -> snd r' = false)};
              nr' <- {nr' | CacheADTwLogIndex_AbsR (fst or') nr'};
              ret (nr', snd or'))
             {r' | (usedKey nr (fst n) ->
                    (exists idx,
                       Same_set _ (fst r')
                                (EnsembleReplace (fst n, (snd n, idx)) nr))
                    /\ snd r' = true)
                   /\ (~ usedKey nr (fst n) -> snd r' = false)}.
    Proof.
      unfold CacheADTwLogIndex_AbsR, usedKey, Same_set; intros; split_and.
      unfold refine; intros; inversion_by computes_to_inv.
      econstructor 2 with (comp_a_value := (DropLogIndex (fst v), snd v));
        simpl.
      - econstructor; simpl; split.
        intros; destruct_ex.
        apply H0 in H2; destruct_ex.
        destruct H; eauto; intuition; eauto.
        unfold SubEnsembleInsert, DropLogIndex, EnsembleInsert,
          Included, In in *; simpl in *; intros; destruct_ex;
        destruct n; destruct x2; simpl in *.
        apply H5 in H.
        eapply (LogIndexEnsembleReplace (nr := nr) (kvi := (k0, (v1, x3)))); try split; eauto.
        unfold DropLogIndex, EnsembleReplace, EnsembleRemove,
        Included, In in *; simpl in *;
        intros; destruct_ex;
        destruct n; destruct x2; simpl in *; intuition; injections.
        eexists; eapply H6; simpl; eauto.
        apply H0 in H8; destruct_ex; eauto.
        intros; eapply H3.
        unfold not; intros; eapply H2.
        destruct_ex; destruct x; eauto.
      - econstructor 2 with (comp_a_value := fst v).
        unfold DropLogIndex; econstructor; split; intros; eauto.
        destruct v; eauto.
    Qed.

    Definition UnLogIndexedEquivalence
               (nr nr' : Ensemble (Key * (Value * nat)))
      := (forall k v i, nr (k, (v, i)) -> (exists i', nr' (k, (v, i'))))
         /\ (forall k v i, nr' (k, (v, i)) -> (exists i', nr (k, (v, i')))).

    Lemma refine_LogIndexLookupSpec
    : forall n or nr,
        CacheADTwLogIndex_AbsR or nr
        -> refine
             (x0 <- {v | ValidLookup or n v};
              nr' <- {nr' | CacheADTwLogIndex_AbsR or nr'};
              ret (nr', x0))
             (x0 <- {v | ValidLookup nr n v};
              nr' <- {nr' | UnLogIndexedEquivalence nr nr'};
              ret (nr', option_map fst x0)).
    Proof.
      unfold CacheADTwLogIndex_AbsR; intros; split_and.
      unfold refine; intros; inversion_by computes_to_inv.
      econstructor 2 with (comp_a_value := option_map fst x).
      - econstructor.
        unfold ValidLookup in *; intros.
        destruct x; simpl in H3; try discriminate.
        destruct p;  eapply H1; eapply H2;
        injections; eauto.
      - subst; econstructor; econstructor.
        split; intros; eauto.
        unfold UnLogIndexedEquivalence in *; split_and.
        destruct (H0 _ _ H); eauto.
        unfold UnLogIndexedEquivalence in *; split_and.
        destruct (H5 _ _ _ H); eauto.
    Qed.

    Definition BoundedStringCacheADT' :
      Sharpened (@CacheSpec Key Value).
    Proof.
      unfold CacheSpec.
      hone representation using CacheADTwLogIndex_AbsR.
      hone constructor "EmptyCache".
      {
        simplify with monad laws.
        rewrite refine_LogIndexEmpty.
        finish honing.
      }
      hone method "AddKey".
      {
        apply refine_LogIndexAddSpec; eauto.
      }
      hone method "UpdateKey".
      {
        apply refine_LogIndexUpdateSpec; eauto.
      }
      hone method "LookupKey".
      {
        simplify with monad laws.
        eapply refine_LogIndexLookupSpec; eauto.
      }
      hone method "AddKey".
      {
        setoid_rewrite refine_ReplaceUsedKey.




 (* *)

  Definition CacheADTwLogIndex_AbsR
             (or : Ensemble (Key * Value))
             (nr : Ensemble (Key * (Value * nat)))
    := forall kv, or (fst kv, fst (snd kv)) <-> nr kv.


    hone method "AddKey".
    hone

    hone method "AddKey".
    {
      rewrite refine_ReplaceUsedKey.
      setoid_rewrite refine_SubEnsembleInsert.
      simpl.
      apply refine_bind.
      reflexivity.
      unfold pointwise_relation; intros.
      apply refine_bind.
      apply refine_if.
      reflexivity.





.
    }

Require Import String_as_OT.
Require Import FMapAVL.

Module StringIndexedMap := FMapAVL.Make String_as_OT.
Definition MapStringNat := StringIndexedMap.t nat.



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
