Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Fiat.Computation Fiat.ADT Fiat.ADTRefinement Fiat.ADTNotation Fiat.ADTRefinement.BuildADTRefinements.

Open Scope string_scope.

Section CacheADT.

  Variable Key : Type.
  Variable Value : Type.

  Definition CacheSig : ADTSig :=
    ADTsignature {
        "EmptyCache"  : unit → rep,
        "AddKey" : rep × (Key * Value) → rep × bool,
        "UpdateKey" : rep × (Key * (Value -> Value)) → rep × bool,
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

  Definition EnsembleUpdate
             (k : Key)
             (ens : Ensemble (Key * Value))
             (f : Value -> Value)
             (kv : Key * Value)
  : Prop := ((fst kv) = k /\ exists v, (snd kv) = f v /\ In _ ens (k, v)) \/
            (EnsembleRemove k ens kv).

  Lemma SubEnsembleInsertReplace
  : forall (kv : Key * Value)
           (r : Ensemble (Key * Value)),
   SubEnsembleInsert kv r (EnsembleReplace kv r).
  Proof.
    unfold SubEnsembleInsert, EnsembleInsert,
    EnsembleReplace, EnsembleRemove; intros; intuition.
  Qed.

  Lemma SubEnsembleInsertRefl
  : forall (kv : Key * Value)
           (r : Ensemble (Key * Value)),
   SubEnsembleInsert kv r r.
  Proof.
    unfold SubEnsembleInsert, EnsembleInsert,
    EnsembleReplace, EnsembleRemove; intros; eauto.
  Qed.

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
            { r' | (SubEnsembleInsert kv r (fst r')) /\
                   ((usedKey r (fst kv) /\ snd r' = false) \/
                    (~ usedKey r (fst kv) /\ snd r' = true))},
        meth "UpdateKey" (r : rep, kv : Key * (Value -> Value)) : bool :=
              { r' |
                (Same_set _ (fst r') (EnsembleUpdate (fst kv) r (snd kv)))
                 /\ ((usedKey r (fst kv) /\ snd r' = true) \/
                     (~ usedKey r (fst kv) -> snd r' = false))},
        meth "LookupKey" (r : rep, k : Key) : option Value :=
                v <- {v | ValidLookup r k v};
        ret (r, v)
      }.

End CacheADT.

Section AddDuplicateKeyStrategies.

  Variable Key : Type.
  Variable Value : Type.

  (* Two strategies : replace the key*)

  Lemma refine_ReplaceUsedKeyAdd
  : forall (kv : Key * Value)
           (r : Ensemble (Key * Value)),
      refine { r' | (SubEnsembleInsert kv r (fst r')) /\
                    ((usedKey r (fst kv) /\ snd r' = false) \/
                     (~ usedKey r (fst kv) /\ snd r' = true))}
             (b <- {b | decides b (usedKey r (fst kv))};
              r' <- If b
                 Then (ret (EnsembleReplace kv r))
                 Else { r' | SubEnsembleInsert kv r r' };
              ret (r', negb b)).
  Proof.
    etransitivity.
    apply refine_pick_decides with
            (P := usedKey r (fst kv));
      intros; refine pick pair;
    (apply refine_bind;
     [reflexivity |
      unfold pointwise_relation; intros;
      refine pick val _;
      [simplify with monad laws; higher_order_1_reflexivity
      | intuition ]]).
    f_equiv; unfold pointwise_relation; intros.
    destruct a; simpl.
    - refine pick val _; try reflexivity.
      apply SubEnsembleInsertReplace.
    - reflexivity.
  Qed.

  Lemma refine_IgnoreUsedKeyAdd
  : forall (kv : Key * Value)
           (r : Ensemble (Key * Value)),
      refine { r' | (SubEnsembleInsert kv r (fst r')) /\
                    ((usedKey r (fst kv) /\ snd r' = false) \/
                     (~ usedKey r (fst kv) /\ snd r' = true))}
             (b <- {b | decides b (usedKey r (fst kv))};
              r' <- If b
                 Then (ret r)
                 Else { r' | SubEnsembleInsert kv r r' };
              ret (r', negb b)).
  Proof.
    etransitivity.
    apply refine_pick_decides with
            (P := usedKey r (fst kv));
      intros; refine pick pair;
    (apply refine_bind;
     [reflexivity |
      unfold pointwise_relation; intros;
      refine pick val _;
      [simplify with monad laws; higher_order_1_reflexivity
      | intuition ]]).
    f_equiv; unfold pointwise_relation; intros.
    destruct a; simpl.
    - refine pick val _; try reflexivity.
      apply SubEnsembleInsertRefl.
    - reflexivity.
  Qed.

End AddDuplicateKeyStrategies.

Section UpdateMissingKeyStrategies.

  Variable Key : Type.
  Variable Value : Type.

  (* Best Practice : Update the key, if its there. *)

  Lemma refine_IgnoreUnusedKeyUpdate
  : forall (kv : Key * (Value -> Value))
           (r : Ensemble (Key * Value)),
      refine { r' |
                (Same_set _ (fst r') (EnsembleUpdate (fst kv) r (snd kv)))
                 /\ ((usedKey r (fst kv) /\ snd r' = true) \/
                     (~ usedKey r (fst kv) -> snd r' = false))}
             (b <- {b | decides b (usedKey r (fst kv))};
              r' <- ret (EnsembleUpdate (fst kv) r (snd kv));
              ret (r', b)).
  Proof.
    etransitivity.
    apply refine_pick_decides with
            (P := usedKey r (fst kv));
      intros; refine pick pair;
    (apply refine_bind;
     [reflexivity |
      unfold pointwise_relation; intros;
      refine pick val _;
      [simplify with monad laws; higher_order_1_reflexivity
      | intuition ]]).
    apply refine_under_bind.
    destruct a; simpl; intros.
    - refine pick val _; [reflexivity | intuition ].
    - inversion_by computes_to_inv; simpl in H.
      f_equiv.
      apply refine_pick_val.
      unfold Same_set, Included; intuition; unfold In in *.
  Qed.

End UpdateMissingKeyStrategies.

Section CacheEvictionStrategies.

  Variable Key : Type.
  Variable Value : Type.

  (* First refinement- determine if there is a key to be replaced. *)

  Lemma refine_SubEnsembleInsert
  : forall (kv : Key * Value)
           (r : Ensemble (Key * Value)),
      refine { r' | (SubEnsembleInsert kv r r')}
             (k_opt <- {k_opt | forall k',
                                    k_opt = Some k' ->
                                    exists v', r (k', v')};
              Ifopt k_opt as k' Then
                                  ret (EnsembleInsert kv
                                                      (EnsembleRemove k' r))
                                  Else
                                  ret (EnsembleInsert kv r)).
  Proof.
    intros; rewrite refine_Pick_If_Then_Opt with
            (P := fun k' => exists v', r (k', v')).
    f_equiv; unfold pointwise_relation; intros; simpl.
    destruct a;
      [ higher_order_1_reflexivity
      | reflexivity ].
    simpl; intros; apply refine_pick_val;
    unfold Same_set, Included, In, SubEnsembleInsert, EnsembleInsert,
    EnsembleRemove in *; simpl; intros; intuition.
    simpl; intros; apply refine_pick_val;
    unfold Same_set, Included, In, SubEnsembleInsert, EnsembleInsert,
    EnsembleRemove in *; simpl; intros; intuition.
  Qed.

  (* Never tab a key for replacement *)
  Lemma refine_pick_KeyToBeReplaced_never
  : forall (r : Ensemble (Key * Value)),
      refine {k_opt | forall k',
                         k_opt = Some k' ->
                         exists v', r (k', v')}
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
      refine {k_opt | forall k',
                         k_opt = Some k' ->
                         exists v', fst r (k', v')}
             {k_opt | forall k',
                         k_opt = Some k' ->
                         ((exists v', fst r (k', v'))
                          /\ (forall idx ki,
                                snd r (k', idx) ->
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
      refine {k_opt | forall k',
                         k_opt = Some k' ->
                         exists v', fst r (k', v')}
             {k_opt | forall k',
                         k_opt = Some k' ->
                         ((exists v', fst r (k', v'))
                          /\ (forall idx ki,
                                snd r (k', idx) ->
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

    Lemma KVEnsemble_EquivalentKeys_Remove {B C} :
      forall (ens : Ensemble (Key * B))
             (ens' : Ensemble (Key * C))
             (EquivKeys : KVEnsemble_EquivalentKeys ens ens')
             (a : Key),
             KVEnsemble_EquivalentKeys (EnsembleRemove a ens)
                                       (EnsembleRemove a ens').
    Proof.
      unfold KVEnsemble_EquivalentKeys, EnsembleRemove in *;
        simpl in *; intuition.
      apply H in H3; destruct_ex; eauto.
      apply H0 in H3; destruct_ex; eauto.
    Qed.

    Lemma KVEnsemble_EquivalentKeys_Replace {B C} :
      forall (ens : Ensemble (Key * B))
             (ens' : Ensemble (Key * C))
             (EquivKeys : KVEnsemble_EquivalentKeys ens ens')
             kb c,
             KVEnsemble_EquivalentKeys (EnsembleReplace kb ens)
                                       (EnsembleReplace (fst kb, c) ens').
    Proof.
      unfold KVEnsemble_EquivalentKeys, EnsembleReplace,
        EnsembleRemove in *;
        simpl in *; intuition; injections; eauto.
      apply H in H3; destruct_ex; eauto.
      apply H0 in H3; destruct_ex; eauto.
    Qed.

    Lemma KVEnsemble_EquivalentKeys_Update {B C} :
      forall (ens : Ensemble (Key * B))
             (ens' : Ensemble (Key * C))
             (EquivKeys : KVEnsemble_EquivalentKeys ens ens')
             k f g,
             KVEnsemble_EquivalentKeys (EnsembleUpdate k ens f)
                                       (EnsembleUpdate k ens' g).
    Proof.
      unfold KVEnsemble_EquivalentKeys, EnsembleUpdate,
        EnsembleReplace, EnsembleRemove in *;
        simpl in *; intuition; injections; eauto; subst.
      destruct_ex; intuition; eauto; subst.
      apply H in H3; destruct_ex; eauto.
      exists (g x0); left; intuition; eauto.
      apply H in H3; destruct_ex; eauto.
      destruct_ex; intuition; subst.
      apply H0 in H3; destruct_ex;
      eexists; left; intuition; eauto.
      apply H0 in H3; destruct_ex;  eauto.
    Qed.

    Lemma KVEnsemble_EquivalentKeys_Refl {B} :
      forall (ens : Ensemble (Key * B)),
        KVEnsemble_EquivalentKeys ens ens.
    Proof.
      unfold KVEnsemble_EquivalentKeys, EnsembleRemove in *;
      simpl in *; intuition; eauto.
    Qed.

    Lemma KVEnsemble_EquivalentKeys_Insert {B C} :
      forall (ens : Ensemble (Key * B))
             (ens' : Ensemble (Key * C))
             (EquivKeys : KVEnsemble_EquivalentKeys ens ens')
             (ab : Key * B) (c : C),
             KVEnsemble_EquivalentKeys (EnsembleInsert ab ens)
                                       (EnsembleInsert (fst ab, c) ens').
    Proof.
      unfold refine; intros.
      unfold KVEnsemble_EquivalentKeys, EnsembleInsert in *;
        simpl in *; intuition; injections; eauto.
      apply H in H2; destruct_ex; eauto.
      apply H0 in H2; destruct_ex; eauto.
    Qed.

    Definition PickID {A} (_ : A) := True.

    Lemma refine_pick_KVEnsembleInsert {B C} :
      forall (ens : Ensemble (Key * B))
             (ens' : Ensemble (Key * C))
             (EquivKeys : KVEnsemble_EquivalentKeys ens ens')
             (ab : Key * B),
             refine
             {ens'' | KVEnsemble_EquivalentKeys
                        (EnsembleInsert ab ens) ens''}
             (b <- {b | @PickID C b};
              ret (EnsembleInsert (fst ab, b) ens')).
    Proof.
      unfold refine; intros; inversion_by computes_to_inv;
      subst; econstructor.
      eauto using KVEnsemble_EquivalentKeys_Insert,
      KVEnsemble_EquivalentKeys_Remove.
    Qed.

    Lemma refine_pick_KVEnsembleInsertRemove {B C} :
      forall (ens : Ensemble (Key * B))
             (ens' : Ensemble (Key * C))
             (EquivKeys : KVEnsemble_EquivalentKeys ens ens')
             (ab : Key * B) k,
        refine
             {ens'' | KVEnsemble_EquivalentKeys
                        (EnsembleInsert
                           ab
                           (EnsembleRemove k ens)) ens''}
             (b <- {b | @PickID C b};
              ret (EnsembleInsert (fst ab, b)
                                  (EnsembleRemove k ens'))).
    Proof.
      unfold refine; intros; inversion_by computes_to_inv;
      subst; econstructor.
      eauto using KVEnsemble_EquivalentKeys_Insert,
      KVEnsemble_EquivalentKeys_Remove.
    Qed.

    Lemma refine_pick_KVEnsembleRemove {B C} :
      forall (ens : Ensemble (Key * B))
             (ens' : Ensemble (Key * C))
             (EquivKeys : KVEnsemble_EquivalentKeys ens ens')
             k,
             refine
             {ens'' | KVEnsemble_EquivalentKeys
                        (EnsembleRemove k ens) ens''}
             (ret (EnsembleRemove k ens')).
    Proof.
      unfold refine; intros; inversion_by computes_to_inv;
      subst; econstructor.
      eauto using KVEnsemble_EquivalentKeys_Remove.
    Qed.

    Lemma refine_pick_KVEnsembleReplace {B C} :
      forall (ens : Ensemble (Key * B))
             (ens' : Ensemble (Key * C))
             (EquivKeys : KVEnsemble_EquivalentKeys ens ens')
             k,
             refine
             {ens'' | KVEnsemble_EquivalentKeys
                        (EnsembleReplace k ens) ens''}
             (b <- {b | @PickID C b};
              ret (EnsembleReplace (fst k, b) ens')).
    Proof.
      unfold refine; intros; inversion_by computes_to_inv;
      subst; econstructor.
      eauto using KVEnsemble_EquivalentKeys_Replace.
    Qed.

    Lemma refine_pick_KVEnsembleUpdate {B C}
    : forall (ens : Ensemble (Key * B))
                (ens' : Ensemble (Key * C))
                (EquivKeys : KVEnsemble_EquivalentKeys ens ens')
                k f,
             refine
               {ens'' | KVEnsemble_EquivalentKeys
                          (EnsembleUpdate k ens f) ens''}
               (b <- {b | @PickID C b};
                ret (EnsembleUpdate k ens' (fun _ => b))).
    Proof.
      unfold refine; intros; inversion_by computes_to_inv;
      subst; econstructor.
      eauto using KVEnsemble_EquivalentKeys_Update.
    Qed.

    Lemma refine_pick_KVEnsemble {B C} :
      forall (ens : Ensemble (Key * B))
             (ens' : Ensemble (Key * C))
             (EquivKeys : KVEnsemble_EquivalentKeys ens ens'),
             refine
          {ens'' | KVEnsemble_EquivalentKeys ens ens''}
          (ret ens').
    Proof.
      unfold refine; intros; inversion_by computes_to_inv;
      subst; econstructor.
      eauto.
    Qed.
  End LogicalIndex.

End CacheEvictionStrategies.

Require Import String_as_OT.
Require Import FMapAVL.
Module StringIndexedMap := FMapAVL.Make String_as_OT.
Definition MapStringNat := StringIndexedMap.t nat.

Section BoundedStringCacheADT.

(* This is a cache which ignores updates to missing values
   and uses an LRU strategy to pick any elements to remove.
 *)

  Variable Value : Type.
  Variable Bound : nat.

  Definition EnsembleFMapEquivalence {A}
             (ens : Ensemble (string * A))
             (fmap : StringIndexedMap.t A) :=
    forall k,
      (forall a, StringIndexedMap.find k fmap = Some a ->
                 ens (k, a))
      /\ (forall a, ens (k, a) ->
                    StringIndexedMap.find k fmap = Some a).

  Definition FMapCommonKeys {A B}
             (values : StringIndexedMap.t A)
             (indices : StringIndexedMap.t B)
    := forall k,
         (forall a, StringIndexedMap.MapsTo k a values ->
                    exists b, StringIndexedMap.MapsTo k b indices)
         /\ (forall b, StringIndexedMap.MapsTo k b indices ->
                    exists a, StringIndexedMap.MapsTo k a values).

  Definition indexBound
             (indices : StringIndexedMap.t nat)
             (indicesBound : nat)
    := forall k idx,
         StringIndexedMap.find k indices = Some idx ->
         idx <= indicesBound.

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

  Lemma decides_usedKey
  : forall (or : Ensemble (string * Value))
           (nr : StringIndexedMap.t Value)
           (k : string),
      EnsembleFMapEquivalence or nr ->
      decides (if StringIndexedMap.find k nr then
                 true else
                 false)
              (usedKey or k).
  Proof.
    unfold EnsembleFMapEquivalence, usedKey; intros;
    pose proof (H k); intuition.
    find_if_inside; simpl; eauto.
    intuition; destruct_ex.
    apply H2 in H0; discriminate.
  Qed.

  Lemma AbsR_add_EnsembleReplace {A}
  : forall nr kv or v,
      EnsembleFMapEquivalence or nr
      -> StringIndexedMap.find (elt:=A) (fst kv) nr = Some v
      -> EnsembleFMapEquivalence
           (EnsembleReplace kv or)
           (StringIndexedMap.add (fst kv) (snd kv) nr).
  Proof.
    unfold EnsembleReplace, EnsembleRemove,
    EnsembleFMapEquivalence;
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
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_1.
    destruct (string_dec k (fst kv)); subst.
    simpl in H1; congruence.
    destruct (H k).
    generalize (H4 _ H3).
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_2,
    StringIndexedMap.find_2.
  Qed.

  Lemma AbsR_add_EnsembleUpdate {A}
  : forall nr k f or v,
      EnsembleFMapEquivalence or nr
      -> StringIndexedMap.find (elt:=A) k nr = Some v
      -> EnsembleFMapEquivalence
           (EnsembleUpdate k or f)
           (StringIndexedMap.add k (f v) nr).
  Proof.
    unfold EnsembleUpdate, EnsembleRemove,
    EnsembleFMapEquivalence;
    intros; intuition.
    destruct (string_dec k0 k); subst.
    left.
    rewrite (StringIndexedMap.find_1 (StringIndexedMap.add_1 nr (f v) (refl_equal k)))
      in *; simpl in *; f_equal; injections; intuition.
    eexists; split; eauto.
    eapply H; eauto.
    right; split; eauto.
    eapply H.
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_3,
    StringIndexedMap.find_2.
    subst; simpl in *.
    destruct_ex; intuition; subst.
    apply H in H3; rewrite H0 in H3; injections.
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_1.
    apply H in H3.
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_2,
    StringIndexedMap.find_2.
  Qed.

  Lemma AbsR_add_EnsembleUpdate' {A}
  : forall nr k f or,
      EnsembleFMapEquivalence or nr
      -> StringIndexedMap.find (elt:=A) k nr = None
      -> EnsembleFMapEquivalence (EnsembleUpdate k or f) nr.
  Proof.
    unfold EnsembleUpdate, EnsembleRemove,
    EnsembleFMapEquivalence;
    intros; intuition.
    destruct (string_dec k0 k); subst.
    rewrite H0 in H1; discriminate.
    right; intuition; eapply H; eauto.
    subst; simpl in *.
    destruct_ex; intuition; eapply H in H3; subst.
    destruct_ex; rewrite H0 in *; discriminate.
    eapply H; eauto.
  Qed.

  Lemma AbsR_add_EnsembleInsert {A}
  : forall nr kv or,
      EnsembleFMapEquivalence or nr
      -> StringIndexedMap.find (elt:=A) (fst kv) nr = None
      -> EnsembleFMapEquivalence
           (fun kv' => kv' = kv \/ or kv')
           (StringIndexedMap.add (fst kv) (snd kv) nr).
  Proof.
    unfold SubEnsembleInsert, EnsembleFMapEquivalence;
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
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_1.
    destruct (string_dec k (fst kv)); subst.
    apply H in H2.
    rewrite H0 in H2; discriminate.
    apply H in H2.
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_2,
    StringIndexedMap.find_2.
  Qed.

  Lemma AbsR_remove_EnsembleRemove {A}
  : forall nr or k,
      EnsembleFMapEquivalence (A := A) or nr
      -> EnsembleFMapEquivalence
           (EnsembleRemove k or)
           (StringIndexedMap.remove k nr).
  Proof.
    unfold EnsembleRemove, EnsembleFMapEquivalence;
    intros; intuition; simpl in *; subst.
    eapply StringIndexedMap.remove_1; try reflexivity;
    unfold StringIndexedMap.In, StringIndexedMap.Raw.In0;
    simpl; apply StringIndexedMap.find_2 in H0;
    unfold StringIndexedMap.MapsTo, StringIndexedMap.remove in H0;
    simpl in H0; eauto.
    destruct (string_dec k0 k); subst; simpl in *.
    elimtype False.
    eapply StringIndexedMap.remove_1; try reflexivity;
    unfold StringIndexedMap.In, StringIndexedMap.Raw.In0;
    simpl; apply StringIndexedMap.find_2 in H0;
    unfold StringIndexedMap.MapsTo, StringIndexedMap.remove in H0;
    simpl in H0; eauto.
    apply StringIndexedMap.find_2 in H0.
    apply StringIndexedMap.remove_3 in H0; eapply H;
    eauto using StringIndexedMap.find_1.
    apply StringIndexedMap.find_1.
    apply StringIndexedMap.remove_2; eauto.
    eapply H in H2.
    eauto using StringIndexedMap.find_2.
  Qed.

  Lemma AbsR_add_EnsembleInsertRemove {A}
  : forall nr or kv,
      EnsembleFMapEquivalence (A := A) or nr
      -> EnsembleFMapEquivalence
           (EnsembleInsert kv (EnsembleRemove (fst kv) or))
           (StringIndexedMap.add (fst kv) (snd kv) nr).
  Proof.
    unfold SubEnsembleInsert, EnsembleRemove,
    EnsembleInsert, EnsembleFMapEquivalence;
    intros; intuition.
    destruct (string_dec k a); subst; simpl in *.
    rewrite (StringIndexedMap.find_1 (StringIndexedMap.add_1 _ b (refl_equal a)))
      in H0; left; f_equal; congruence.
    right; intuition;
    apply StringIndexedMap.find_2 in H0;
      apply StringIndexedMap.add_3 in H0; eauto.
    eapply H; eauto using StringIndexedMap.find_1.
    unfold StringIndexedMap.In, StringIndexedMap.Raw.In0,
    StringIndexedMap.MapsTo in *; simpl in *; eauto.
    injections.
    eauto using StringIndexedMap.find_1,
    StringIndexedMap.add_1.
    apply H in H2; simpl in *.
    apply StringIndexedMap.find_1;
      apply StringIndexedMap.add_2; eauto.
    eauto using StringIndexedMap.find_1,
      StringIndexedMap.add_2, StringIndexedMap.remove_2,
      StringIndexedMap.find_2.
  Qed.

  Lemma FMapCommonKeys_add {A B}
  : forall k a b
           (ens : StringIndexedMap.t A)
           (ens' : StringIndexedMap.t B),
      FMapCommonKeys ens ens'
      -> FMapCommonKeys
           (StringIndexedMap.add k a ens)
           (StringIndexedMap.add k b ens').
  Proof.
    unfold FMapCommonKeys; intuition;
    (destruct (string_dec k0 k);
     [eexists; eapply StringIndexedMap.add_1; eauto
     |
     eapply StringIndexedMap.add_3 in H0; eauto;
     apply H in H0; destruct_ex;
     eexists; eapply StringIndexedMap.add_2; eauto]).
  Qed.

  Lemma FMapCommonKeys_remove {A B}
  : forall k
           (ens : StringIndexedMap.t A)
           (ens' : StringIndexedMap.t B),
      FMapCommonKeys ens ens'
      -> FMapCommonKeys
           (StringIndexedMap.remove k ens)
           (StringIndexedMap.remove k ens').
  Proof.
    unfold FMapCommonKeys; intuition;
    (destruct (string_dec k0 k);
     [subst; elimtype False;
      eapply (StringIndexedMap.remove_1); eauto;
      unfold StringIndexedMap.In, StringIndexedMap.Raw.In0,
      StringIndexedMap.MapsTo in *; simpl in *; eauto
     |
     eapply StringIndexedMap.remove_3 in H0;
       apply H in H0; destruct_ex;
       eauto using StringIndexedMap.remove_2 ]).
  Qed.

  Lemma indexBound_add
  : forall indices k n,
      indexBound indices n
      -> indexBound (StringIndexedMap.add k n indices) (S n).
  Proof.
    unfold indexBound; intros.
    destruct (string_dec k k0).
    rewrite (StringIndexedMap.find_1 (StringIndexedMap.add_1 _ _ e)) in H0.
    injections; omega.
    apply StringIndexedMap.find_2 in H0.
    eapply StringIndexedMap.add_3 in H0; eauto.
    apply StringIndexedMap.find_1 in H0; eauto.
  Qed.

  Lemma indexBound_add_remove
  : forall indices k k' n,
      indexBound indices n
      -> indexBound (StringIndexedMap.add k n
                                          (StringIndexedMap.remove k' indices)) (S n).
  Proof.
    unfold indexBound; intros.
    destruct (string_dec k k0).
    rewrite (StringIndexedMap.find_1 (StringIndexedMap.add_1 _ _ e)) in H0.
    injections; omega.
    apply StringIndexedMap.find_2 in H0.
    eapply StringIndexedMap.add_3 in H0; eauto.
    destruct (string_dec k' k0).
    elimtype False;
      eapply (StringIndexedMap.remove_1); eauto;
      unfold StringIndexedMap.In, StringIndexedMap.Raw.In0,
      StringIndexedMap.MapsTo in *; simpl in *; eauto.
    apply StringIndexedMap.remove_3 in H0; eauto.
    apply StringIndexedMap.find_1 in H0; eauto.
  Qed.

  Definition find_minimum_Key
             (indices : StringIndexedMap.t nat)
  : option (string * nat) :=
    StringIndexedMap.fold
      (fun k idx sv =>
         Ifopt sv as sv'
                       Then
                         if (lt_dec idx (snd sv') )
                         then Some (k, idx)
                         else Some sv'
                       Else
                         Some (k, idx))
      indices None.

  Lemma fold_left_In :
    forall l kv p',
   fold_left
     (fun (a : option (StringIndexedMap.key * nat))
        (p : StringIndexedMap.key * nat) =>
      Ifopt a as sv'
      Then if lt_dec (snd p) (snd sv') then Some (fst p, snd p) else Some sv'
      Else Some p) l p' =
   Some kv ->
   (Some kv = p') \/
   SetoidList.InA
     (fun p p' : string * nat => fst p = fst p' /\ snd p = snd p')
     kv l.
  Proof.
    clear; induction l; simpl; intros; subst; eauto.
    destruct p'; simpl in H.
    destruct (lt_dec (snd a) (snd p)).
    destruct (IHl _ _ H).
    right; constructor; injections; simpl; eauto.
    right; constructor 2; eauto.
    destruct (IHl _ _ H).
    injections; eauto.
    eauto.
    right; destruct (IHl _ _ H); injections; eauto.
  Qed.

  Lemma fold_left_min_opt :
    forall l kv p',
   fold_left
     (fun (a : option (StringIndexedMap.key * nat))
        (p : StringIndexedMap.key * nat) =>
      Ifopt a as sv'
      Then if lt_dec (snd p) (snd sv') then Some (fst p, snd p) else Some sv'
      Else Some p) l (Some p') =
   Some kv ->
   snd kv <= snd p'.
  Proof.
    clear; induction l; simpl; intros; subst; eauto.
    injections; eauto.
    destruct (lt_dec (snd a) (snd p')).
    apply le_trans with (m := snd a); eauto with arith.
    eauto.
  Qed.

  Lemma find_minimum_Key_In :
    forall indices kv,
      find_minimum_Key indices = Some kv ->
      StringIndexedMap.MapsTo (elt:=nat) (fst kv) (snd kv) indices.
  Proof.
    intros.
    unfold find_minimum_Key in H.
    rewrite StringIndexedMap.fold_1 in H.
    eapply StringIndexedMap.elements_2.
    destruct (@fold_left_In (StringIndexedMap.elements (elt:=nat) indices) kv None); intuition.
    unfold StringIndexedMap.key in *.
    rewrite <- H; f_equal.
    repeat (apply functional_extensionality; intros); f_equal;
    intuition.
    discriminate.
    destruct kv.
    unfold StringIndexedMap.eq_key_elt, StringIndexedMap.Raw.Proofs.PX.eqke; eauto.
  Qed.

  Lemma find_minimum_Key_correct :
    forall indices kv,
      find_minimum_Key indices = Some kv ->
      forall k v, StringIndexedMap.find k indices = Some v ->
                  snd kv <= v.
  Proof.
    intros.
    unfold find_minimum_Key in H.
    rewrite StringIndexedMap.fold_1 in H.
    apply StringIndexedMap.find_2 in H0.
    apply StringIndexedMap.elements_1 in H0.
    unfold StringIndexedMap.eq_key_elt in H0.
    unfold StringIndexedMap.Raw.Proofs.PX.eqke in H0.
    assert (   forall (k0 : StringIndexedMap.key) (v0 : nat) p',
   fold_left
     (fun (a : option (StringIndexedMap.key * nat))
        (p : StringIndexedMap.key * nat) =>
      Ifopt a as sv'
      Then if lt_dec (snd p) (snd sv') then Some (fst p, snd p) else Some sv'
      Else Some p)
     (StringIndexedMap.elements (elt:=nat) indices) (Some p') =
   Some kv ->

   SetoidList.InA
     (fun p p' : string * nat => fst p = fst p' /\ snd p = snd p')
     (k0, v0) (StringIndexedMap.elements (elt:=nat) indices)
   -> ((snd kv <= snd p') /\( snd kv <= v0 ))).
    { clear; induction (StringIndexedMap.elements (elt:=nat) indices);
      simpl; intros; subst; eauto.
      destruct p'; simpl in H.
      inversion H0; subst; intuition; simpl in *; subst; eauto.
      destruct (lt_dec (snd a) (snd p')).
      inversion H0; subst.
      intuition; simpl in *; intros; subst.
      destruct (fold_left_In _ _ H); injections; simpl;
      auto with arith.
      destruct kv.
      destruct (IHl _ _ _ H H1); simpl in *.
      eauto with arith.
      destruct (fold_left_In _ _ H); injections; simpl;
      auto with arith.
      destruct kv.
      destruct (IHl _ _ _ H H1); simpl in *; eauto with arith.
      intuition.
      destruct (IHl _ _ _ H H2); simpl in *.
      omega.
      destruct (IHl _ _ _ H H2); simpl in *; eauto.
      inversion H0; subst.
      destruct (fold_left_In _ _ H); injections; simpl;
      intuition; simpl in *; subst.
      apply not_gt.
      auto with arith.
      destruct kv.
      destruct (IHl _ _ _ H H1); simpl in *; eauto.
      destruct kv.
      destruct (IHl _ _ _ H H1); simpl in *; eauto.
      eapply le_trans.
      eapply H2.
      apply not_gt; auto with arith.
      destruct (IHl _ _ _ H H2); eauto.
    }
    destruct ((StringIndexedMap.elements (elt:=nat) indices)).
    simpl in H; discriminate.
    simpl in H.
    eapply H1 with (p' := p); eauto.
    simpl.
    destruct (lt_dec (snd p) (snd p)); eauto.
    elimtype False.
    omega.
    rewrite <- H; f_equal.
    repeat (apply functional_extensionality; intros); f_equal.
    destruct x0; reflexivity.
    destruct p; eauto.
  Qed.

  Lemma refine_pick_oldest {V} :
    forall spec_indices impl_indices
           spec_values impl_values,
    EnsembleFMapEquivalence spec_indices impl_indices /\
    EnsembleFMapEquivalence spec_values impl_values /\
    FMapCommonKeys impl_values impl_indices
    ->  refine {k_opt | forall k' : string,
                          k_opt = Some k' ->
                          ((exists v' : V, spec_values (k', v'))
                           /\ (forall (idx : nat) (ki : string * nat),
                                 spec_indices (k', idx) -> spec_indices ki -> idx <= snd ki))}
               (ret (option_map fst (find_minimum_Key impl_indices))).
  Proof.
    unfold refine; intros; inversion_by computes_to_inv; subst.
    econstructor; intros.
    caseEq (find_minimum_Key impl_indices); rewrite H2 in *;
    simpl in *; try discriminate; injections.
    unfold EnsembleFMapEquivalence in *.
    pose proof (find_minimum_Key_correct _ H2).
    pose proof (find_minimum_Key_In _ H2).
    split; intros.
    unfold FMapCommonKeys in H3.
    destruct (H3 (fst p)).
    destruct (H6 (snd p)); eauto.
    destruct (H (fst p)); eexists; eauto.
    eapply H8.
    eauto using StringIndexedMap.find_1.
    apply H1 in H5; destruct ki; eapply H1 in H6. destruct_ex;
    simpl in *.
    eapply StringIndexedMap.find_1 in H4; rewrite H5 in H4.
    injection H4; intros; subst; eauto.
  Qed.

  Lemma refine_If_Then_Else'
  : forall (A : Type) (c : bool) (x x0 y y0 : Comp A),
      (c = true -> refine x y)
      -> (c = false -> refine x0 y0)
      -> refine (If c Then x Else x0) (If c Then y Else y0).
  Proof.
    unfold refine; intros; destruct c; auto.
  Qed.

  Lemma FMapCommonKeys_find_None {A B}
  : forall m m' k,
      FMapCommonKeys m m'
      -> StringIndexedMap.find (elt:=A) k m = None
      -> StringIndexedMap.find (elt:=B) k m' = None .
  Proof.
    intros.
    caseEq (StringIndexedMap.find (elt:=B) k m'); eauto.
    apply StringIndexedMap.find_2 in H1.
    apply H in H1.
    destruct_ex.
    apply StringIndexedMap.find_1 in H1.
    rewrite H1 in H0; discriminate.
  Qed.

  Lemma StringIndexedMap_find_None_remove {V}
  : forall k k' m,
      StringIndexedMap.find (elt:=V) k m = None
      -> StringIndexedMap.find
           (elt:=V) k
           (StringIndexedMap.remove k' m) = None.
  Proof.
    intros.
    caseEq (StringIndexedMap.find (elt:=V) k (StringIndexedMap.remove (elt:=V) k' m)); eauto.
    apply StringIndexedMap.find_2 in H0.
    apply StringIndexedMap.remove_3 in H0;
      apply StringIndexedMap.find_1 in H0;
      congruence.
  Qed.

Tactic Notation "rewrite" "with" "monad" "laws" :=
  repeat first [ setoid_rewrite refineEquiv_bind_bind
               | setoid_rewrite refineEquiv_bind_unit
               | setoid_rewrite refineEquiv_unit_bind].

(* To keep the presentation clean for the paper, we'll
 split and rename the premise holding the abstraction. *)
Ltac split_CacheADTwLogIndex_AbsR :=
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
        split_CacheADTwLogIndex_AbsR.
        setoid_rewrite refine_pick_CacheADTwLogIndex_AbsR.
        setoid_rewrite refine_ReplaceUsedKeyAdd.
        setoid_rewrite refine_SubEnsembleInsert.
        rewrite with monad laws.
        setoid_rewrite refine_pick_KeyToBeReplaced_min.
        setoid_rewrite refine_If_Then_Else_Bind.
        rewrite with monad laws.
        setoid_rewrite refine_If_Opt_Then_Else_Bind.
        rewrite with monad laws.
        pose proof refine_pick_KVEnsembleInsertRemove.
        setoid_rewrite refine_pick_KVEnsembleInsertRemove
                       with (1 := EquivKeys_H).
        setoid_rewrite refine_pick_KVEnsembleInsert
                       with (1 := EquivKeys_H).
        rewrite with monad laws; simpl.
        finish honing.
      }
      hone method "UpdateKey".
      {
        split_CacheADTwLogIndex_AbsR.
        setoid_rewrite refine_pick_CacheADTwLogIndex_AbsR.
        setoid_rewrite refine_IgnoreUnusedKeyUpdate.
        rewrite with monad laws.
        setoid_rewrite refine_pick_KVEnsembleUpdate
                       with (1 := EquivKeys_H).
        rewrite with monad laws; simpl.
        finish honing.
      }
      hone method "LookupKey".
      {
        split_CacheADTwLogIndex_AbsR.
        setoid_rewrite refine_pick_CacheADTwLogIndex_AbsR.
        rewrite with monad laws.
        setoid_rewrite (refine_pick_KVEnsemble EquivKeys_H).
        rewrite with monad laws;  simpl.
        finish honing.
      }

      hone representation using BoundedStringCacheADT_AbsR.

      hone constructor "EmptyCache".
      { simplify with monad laws.
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
      simplify with monad laws.
      refine pick val (StringIndexedMap.find n (fst (fst r_n))).
      simplify with monad laws; simpl.
      rewrite refine_pick_val by eauto.
      simplify with monad laws.
      finish honing.
      unfold BoundedStringCacheADT_AbsR, ValidLookup in *;
        eapply H0.
    }

    hone method "UpdateKey".
    {
      unfold BoundedStringCacheADT_AbsR in *; split_and.
      simplify with monad laws.
      rewrite refine_pick_val by eauto using decides_usedKey.
      simplify with monad laws; simpl.
      refine pick val (snd r_n); unfold PickID; eauto;
      simplify with monad laws.
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
        eauto using AbsR_add_EnsembleUpdate.
        apply StringIndexedMap.find_2 in H3.
        apply H2 in H3; destruct_ex.
        eapply AbsR_add_EnsembleUpdate with (f := fun _ => snd r_n);
          eauto using StringIndexedMap.find_1.
        eauto using FMapCommonKeys_add.
        eauto using indexBound_add.
      }
      {
        refine pick val _; eauto.
        simplify with monad laws; simpl.
        reflexivity.
        caseEq (StringIndexedMap.find (elt:=Value) (fst n) (fst (fst r_n)));
          try solve [elimtype False; eapply H3; eauto];
          intuition; eauto using AbsR_add_EnsembleUpdate'.
        eapply AbsR_add_EnsembleUpdate'; eauto using FMapCommonKeys_find_None.
      }
      refine pick val (StringIndexedMap.find (elt:=Value) (fst n) (fst (fst r_n)));
        try (split; congruence).
      simplify with monad laws.
      finish honing.
    }

    hone method "AddKey".
    {
      unfold BoundedStringCacheADT_AbsR in *; split_and.
      simplify with monad laws.
      rewrite refine_pick_val by eauto using decides_usedKey.
      simplify with monad laws.
      setoid_rewrite refine_If_Then_Else_Bind.
      etransitivity.
      apply refine_If_Then_Else';
        caseEq (StringIndexedMap.find (elt:=Value) (fst n) (fst (fst r_n))); simpl; try discriminate.
      (* If the key is used, do this. *)
      + simplify with monad laws.
        refine pick val (snd r_n); unfold PickID; eauto.
        simplify with monad laws; simpl.
        refine pick val ((_, _), _);
          [ |
            simpl; intuition;
            simpl; eauto using
                         AbsR_add_EnsembleReplace,
                   FMapCommonKeys_remove,
                   FMapCommonKeys_add,
                   AbsR_add_EnsembleInsertRemove,
                   indexBound_add].
        simplify with monad laws.
        reflexivity.
        eapply (AbsR_add_EnsembleInsertRemove (fst n, snd r_n) H0).
      + (* If the key is not used, do this. *)
        simplify with monad laws.
        (* Check to see if we've hit the bound. *)
        apply (refine_if (b := if (gt_dec (snd r_n) Bound)
                               then true
                               else false)); intros.
        (* If we have, then pick a key to remove. *)
        rewrite refine_pick_oldest; eauto.
        simplify with monad laws.
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
                     AbsR_remove_EnsembleRemove,
                     StringIndexedMap_find_None_remove,
                     FMapCommonKeys_add,
                     indexBound_add_remove].
          simplify with monad laws; simpl.
          higher_order_1_reflexivity.
          apply (@AbsR_add_EnsembleInsert nat);
            eauto using
                AbsR_add_EnsembleInsert, AbsR_remove_EnsembleRemove,
          StringIndexedMap_find_None_remove.
          apply StringIndexedMap_find_None_remove.
          eapply FMapCommonKeys_find_None; eauto.
        * refine pick val (snd r_n); unfold PickID; eauto.
          simplify with monad laws; simpl.
          refine pick val ((_, _), S (snd r_n));
            [ |
              simpl; intuition
                       simpl; eauto using
                                    AbsR_add_EnsembleInsert,
                              FMapCommonKeys_add,
                              indexBound_add;
              eapply (AbsR_add_EnsembleInsert (_, _));
              simpl; eauto using FMapCommonKeys_find_None].
          simplify with monad laws.
          reflexivity.
        * refine pick val None; try discriminate.
          simplify with monad laws.
          refine pick val (snd r_n); unfold PickID; eauto.
          simplify with monad laws; simpl.
          refine pick val ((_, _), S (snd r_n));
            [ |
              simpl; intuition
                       simpl; eauto using
                                    AbsR_add_EnsembleInsert,
                              FMapCommonKeys_add,
                              indexBound_add;
              eapply (AbsR_add_EnsembleInsert (_, _));
              simpl; eauto using FMapCommonKeys_find_None].
          simplify with monad laws.
          reflexivity.
      + finish honing.
    }

    finish sharpening.
    Defined.
F
End BoundedStringCacheADT.
