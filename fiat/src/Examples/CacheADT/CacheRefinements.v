Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Computation ADT ADTRefinement ADTNotation BuildADTRefinements
        KVEnsembles CacheSpec.

Section AddDuplicateKeyStrategies.

  Context {Key : Type}.
  Context {Value : Type}.

  (* Two strategies : replace the key*)

  Lemma refine_ReplaceUsedKeyAdd
  : forall (kv : Key * Value)
           (r : Ensemble (Key * Value)),
      refine { r' | (SubEnsembleInsert kv r (fst r')) /\
                    ((usedKey r (fst kv) /\ snd r' = false) \/
                     (~ usedKey r (fst kv) /\ snd r' = true))}
             (b <- {b | decides b (usedKey r (fst kv))};
              r' <- If b
                 Then (ret (EnsembleReplaceKey kv r))
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
      apply SubEnsembleInsertReplaceKey.
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

  Context {Key : Type}.
  Context {Value : Type}.

  (* Best Practice : Just update the key, if its there. *)

  Lemma refine_IgnoreUnusedKeyUpdate
  : forall (kv : Key * (Value -> Value))
           (r : Ensemble (Key * Value)),
      refine { r' |
                (Same_set _ (fst r') (EnsembleUpdateKey (fst kv) r (snd kv)))
                 /\ ((usedKey r (fst kv) /\ snd r' = true) \/
                     (~ usedKey r (fst kv) -> snd r' = false))}
             (b <- {b | decides b (usedKey r (fst kv))};
              r' <- ret (EnsembleUpdateKey (fst kv) r (snd kv));
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

  Context {Key : Type}.
  Context {Value : Type}.

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
                                                      (EnsembleRemoveKey k' r))
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
    EnsembleRemoveKey in *; simpl; intros; intuition.
    simpl; intros; apply refine_pick_val;
    unfold Same_set, Included, In, SubEnsembleInsert, EnsembleInsert,
    EnsembleRemoveKey in *; simpl; intros; intuition.
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
             KVEnsemble_EquivalentKeys (EnsembleRemoveKey a ens)
                                       (EnsembleRemoveKey a ens').
    Proof.
      unfold KVEnsemble_EquivalentKeys, EnsembleRemoveKey in *;
        simpl in *; intuition.
      apply H in H3; destruct_ex; eauto.
      apply H0 in H3; destruct_ex; eauto.
    Qed.

    Lemma KVEnsemble_EquivalentKeys_Replace {B C} :
      forall (ens : Ensemble (Key * B))
             (ens' : Ensemble (Key * C))
             (EquivKeys : KVEnsemble_EquivalentKeys ens ens')
             kb c,
             KVEnsemble_EquivalentKeys (EnsembleReplaceKey kb ens)
                                       (EnsembleReplaceKey (fst kb, c) ens').
    Proof.
      unfold KVEnsemble_EquivalentKeys, EnsembleReplaceKey,
        EnsembleRemoveKey in *;
        simpl in *; intuition; injections; eauto.
      apply H in H3; destruct_ex; eauto.
      apply H0 in H3; destruct_ex; eauto.
    Qed.

    Lemma KVEnsemble_EquivalentKeys_Update {B C} :
      forall (ens : Ensemble (Key * B))
             (ens' : Ensemble (Key * C))
             (EquivKeys : KVEnsemble_EquivalentKeys ens ens')
             k f g,
             KVEnsemble_EquivalentKeys (EnsembleUpdateKey k ens f)
                                       (EnsembleUpdateKey k ens' g).
    Proof.
      unfold KVEnsemble_EquivalentKeys, EnsembleUpdateKey,
        EnsembleReplaceKey, EnsembleRemoveKey in *;
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
      unfold KVEnsemble_EquivalentKeys, EnsembleRemoveKey in *;
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
                           (EnsembleRemoveKey k ens)) ens''}
             (b <- {b | @PickID C b};
              ret (EnsembleInsert (fst ab, b)
                                  (EnsembleRemoveKey k ens'))).
    Proof.
      unfold refine; intros; inversion_by computes_to_inv;
      subst; econstructor.
      eauto using KVEnsemble_EquivalentKeys_Insert,
      KVEnsemble_EquivalentKeys_Remove.
    Qed.

    Lemma refine_pick_KVEnsembleRemoveKey {B C} :
      forall (ens : Ensemble (Key * B))
             (ens' : Ensemble (Key * C))
             (EquivKeys : KVEnsemble_EquivalentKeys ens ens')
             k,
             refine
             {ens'' | KVEnsemble_EquivalentKeys
                        (EnsembleRemoveKey k ens) ens''}
             (ret (EnsembleRemoveKey k ens')).
    Proof.
      unfold refine; intros; inversion_by computes_to_inv;
      subst; econstructor.
      eauto using KVEnsemble_EquivalentKeys_Remove.
    Qed.

    Lemma refine_pick_KVEnsembleReplaceKey {B C} :
      forall (ens : Ensemble (Key * B))
             (ens' : Ensemble (Key * C))
             (EquivKeys : KVEnsemble_EquivalentKeys ens ens')
             k,
             refine
             {ens'' | KVEnsemble_EquivalentKeys
                        (EnsembleReplaceKey k ens) ens''}
             (b <- {b | @PickID C b};
              ret (EnsembleReplaceKey (fst k, b) ens')).
    Proof.
      unfold refine; intros; inversion_by computes_to_inv;
      subst; econstructor.
      eauto using KVEnsemble_EquivalentKeys_Replace.
    Qed.

    Lemma refine_pick_KVEnsembleUpdateKey {B C}
    : forall (ens : Ensemble (Key * B))
                (ens' : Ensemble (Key * C))
                (EquivKeys : KVEnsemble_EquivalentKeys ens ens')
                k f,
             refine
               {ens'' | KVEnsemble_EquivalentKeys
                          (EnsembleUpdateKey k ens f) ens''}
               (b <- {b | @PickID C b};
                ret (EnsembleUpdateKey k ens' (fun _ => b))).
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
