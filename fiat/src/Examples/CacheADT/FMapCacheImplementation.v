Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Computation ADT ADTRefinement ADTNotation BuildADTRefinements
        KVEnsembles CacheSpec CacheRefinements.

Require Import String_as_OT.
Require Import FMapAVL.
Module StringIndexedMap := FMapAVL.Make String_as_OT.
Definition MapStringNat := StringIndexedMap.t nat.

Section StringKEnsembles.

(* Implementation of Ensembles of String + Value pairs using
   finite maps. *)

  Variable Value : Type.

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

  Lemma AbsR_add_EnsembleReplaceKey {A}
  : forall nr kv or v,
      EnsembleFMapEquivalence or nr
      -> StringIndexedMap.find (elt:=A) (fst kv) nr = Some v
      -> EnsembleFMapEquivalence
           (EnsembleReplaceKey kv or)
           (StringIndexedMap.add (fst kv) (snd kv) nr).
  Proof.
    unfold EnsembleReplaceKey, EnsembleRemoveKey,
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

  Lemma AbsR_add_EnsembleUpdateKey {A}
  : forall nr k f or v,
      EnsembleFMapEquivalence or nr
      -> StringIndexedMap.find (elt:=A) k nr = Some v
      -> EnsembleFMapEquivalence
           (EnsembleUpdateKey k or f)
           (StringIndexedMap.add k (f v) nr).
  Proof.
    unfold EnsembleUpdateKey, EnsembleRemoveKey,
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

  Lemma AbsR_add_EnsembleUpdateKey' {A}
  : forall nr k f or,
      EnsembleFMapEquivalence or nr
      -> StringIndexedMap.find (elt:=A) k nr = None
      -> EnsembleFMapEquivalence (EnsembleUpdateKey k or f) nr.
  Proof.
    unfold EnsembleUpdateKey, EnsembleRemoveKey,
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

  Lemma AbsR_remove_EnsembleRemoveKey {A}
  : forall nr or k,
      EnsembleFMapEquivalence (A := A) or nr
      -> EnsembleFMapEquivalence
           (EnsembleRemoveKey k or)
           (StringIndexedMap.remove k nr).
  Proof.
    unfold EnsembleRemoveKey, EnsembleFMapEquivalence;
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
           (EnsembleInsert kv (EnsembleRemoveKey (fst kv) or))
           (StringIndexedMap.add (fst kv) (snd kv) nr).
  Proof.
    unfold SubEnsembleInsert, EnsembleRemoveKey,
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

End StringKEnsembles.

Section BoundedCacheFMap.

  Variable Bound : nat.

  Definition indexBound
             (indices : StringIndexedMap.t nat)
             (indicesBound : nat)
    := forall k idx,
         StringIndexedMap.find k indices = Some idx ->
         idx <= indicesBound.

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

End BoundedCacheFMap.
