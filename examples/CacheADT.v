Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation BuildADTRefinements.

Open Scope ADT.
Open Scope ADTSig.
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

  Definition decides (b : bool) (P : Prop)
    := if b then P else ~ P.

  Definition EnsembleInsert {A} (a : A) (ens : Ensemble A) (a' : A)
  : Prop := a' = a \/ ens a'.

  Definition EnsembleReplace
             (k : Key * Value)
             (ens : Ensemble (Key * Value))
             (k' : Key * Value)
  : Prop := k' = k \/
            (fst k' <> fst k -> ens k').

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
                   (~ usedKey r (fst kv) -> r' = (EnsembleInsert kv r, true))},
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

Lemma refine_pick_decides {A}
      (P : Prop)
      (Q Q' : Ensemble A)
: refine {a | (P -> Q a) /\
              (~ P -> Q' a)}
         (b <- {b | decides b P};
          if b then
            {a | Q a}
          else
            {a | Q' a}).
Proof.
  unfold refine; intros; apply_in_hyp computes_to_inv;
  destruct_ex; split_and; inversion_by computes_to_inv.
  destruct x; simpl in *; inversion_by computes_to_inv;
  econstructor; intuition.
Qed.

Section UnboundedStringCacheADT.

  Variable Value : Type.

  Definition UnboundedStringCacheADT_AbsR
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
      UnboundedStringCacheADT_AbsR or nr ->
      decides (if StringIndexedMap.find k nr then
                 true else
                 false)
              (usedKey or k).
  Proof.
    unfold UnboundedStringCacheADT_AbsR, usedKey; intros;
    pose proof (H k); intuition.
    find_if_inside; simpl; eauto.
    intuition; destruct_ex.
    destruct (H2 _ H0); discriminate.
  Qed.

  Lemma AbsR_add_EnsembleReplace
  : forall nr kv or v,
      UnboundedStringCacheADT_AbsR or nr
      -> StringIndexedMap.find (elt:=Value) (fst kv) nr = Some v
      -> UnboundedStringCacheADT_AbsR
           (EnsembleReplace kv or)
           (StringIndexedMap.add (fst kv) (snd kv) nr).
  Proof.
    unfold EnsembleReplace, UnboundedStringCacheADT_AbsR;
    intros; intuition.
    destruct (string_dec k (fst kv)); subst.
    left.
    rewrite (StringIndexedMap.find_1 (StringIndexedMap.add_1 nr (snd kv) (refl_equal (fst kv))))
      in *; destruct kv; simpl in *; f_equal; congruence.
    right; intros.
    eapply H.
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_3,
    StringIndexedMap.find_2.
    subst; simpl in *.
    eexists; eauto using StringIndexedMap.find_1, StringIndexedMap.add_1.
    destruct (string_dec k (fst kv)); subst.
    eexists; eauto using StringIndexedMap.find_1, StringIndexedMap.add_1.
    destruct (H k).
    destruct (H3 _ (H2 n)).
    eauto using StringIndexedMap.find_1, StringIndexedMap.add_2,
    StringIndexedMap.find_2.
  Qed.

  Lemma AbsR_add_EnsembleInsert
  : forall nr kv or,
      UnboundedStringCacheADT_AbsR or nr
      -> StringIndexedMap.find (elt:=Value) (fst kv) nr = None
      -> UnboundedStringCacheADT_AbsR
           (EnsembleInsert kv or)
           (StringIndexedMap.add (fst kv) (snd kv) nr).
  Proof.
    unfold EnsembleInsert, UnboundedStringCacheADT_AbsR;
    intros; intuition.
    destruct (string_dec k (fst kv)); subst.
    left.
    rewrite (StringIndexedMap.find_1 (StringIndexedMap.add_1 nr (snd kv) (refl_equal (fst kv))))
      in *; destruct kv; simpl in *; f_equal; congruence.
    right; intros.
    eapply H.
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

  Definition UnboundedStringCacheADT' :
    Sharpened (@CacheSpec string Value).
  Proof.
    unfold CacheSpec; simpl.
    hone representation using UnboundedStringCacheADT_AbsR.

    hone constructor "EmptyCache".
    {
      simplify with monad laws.
      rewrite refine_pick_val with
      (A := StringIndexedMap.t Value)
      (a := StringIndexedMap.empty Value).
      finish honing.
      unfold UnboundedStringCacheADT_AbsR; intros; intuition.
      eapply (StringIndexedMap.empty_1); eauto.
      eapply (StringIndexedMap.find_2); eauto.
    }

    hone method "LookupKey".
    {
      simplify with monad laws.
      rewrite refine_pick_val with
      (A := option Value)
        (a := StringIndexedMap.find n r_n).
      simplify with monad laws; simpl.
      rewrite refine_pick_val by eauto.
      simplify with monad laws.
      finish honing.
      unfold UnboundedStringCacheADT_AbsR, ValidLookup in *;
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
        erewrite refine_pick_val with
        (A := prod (Ensemble (string * Value)) bool)
        (a := (_, _)) by reflexivity.
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
        (* If the Key is used, do this. *)
        caseEq (StringIndexedMap.find (elt:=Value) (fst n) r_n);
        try discriminate; simpl.
        erewrite refine_pick_val with
        (A := prod (Ensemble (string * Value)) bool)
        (a := (_, _)) by reflexivity.
        simplify with monad laws.
        rewrite refine_pick_val by eauto.
        simplify with monad laws; simpl; reflexivity.
      }
      {
        caseEq (StringIndexedMap.find (elt:=Value) (fst n) r_n);
        try discriminate; simpl.
        rewrite refineEquiv_pick_eq; simplify with monad laws; simpl.
        rewrite refine_pick_val by
          eauto using AbsR_add_EnsembleInsert.
        simplify with monad laws.
        reflexivity.
      }
    }

    finish sharpening.

  Defined.

End UnboundedStringCacheADT.
