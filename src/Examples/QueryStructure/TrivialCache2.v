Ltac typeof' a := type of a.

Require Import QueryStructureNotations.
Require Import ListImplementation.
Require Import AddCache ADTCache.
Require Import String_as_OT.
Require Import FMapAVL.

Module StringIndexedMap := FMapAVL.Make String_as_OT.
Definition MapStringNat := StringIndexedMap.t nat.

Definition MySchema :=
  Query Structure Schema
    [ relation "Person" has
          schema <"Age" :: nat,
                  "Name" :: string>;
      relation "Dog" has
          schema <"Owner" :: string,
                  "Name" :: string,
                  "Breed" :: string> ]
    enforcing [].

Definition Person := TupleDef MySchema "Person".
Definition Dog := TupleDef MySchema "Dog".

Definition MySig : ADTSig :=
  ADTsignature {
      "Empty" : unit → rep,
      "AddDog" : rep × Dog → rep × bool,
      "YoungOwners'Breeds" : rep × nat → rep × list string,
      "BreedPopulation" : rep × string → rep × nat
  }.

Definition MySpec : ADT MySig :=
  QueryADTRep MySchema {
    const "Empty" (_ : unit) : rep := empty,

   update "AddDog" (dog : Dog) : bool :=
      Insert dog into "Dog",

    query "YoungOwners'Breeds" ( ageLimit : nat ) : list string :=
      For (d in "Dog")
          (o in "Person")
          Where (ageLimit > o!"Age")
          Where (d!"Name" = o!"Name")
          Return (d!"Breed"),

    query "BreedPopulation" ( breed : string ) : nat :=
        Count (For (d in "Dog")
                   Where (d!"Breed" = breed)
                   Return ())
}.

Definition BreedCacheSpec
           (or : UnConstrQueryStructure MySchema)
           (cache : Ensemble (string * nat)) :=
  forall BreedCount,
    cache BreedCount ->
    refine
    (Count (For (UnConstrQuery_In or ``("Dog")
                                  (fun d =>
                                     Where (d!"Breed" = (fst BreedCount))
                                           Return ()))))
    (ret (snd BreedCount)).

Definition MyListImpl_abs
           (or : cachedRep (UnConstrQueryStructure MySchema) (Ensemble (string * nat)))
           (nr : (list Person * list Dog) * MapStringNat) : Prop :=
  ((origRep or) ! "Person" ≃ fst (fst nr) /\
   (origRep or) ! "Dog" ≃ snd (fst nr) ) /\
  forall BreedCount, cachedVal or BreedCount <->
                     StringIndexedMap.MapsTo (fst BreedCount) (snd BreedCount) (snd nr).

Lemma refine_under_bind' {A B}
: forall c (x y : A -> Comp B),
    (forall a, computes_to c a -> refine (x a) (y a))
    -> refine (a <- c; x a) (a <- c; y a).
Proof.
  unfold refine; intros; inversion_by computes_to_inv;
  econstructor; eauto.
Qed.

Definition My :
  Sharpened MySpec.
Proof.
  unfold MySpec.

  pose_string_ids.
  Print Ltac pose_string_ids.

  start honing QueryStructure.

  hone representation using (cachedRep_AbsR BreedCacheSpec).

  hone method "YoungOwners'Breeds".
  { simplify with monad laws.
    setoid_rewrite (refine_pick_val _ H0).
    simplify with monad laws; simpl.
    unfold cachedRep_AbsR in H0; intuition; subst.
    finish honing.
  }

  hone method "BreedPopulation".
  { simplify with monad laws.

    unfold cachedRep_AbsR in H0; intuition; subst.

    eapply (refine_Pick_Some (fun Count => cachedVal r_n (n, Count))); intros.

    { intros; destruct_ex.
      unfold BreedCacheSpec in H2.
      subst_strings.
      setoid_rewrite (H2 _ H0).
      simplify with monad laws; cbv beta; simpl.
      rewrite refine_pick_val; eauto.
      simplify with monad laws; cbv beta; simpl.
      higher_order_1_reflexivity.
      econstructor; eauto.
    }

    { intros; unfold BreedCacheSpec in H2.
      subst_body.
      apply refine_under_bind'; intros.
      (* Check to see if the cache isn't fully populated. *)
      eapply (refine_Pick_Some
                (EnsembleListEquivalence.EnsembleListEquivalence (cachedVal r_n))).
      intros; apply (@refine_if _ _ (if (lt_dec (length b) 10) then true
                    else false)).
      (* If so, insert this query into the cache. *)
      intros; rewrite refine_pick_cachedRep.
      simpl; simplify with monad laws.
      rewrite refine_pick_val with
      (A := Ensemble (string * nat))
        (a := EnsembleInsert (n, a) (cachedVal r_n)).
      simplify with  monad laws.
      reflexivity.
      unfold BreedCacheSpec, EnsembleInsert; intros;
      intuition.
      subst; simpl.
      intros v Comp_v; apply computes_to_inv in Comp_v;
      subst; eauto.
      (* If not, Check and see if there are any Breeds in the cache with
       smaller populations. *)
      intros.
      eapply (refine_Pick_Some
                (fun BreedCount => cachedVal r_n BreedCount
                                   /\ (a > snd BreedCount)
                                   /\ (forall BreedCount',
                                         cachedVal r_n BreedCount' ->
                                         snd BreedCount >= snd BreedCount'))); intros;
      [ split_and
      | rewrite refine_pick_val;
        [ simplify with monad laws; cbv beta; simpl; reflexivity
        | econstructor; simpl; eauto]
      ].
      (* If so, drop the smallest one and add the new one. *)
      rewrite refine_pick_cachedRep.
      simpl; simplify with monad laws.
      rewrite refine_pick_val with
      (A := Ensemble (string * nat))
      (a := EnsembleInsert (n, a)
                           (fun BreedCount =>
                              b0 <> BreedCount
                              /\ cachedVal r_n BreedCount)).
      simplify with monad laws.
      higher_order_1_reflexivity.
      intros BreedCount InBreedCount.
      unfold EnsembleInsert in InBreedCount; intuition; subst.
      simpl.
      unfold refine; intros; inversion_by computes_to_inv; subst; eauto.
      (* If the cache isn't enumerable, then don't touch it. *)
      intros.
    }
  }

  hone constructor "Empty".
  { simplify with monad laws.
    rewrite refine_pick_cachedRep.
    rewrite refine_pick_val with (A := Ensemble (string * nat))
                                   (a := fun _ => False).
    simplify with monad laws; finish honing.
    unfold BreedCacheSpec; simpl.
    intuition.
  }

  hone method "AddDog".
  {
    simplify with monad laws; cbv beta; simpl.
    etransitivity.
    eapply refine_bind_pick; intros.
    rewrite refine_pick_cachedRep.
    simplify with monad laws.
    subst_strings.
    eapply (refine_Pick_Some (fun Count => cachedVal r_n (n!"Breed", Count))); intros.

    (* If this breed is cached. *)
    { unfold cachedRep_AbsR, BreedCacheSpec in *; split_and; subst.
      set (n!"Breed") in *.
      simpl in d.
      rewrite refine_pick_val with
      (A := Ensemble (string * nat))
      (a := EnsembleInsert (d, S b)
                           (fun BreedCount =>
                              fst BreedCount <> d
                              /\ cachedVal r_n BreedCount)).
      simplify with monad laws.
      higher_order_1_reflexivity.
      unfold EnsembleInsert at 1; simpl; intros; intuition.
      - subst_strings.
        rewrite refine_For_In_Insert.
        rewrite refine_Count_bind_bind_app.
        unfold Query_Where at 1, Query_Return at 1.
        rewrite refine_pick_val by
            (subst; cbv [GetAttribute']; simpl; split;
             [ econstructor
             | congruence ]).
        rewrite refine_Count by
            (subst; eapply H2); simplify with monad laws.
        simpl; erewrite (H4 (fst BreedCount, _)) by
                 (subst; eauto).
        simplify with monad laws; subst; simpl; reflexivity.
        unfold In, not; intros; eapply H1; eauto.
      - subst_strings.
        rewrite refine_For_In_Insert.
        rewrite refine_Count_bind_bind_app.
        unfold Query_Where at 1, Query_Return at 1.
        rewrite refine_pick_val
          by (subst; cbv [GetAttribute'] in *; simpl; split;
              [ try congruence
              | econstructor ]).
        rewrite refine_Count by
            (subst; eapply H2); simplify with monad laws.
        simpl; erewrite H4 by eauto.
        reflexivity.
        unfold In, not; intros; eapply H1; eauto.
    }
    { rewrite (@refine_pick_val _ (cachedVal r_n)).
      simplify with monad laws; reflexivity.
      unfold cachedRep_AbsR in *; intuition; subst.
      unfold BreedCacheSpec; intros.
      subst_strings.
      rewrite refine_For_In_Insert.
      rewrite refine_Count_bind_bind_app.
      unfold Query_Where at 1, Query_Return at 1.
      rewrite refine_pick_val by
          (cbv [GetAttribute'] in *; simpl in *; split;
           [ destruct BreedCount; intros; elimtype False; eapply H2;
             rewrite H3; eapply H0
           | econstructor ]).
        rewrite refine_Count by
            (subst; eapply H2); simplify with monad laws.
        eapply H4; eauto.
        unfold In, not; intros; eapply H1; eauto.
    }
    destruct H0; subst.
    finish honing.
  }

  hone representation using MyListImpl_abs.

  hone method "YoungOwners'Breeds".
  {
    simplify with monad laws; simpl.
    unfold MyListImpl_abs in *; intuition.
    rewrite refine_List_Query_In by apply H3.
    rewrite refine_Join_List_Query_In by apply H0.
    rewrite refine_List_Query_In_Where.
    rewrite refine_List_Query_In_Where.
    rewrite refine_List_For_Query_In_Return;
      pose_string_ids; simplify with monad laws; simpl.
    let H := fresh in
    pose (refineEquiv_pick_pair
            (fun nr => EnsembleIndexedListEquivalence
                         ((origRep or)!StringId2)%QueryImpl
                         (fst nr) /\
                       EnsembleIndexedListEquivalence
                         ((origRep or)!StringId3)%QueryImpl
                         (snd nr))
            (fun nr => (forall BreedCount : string * nat,
                          cachedVal or BreedCount <->
                          StringIndexedMap.MapsTo (fst BreedCount)
                                                  (snd BreedCount) nr)))
      as H;
    simpl in H; rewrite H; clear H.
    rewrite refineEquiv_pick_pair.
    simpl in *.
    simplify with monad laws.
    rewrite refine_pick_val by eauto.
    simplify with monad laws.
    rewrite refine_pick_val by eauto.
    simplify with monad laws.
    rewrite refine_pick_val by eauto.
    simplify with monad laws.
    finish honing.
  }

  hone constructor "Empty".
  { simplify with monad laws.
    unfold MyListImpl_abs, GetUnConstrRelation; simpl.
    rewrite (@refineEquiv_pick_pair_pair
                  (list Person)
                  (list Dog)
                  (nat)
                  (EnsembleIndexedListEquivalence (fun _ : IndexedTuple => False))
                  (EnsembleIndexedListEquivalence (fun _ : IndexedTuple => False))
                  (fun c : nat => 0 = c)).
    rewrite refine_pick_val by
        apply EnsembleIndexedListEquivalence_Empty;
    simplify with monad laws.
    rewrite refine_pick_val by
        apply EnsembleIndexedListEquivalence_Empty;
      simplify with monad laws.
    rewrite refineEquiv_pick_eq';
      simplify with monad laws.
    finish honing.
  }


  hone method "BreedPopulation".
  {
    eapply refine_if with (b := if (string_dec n "Dachshund")
                                then true
                                else false);
    find_if_inside; try congruence; intros;
    simplify with monad laws; simpl.

    {
      unfold MyListImpl_abs in *; intuition.
      setoid_rewrite refineEquiv_pick_pair_pair.
      setoid_rewrite refineEquiv_pick_eq'.
      simplify with monad laws.
      rewrite refine_pick_val by eassumption.
      simplify with monad laws.
      rewrite refine_pick_val by eassumption.
      simplify with monad laws.
      rewrite H3.
      reflexivity.
    }

    {
      unfold MyListImpl_abs in *; split_and.
      rewrite refine_Count; simplify with monad laws.
      rewrite refine_List_Query_In by eassumption.
      simpl; subst_body.
      setoid_rewrite refine_List_Query_In_Where.
      rewrite refine_List_For_Query_In_Return;
        simplify with monad laws; simpl.
      setoid_rewrite refineEquiv_pick_pair_pair.
      setoid_rewrite refineEquiv_pick_eq'.
      simplify with monad laws.
      rewrite refine_pick_val by eassumption.
      simplify with monad laws.
      rewrite refine_pick_val by eassumption.
      simplify with monad laws.
      rewrite H3.
      reflexivity.
    }
    }

  hone method "AddDog".
  {
    unfold MyListImpl_abs in *; split_and.
    simplify with monad laws; simpl.
    rewrite refine_pick_val with (A := nat) (a := length (snd (fst r_n))).
    simplify with monad laws; simpl.
    pose_string_ids.
    setoid_rewrite refineEquiv_pick_pair_pair; simpl.
    setoid_rewrite refineEquiv_pick_eq'.
    simplify with monad laws.
    subst_strings.
      match goal with
          |- context
               [{a | EnsembleIndexedListEquivalence
                       ((@UpdateUnConstrRelation ?QSSchema ?c ?Ridx
                                                (EnsembleInsert ?n (?c!?R)))!?R')%QueryImpl a}%comp] =>
          let H := fresh in
          generalize ((@ImplementListInsert_neq QSSchema
                                                {| bindex := R' |}
                                                {| bindex := R |} n c)) as H; intros; setoid_rewrite H
      end; try reflexivity; try eassumption.
      simplify with monad laws.
      match goal with
          |- context
               [{a | EnsembleIndexedListEquivalence
                       ((@UpdateUnConstrRelation ?QSSchema ?c ?Ridx
                                                (EnsembleInsert ?n (?c!?R)))!?R)%QueryImpl a}%comp] =>
          let H := fresh in
          generalize ((@ImplementListInsert_eq QSSchema
                                                {| bindex := R |}
                                                n c)) as H; intros; setoid_rewrite H
      end; try reflexivity; try eassumption.
      simplify with monad laws.
      rewrite H2.
      finish honing.
      congruence.
      intros; destruct H3 as [H3 _].
      intros; eapply lt_irrefl.
      setoid_rewrite <- H4 in H3; eapply H3.
      eauto.
  }

  finish sharpening.
Defined.
