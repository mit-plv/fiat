Require Import Fiat.QueryStructure.Specification.Representation.QueryStructureNotations.
Require Import Fiat.QueryStructure.Implementation.ListImplementation.
Require Import ComputationalADT AddCache ADTCache CacheADT.

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
  Def ADT {
    rep := QueryStructure MySchema,

   const "Empty" (_ : unit) : rep := empty,,

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

Section CachingRefinement.

  Definition CacheSpec := @CacheSpec string nat.
  Variable LRUCache : Sharpened CacheSpec.
  Definition PopCache := projT1 LRUCache.
  Definition PopCacheAbs : Rep CacheSpec -> Rep PopCache -> Prop :=
    AbsR (projT2 LRUCache).
  (* Definition PopCacheComp := snd (projT2 LRUCache). *)

  (* Definition EmptyCache := CallConstructor PopCacheComp "EmptyCache" ().
  Definition InsertKey r i := CallMethod PopCacheComp "AddKey" r i.
  Definition LookupKey r i := CallMethod PopCacheComp "LookupKey" r i.
  Definition UpdateKey r i := CallMethod PopCacheComp "UpdateKey" r i. *)

  Definition BreedCacheSpec
             (or : UnConstrQueryStructure MySchema)
             (cache : Rep CacheSpec) :=
    forall breed pop,
      cache (breed,  pop)
      -> refine
           (Count (For (UnConstrQuery_In or ``("Dog")
                                         (fun d =>
                                            Where (d!"Breed" = breed)
                                                  Return ()))))
           (ret pop).

  Definition MyListImpl_abs
             (or : cachedRep (UnConstrQueryStructure MySchema) (Rep CacheSpec))
             (nr : (list Person * list Dog) * (Rep PopCache)) : Prop :=
    ((origRep or) ! "Person" ≃ fst (fst nr) /\
     (origRep or) ! "Dog" ≃ snd (fst nr)) /\
    PopCacheAbs (cachedVal or) (snd nr).

  Definition My :
    Sharpened MySpec.
  Proof.
    unfold MySpec.

    start honing QueryStructure.

    hone representation using (cachedRep_AbsR BreedCacheSpec).

    hone method "YoungOwners'Breeds".
    { simplify with monad laws.
      setoid_rewrite (refine_pick_val _ H0).
      simplify with monad laws.
      unfold cachedRep_AbsR in H0; intuition; subst; simpl.
      finish honing.
    }

    hone method "BreedPopulation".
    { simplify with monad laws.
      etransitivity.
      apply refine_Pick_If_Then_Opt with (P := fun v => cachedVal r_n (n, v)); intros.
      { destruct H0; subst; unfold BreedCacheSpec in *|- .
        subst_strings.
        apply H2 in H1.
        rewrite H1.
        simplify with monad laws; cbv beta; simpl.
        refine pick val _; try split; eauto.
        simplify with monad laws.
        finish honing.
      }
      {
        unfold cachedRep_AbsR in *|-; simpl; split_and; subst.
        rewrite refine_under_bind; [reflexivity | ].
        intros; rewrite refine_pick_cachedRep.
        simplify with monad laws.
        assert (refine {cv | BreedCacheSpec (origRep r_n) cv}
                       (c <- (callMeth CacheSpec "AddKey" (cachedVal r_n) (n, a));
                        ret (fst c))).
        repeat econstructor.
        inversion_by computes_to_inv; subst.
        unfold BreedCacheSpec; intros.
        unfold SubEnsembleInsert in H1.
        intros H7; pose proof (H1 _ H3).
        destruct H4; injections.
        unfold refine; intros; inversion_by computes_to_inv; subst; eauto.
        apply H2; eauto.
        rewrite H1.
        simplify with monad laws.
        finish honing.
      }
      finish honing.
    }

    hone constructor "Empty".
    { simplify with monad laws.
      rewrite refine_pick_cachedRep.
      refine pick val (fun _ : string * nat => False).
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
      assert (refine {cv |
                      BreedCacheSpec
                        (UpdateUnConstrRelation or ``(StringId7)
                                                (InsertQSSpecs.EnsembleInsert
                                                   {| tupleIndex := a; indexedTuple := n |}
                                                   (or!StringId7)%QueryImpl)) cv}
                     (r' <- callMeth CacheSpec "UpdateKey" (cachedVal r_n) (n!"Breed", S);
                      ret (fst r'))).
      repeat econstructor.
      inversion_by computes_to_inv; subst.
      unfold BreedCacheSpec; intros.
      simpl; pose_string_ids.
      etransitivity.
      apply refine_refine_Count.
      apply refine_For_In_Insert.
      unfold In, not; intros; eapply H1;
      [ eapply H4
      | subst_body; auto ].
      rewrite refine_Count_bind_bind_app.
      unfold cachedRep_AbsR, BreedCacheSpec in H0; split_and; subst.
      pose_string_ids.
      pose (n!"Breed"); simpl in *.
      etransitivity.
      apply refine_if with (b := if (string_dec d breed)
                                 then true
                                 else false);
        find_if_inside; try discriminate; subst; intros.
      { setoid_rewrite refine_Count at 1; simplify with monad laws;
        unfold Query_Where; refine pick val [()];
        [ | intuition; econstructor].
        simplify with monad laws.
        apply H2 in H3; unfold In in *.
        subst_strings.
        destruct H3; split_and.
        destruct_ex; split_and; subst.
        rewrite (H6 _ _ H8).
        simplify with monad laws; simpl; reflexivity.
        unfold EnsembleRemove in H3; simpl in H3; elimtype False; eapply H3;
        reflexivity.
      }
      {
        setoid_rewrite refine_Count at 1; simplify with monad laws;
        unfold Query_Where; refine pick val [];
        [ | intuition; econstructor].
        simplify with monad laws.
        apply H2 in H3; unfold In in *.
        subst_strings.
        destruct H3; split_and; try congruence.
        destruct H3; rewrite (H6 _ _ H4); reflexivity.
      }
      find_if_inside; reflexivity.
      subst_strings; setoid_rewrite H2.
      simplify with monad laws.
      higher_order_1_reflexivity.
      cbv beta.
      unfold cachedRep_AbsR in H0; intuition.
      subst.
      finish honing.
    }

    hone representation using MyListImpl_abs.
    hone constructor "Empty".
    { simplify with monad laws.
      unfold MyListImpl_abs, GetUnConstrRelation; simpl.
      rewrite refineEquiv_pick_pair_pair.
      rewrite refine_pick_val by
          apply EnsembleIndexedListEquivalence_Empty;
        simplify with monad laws.
      rewrite refine_pick_val by
          apply EnsembleIndexedListEquivalence_Empty;
        simplify with monad laws.
      (* Rewriting with the cache implementation. *)
      assert (refine {c | PopCacheAbs (fun _ : string * nat => False) c}
                     (callCons PopCache "EmptyCache" ())).
      {
        pose (ADTRefinementPreservesConstructors (projT2 LRUCache) {| bindex := "EmptyCache" |}).
        simpl in r; rewrite <- r.
        rewrite refineEquiv_bind_unit; f_equiv.
      }
      rewrite H0.
      finish honing.
    }

    hone method "YoungOwners'Breeds".
    {
      pose_string_ids.
      simplify with monad laws; simpl.
      unfold MyListImpl_abs in *; intuition.
      rewrite refine_List_Query_In by apply H3.
      subst_strings.
      rewrite refine_Join_List_Query_In by apply H0.
      pose_string_ids.
      rewrite refine_List_Query_In_Where.
      rewrite refine_List_Query_In_Where.
      rewrite refine_List_For_Query_In_Return;
        simplify with monad laws; simpl.
      refine pick pair; simplify with monad laws;
      refine pick pair; simplify with monad laws.
      simpl in *.
      refine pick val _ ; try eassumption.
      simplify with monad laws.
      refine pick val _ ; try eassumption.
      simplify with monad laws.
      refine pick val _ ; try eassumption.
      simplify with monad laws.
      finish honing.
    }

    hone method "BreedPopulation".
    { simplify with monad laws.
      pose (callMeth PopCache "LookupKey" (snd r_n) n).
      assert (refine {b | forall b' : nat, b = Some b' -> cachedVal or (n, b')}
                     (o <- callMeth PopCache "LookupKey" (snd r_n) n;
                      ret (snd o))).
      {
        pose (ADTRefinementPreservesMethods (projT2 LRUCache) {| bindex := "LookupKey" |}
                                            (cachedVal or) (snd r_n) n (proj2 H0)).
        simpl in r.
        subst_strings.
        rewrite <- r.
        unfold refine; intros; inversion_by computes_to_inv; subst.
        simpl in *.
        econstructor; intros; eapply H2; eauto.
      }
      subst_strings; setoid_rewrite H1; simplify with monad laws.
      etransitivity; [apply refine_under_bind | ]; intros.
      rewrite refine_If_Opt_Then_Else_Bind; apply refine_If_Opt_Then_Else.
      { unfold pointwise_relation; intros.
        simplify with monad laws.
        refine pick val _; simpl; eauto.
        simplify with monad laws; higher_order_1_reflexivity.
      }
      {
        unfold MyListImpl_abs in *; split_and.
        rewrite refine_Count; simplify with monad laws.
        rewrite refine_List_Query_In by eassumption.
        simpl; subst_body.
        setoid_rewrite refine_List_Query_In_Where.
        rewrite refine_List_For_Query_In_Return;
          simplify with monad laws.
        etransitivity.
        apply refine_bind; [reflexivity | unfold pointwise_relation; intros].
        refine pick pair; simplify with monad laws.
        refine pick pair; simplify with monad laws.
        rewrite refine_pick_val by eassumption.
        simplify with monad laws.
        rewrite refine_pick_val by eassumption.
        simplify with monad laws.
        higher_order_1_reflexivity.
        pose (callMeth PopCache "AddKey" (snd r_n)).
        assert (forall kv, refine
                             (or <- (callMeth CacheSpec "AddKey" (cachedVal or) kv);
                              {b | PopCacheAbs (fst or) b})
                             (nr <- c kv; ret (fst nr))).
        {
          intros;
          pose (ADTRefinementPreservesMethods (projT2 LRUCache) {| bindex := "AddKey" |}
                                              _ _ kv H4).
          unfold c; subst_strings. rewrite <- r.
          repeat rewrite refineEquiv_bind_bind.
          f_equiv; unfold pointwise_relation; intros.
          rewrite refineEquiv_bind_bind; simpl.
          setoid_rewrite refineEquiv_bind_unit; simpl.
          setoid_rewrite refineEquiv_unit_bind.
          reflexivity.
        }
        simpl in H.
        rewrite <- refineEquiv_bind_bind.
        rewrite H; simplify with monad laws.
        reflexivity.
      }
      finish honing.
    }

    hone method "AddDog".
    {
      unfold MyListImpl_abs in *; split_and.
      pose_string_ids.
      simplify with monad laws; simpl.
      rewrite refine_pick_val with (A := nat) (a := length (snd (fst r_n))).
      simplify with monad laws; simpl.
      pose_string_ids.
      etransitivity.
      apply refine_bind; [reflexivity | unfold pointwise_relation; intros].
      refine pick pair; simplify with monad laws.
      refine pick pair; simplify with monad laws.
      rewrite refine_pick_val by eassumption.
      simplify with monad laws.
      subst_strings.
      match goal with
          |- context
               [{a | EnsembleIndexedListEquivalence
                       ((@UpdateUnConstrRelation ?QSSchema ?c ?Ridx
                                                 (InsertQSSpecs.EnsembleInsert ?n (?c!?R)))!?R)%QueryImpl a}%comp] =>
          let H := fresh in
          generalize ((@ImplementListInsert_eq QSSchema
                                               {| bindex := R |}
                                               n c)) as H; intros; setoid_rewrite H
      end; try reflexivity; try eassumption.
      simplify with monad laws.
      higher_order_1_reflexivity.
      pose (callMeth PopCache "UpdateKey" (snd r_n)).
      assert (forall kv, refine
                           (or <- (callMeth CacheSpec "UpdateKey" (cachedVal or) kv);
                            {b | PopCacheAbs (fst or) b})
                           (nr <- c kv; ret (fst nr))).
      {
        intros;
        pose (ADTRefinementPreservesMethods (projT2 LRUCache) {| bindex := "UpdateKey" |}
                                            _ _ kv H2).
        unfold c; subst_strings. rewrite <- r.
        repeat rewrite refineEquiv_bind_bind.
        f_equiv; unfold pointwise_relation; intros.
        rewrite refineEquiv_bind_bind; simpl.
        setoid_rewrite refineEquiv_bind_unit; simpl.
        setoid_rewrite refineEquiv_unit_bind.
        reflexivity.
      }
      simpl in H1.
      rewrite <- refineEquiv_bind_bind.
      subst_strings.
      set (n!"Breed").
      specialize (H1 (d, S )).
      subst_body.
      rewrite H1.
      simplify with monad laws.
      finish honing.
      intros; destruct H3 as [H3 _].
      intros; eapply lt_irrefl.
      setoid_rewrite <- H4 in H3; eapply H3.
      eauto.
    }

    finish sharpening.

  Defined.

End CachingRefinement.

Check (My (BoundedStringCacheADT nat 29)).
