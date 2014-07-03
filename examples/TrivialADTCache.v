Require Import QueryStructureNotations.
Require Import ListImplementation.
Require Import AddCache ADTCache CacheADT.

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

Section CachingRefinement.

  Require Import ComputationalADT.

  Definition CacheSpec := @CacheSpec string nat.
  Variable LRUCache : FullySharpened CacheSpec.
  Definition PopCache := projT1 LRUCache.
  Definition PopCacheAbs : Rep CacheSpec -> Rep PopCache -> Prop :=
    AbsR (fst (projT2 LRUCache)).
  Definition PopCacheComp := snd (projT2 LRUCache).

  Definition CallMethod'
             (Sig : ADTSig)
             (A : ADT Sig)
             (CompA : is_computationalADT A)
             (idx : MethodIndex Sig)
             (r : Rep A)
             (i : fst (MethodDomCod Sig idx))
             : Rep A * snd (MethodDomCod Sig idx) :=
    is_computational_val (proj2 CompA idx r i).

  Notation CallMethod CompADT idx r i :=
    (CallMethod' CompADT {|bindex := idx |} r i).

  Definition CallConstructor'
             (Sig : ADTSig)
             (A : ADT Sig)
             (CompA : is_computationalADT A)
             (idx : ConstructorIndex Sig)
             (i : ConstructorDom Sig idx)
             : Rep A :=
    is_computational_val (proj1 CompA idx i).

  Notation CallConstructor CompADT idx i :=
    (CallConstructor' CompADT {|bindex := idx |} i).

  Definition EmptyCache := CallConstructor PopCacheComp "EmptyCache" ().
  Definition InsertKey r i := CallMethod PopCacheComp "AddKey" r i.
  Definition LookupKey r i := CallMethod PopCacheComp "LookupKey" r i.
  Definition UpdateKey r i := CallMethod PopCacheComp "UpdateKey" r i.

  Definition BreedCacheSpec
             (or : UnConstrQueryStructure MySchema)
             (cache : Rep CacheSpec) :=
    forall breed r pop,
      r (breed,  pop)
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

  Lemma refine_Pick_Some {A B}
  : forall (P : Ensemble B) (c e : Comp A) (t : B -> Comp A),
      (forall b, P b -> refine c (t b))
      -> ((forall b, ~ P b) -> refine c e)
      -> refine c
                (b <- {b | forall b',
                             (b = Some b' -> P b')
                             /\ (b = None -> forall b', ~ P b')};
                 match b with
                   | Some b => t b
                   | None => e
                 end).
  Proof.
    unfold refine; intros; apply computes_to_inv in H1; destruct_ex; intuition.
    destruct x; inversion_by computes_to_inv; eauto.
  Qed.

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
      apply refine_Pick_Some with (P := fun v => cachedVal r_n (n, v)); intros.
      { refine pick val _.
        simplify with monad laws; cbv beta; simpl.
        destruct H0; subst.
        unfold BreedCacheSpec in *.
        apply H2 in H1.
        subst_strings.
        rewrite H1.
        simplify with monad laws.
        finish honing.
      }
      {
        unfold cachedRep_AbsR in *|-; simpl; split_and; subst.
        rewrite refine_under_bind'; [reflexivity | ].
        intros; rewrite refine_pick_cachedRep.
        simplify with monad laws.
        intros; pose (callMeth CacheSpec "AddKey" (cachedVal r_n) (n, x)); simpl in c.
        
        rewrite refine_pick_val with 
                (A := (Ensemble (string * nat)))
                (a := callMeth CacheSpec "AddKey" (cachedVal r_n) (n, x)).

                         cachedVal := c |}).

        intros; rewrite refineEquiv_pick_pair.
        intros; pose (callMeth CacheSpec "AddKey" (cachedVal r_n) (n, x)).
        re

        simpl in c.
        intros; rewrite refine_pick_val with 
                (A := cachedRep (UnConstrQueryStructure MySchema) (Ensemble (string * nat)))
                (a := {| origRep := origRep r_n; 
                         cachedVal := c |}).
        simplify with monad laws.

        finish honing.
        cbv beta. simpl.
        refine pick val ({| origRep := rep r_n; cachedVal := callMeth CacheSpec "insert" r_n (n, b) |}).
        rewrite refine_pick_val 
        unfold cachedRep_AbsR in H0; intuition; subst.
    eapply refine_if with (b := if (string_dec n "Dachshund")
                                then true
                                else false).
    { find_if_inside; try congruence; subst.
      intros; unfold BreedCacheSpec in H2.
      subst_body.
      setoid_rewrite H2; simplify with monad laws; simpl.
      reflexivity. }
    { find_if_inside; try congruence; subst.
      simpl; reflexivity.
    }
  }

  hone constructor "Empty".
  { simplify with monad laws.
    rewrite refine_pick_cachedRep.
    rewrite refine_pick_val with (A := nat)
                                   (a := 0).
    simplify with monad laws; finish honing.
    unfold BreedCacheSpec; simpl.
    unfold pointwise_relation; intros; setoid_rewrite refine_Count.
    setoid_rewrite refine_For_In_Empty.
    simplify with monad laws; reflexivity.
  }

  hone method "AddDog".
  {
    simplify with monad laws; cbv beta; simpl.
    etransitivity.
    eapply refine_bind_pick; intros.
    rewrite refine_pick_cachedRep.
    simplify with monad laws.
    unfold BreedCacheSpec; simpl.
    pose_string_ids.

    rewrite refine_pick_val.
    simplify with monad laws; higher_order_1_reflexivity.
    unfold pointwise_relation; intros.
    intros; etransitivity.
    apply refine_refine_Count.
    apply refine_For_In_Insert.
    unfold In, not; intros; eapply H1;
    [ eapply H2
     | subst_body; auto ].
    rewrite refine_Count_bind_bind_app.
    unfold cachedRep_AbsR, BreedCacheSpec in H0; split_and; subst.
    pose_string_ids.
    setoid_rewrite H3.
    simplify with monad laws.
    subst_body.
    etransitivity.
    pose (n!"Breed"); simpl in *.
    eapply refine_if with (b := if (string_dec d "Dachshund")
                                then true
                                else false);
    find_if_inside; try congruence; intros.
    subst_body.
    rewrite refine_Count; simplify with monad laws.
    unfold Query_Where, Query_Return.
    rewrite refine_pick_val.
    simplify with monad laws; reflexivity.
    intuition.
    rewrite refine_Count; simplify with monad laws.
    unfold Query_Where, Query_Return.
    rewrite refine_pick_val.
    simplify with monad laws; reflexivity.
    intuition.
    eapply refineEquiv_if_ret.
    simpl.
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
    rewrite refineEquiv_pick_eq';
      simplify with monad laws.
    finish honing.
  }

  hone method "YoungOwners'Breeds".
  {
    simplify with monad laws; simpl.
    unfold MyListImpl_abs in *; intuition.
    rewrite refine_List_Query_In by apply H3.
    rewrite refine_Join_List_Query_In by apply H0.
    rewrite refine_List_Query_In_Where.
    rewrite refine_List_Query_In_Where.
    rewrite refine_List_For_Query_In_Return;
      simplify with monad laws; simpl.

    setoid_rewrite refineEquiv_pick_pair_pair.
    setoid_rewrite refineEquiv_pick_eq'.
    simplify with monad laws.
    simpl in *.
    rewrite refine_pick_val by eassumption.
    simplify with monad laws.
    rewrite refine_pick_val by eassumption.
    simplify with monad laws.
    rewrite H2.
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
