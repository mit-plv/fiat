Ltac typeof' H := type of H.

Require Import QueryStructureNotations.
Require Import ListImplementation.
Require Import AddCache ADTCache.

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
      "YoungOwners'Breeds" : rep × nat → rep × list string,
      "BreedPopulation" : rep × string → rep × nat
  }.

Definition MySpec : ADT MySig :=
  QueryADTRep MySchema {
    const "Empty" (_ : unit) : rep := empty,

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

Definition BreedCacheSpec (or : UnConstrQueryStructure MySchema)
           (cache : string -> nat) :=
forall breed,
  refine
    (Count (For (UnConstrQuery_In or ``("Dog")
                                  (fun d =>
                                     Where (d!"Breed" = breed)
             Return ()))))
    (ret (cache breed)).

Definition MyListImpl_abs
           (or : cachedRep (UnConstrQueryStructure MySchema) (string -> nat))
           (nr : (list Person * list Dog) * (string -> nat)) : Prop :=
  ((origRep or) ! "Person" ≃ fst (fst nr) /\
  (origRep or) ! "Dog" ≃ snd (fst nr)) /\
  cachedVal or = snd nr.

Definition My :
  Sharpened MySpec.
Proof.
  unfold MySpec.

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
    setoid_rewrite (refine_pick_val _ H0).
    simplify with monad laws; simpl.
    unfold cachedRep_AbsR in H0; intuition; subst.
    unfold BreedCacheSpec in H2.
    subst_body.
    setoid_rewrite (H2 n); simplify with monad laws; simpl.
    finish honing.
  }

  hone constructor "Empty".
  { simplify with monad laws.
    rewrite refine_pick_cachedRep.
    rewrite refine_pick_val with (A := string -> nat)
                                   (a := fun x : string => 0).
    simplify with monad laws; finish honing.
    unfold BreedCacheSpec; simpl.
    intros; setoid_rewrite refine_Count.
    setoid_rewrite refine_For_In_Empty.
    simplify with monad laws; reflexivity.
  }

  hone representation using MyListImpl_abs.
  hone constructor "Empty".
  { simplify with monad laws.
    unfold MyListImpl_abs, GetUnConstrRelation; simpl.
    rewrite (@refineEquiv_pick_pair_pair
                  (list Person)
                  (list Dog)
                  (string -> nat)
                  (EnsembleIndexedListEquivalence (fun _ : IndexedTuple => False))
                  (EnsembleIndexedListEquivalence (fun _ : IndexedTuple => False))
                  (fun c : string -> nat => (fun _ => 0) = c)).
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
    rewrite refine_pick_val by apply H0.
    simplify with monad laws.
    rewrite refine_pick_val by apply H3.
    simplify with monad laws.
    rewrite H2.
    finish honing.
  }

  hone method "BreedPopulation".
  {
    simplify with monad laws; simpl.
    
    unfold MyListImpl_abs in *; intuition.
    setoid_rewrite refineEquiv_pick_pair_pair.
    setoid_rewrite refineEquiv_pick_eq'.
    simplify with monad laws.
    rewrite refine_pick_val by apply H0.
    simplify with monad laws.
    rewrite refine_pick_val by apply H3.
    simplify with monad laws.
    rewrite H2.
    finish honing.
  }

  finish sharpening.
Defined.
