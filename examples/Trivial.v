Require Import QueryStructureNotations.
Require Import ListImplementation.
Require Import AddCache.

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
           (or : UnConstrQueryStructure MySchema)
           (nr : list Person * list Dog) : Prop :=
  or!"Person" ≃ fst nr /\ or!"Dog" ≃ snd nr.

Definition My :
  Sharpened MySpec.
Proof.
  unfold MySpec.

  start honing QueryStructure.

  add cache with spec BreedCacheSpec.

  hone method "YoungOwners'Breeds".
  { simplify with monad laws; cbv beta; simpl.



  hone representation using MyListImpl_abs.
  implement_empty_list "Empty" MyListImpl_abs.

  hone method "YoungOwners'Breeds".
  {
    simpl.
    unfold MyListImpl_abs in H; split_and.
    setoid_rewrite refineEquiv_pick_ex_computes_to_and.
    simplify with monad laws.
    rewrite refine_List_Query_In; eauto.
    rewrite refine_Join_List_Query_In; eauto.
    rewrite refine_List_Query_In_Where.
    rewrite refine_List_Query_In_Where.
    rewrite refine_List_For_Query_In_Return;
      simplify with monad laws; simpl.

    setoid_rewrite refineEquiv_pick_pair_pair.
    setoid_rewrite refineEquiv_pick_eq'.
    simplify with monad laws.
    rewrite refine_pick_val by eassumption.
    simplify with monad laws.
    rewrite refine_pick_val by eassumption.
    simplify with monad laws.
    finish honing.
  }

  finish sharpening.
Defined.
