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
      "YoungOwners'Breeds" : rep × nat → rep × list string
  }.

Definition MySpec : ADT MySig :=
  QueryADTRep MySchema {
    const "Empty" (_ : unit) : rep := empty,

    query "YoungOwners'Breeds" ( ageLimit : nat ) : list string :=
      For (d in "Dog")
          (o in "Person")
          Where (ageLimit > o!"Age")
          Where (d!"Name" = o!"Name")
          Return (d!"Breed")
}.

Definition MyListImpl_abs
           (or : UnConstrQueryStructure MySchema)
           (nr : list Person * list Dog) : Prop :=
  or!"Person" ≃ fst nr /\ or!"Dog" ≃ snd nr.

Definition My :
  Sharpened MySpec.
Proof.
  unfold MySpec.

  start honing QueryStructure.

  hone representation using MyListImpl_abs.

  hone constructor "Empty".
  { simplify with monad laws.
    unfold MyListImpl_abs.
    rewrite refineEquiv_pick_pair.
    rewrite refine_pick_val by
        apply EnsembleIndexedListEquivalence_Empty.
    simplify with monad laws.
    rewrite refine_pick_val by
        apply EnsembleIndexedListEquivalence_Empty.
    simplify with monad laws.
    finish honing.
  }

  hone method "YoungOwners'Breeds".
  {
    simplify with monad laws; simpl.
    subst_strings.
    unfold MyListImpl_abs in *; simpl in *; intuition.
    rewrite refine_List_Query_In by eassumption.
    rewrite refine_Join_List_Query_In by eassumption.
    rewrite refine_List_Query_In_Where.
    rewrite refine_List_Query_In_Where.
    rewrite refine_List_For_Query_In_Return;
      simplify with monad laws; simpl.

    setoid_rewrite refineEquiv_pick_pair.
    pose_string_ids.
    simplify with monad laws.
    rewrite refine_pick_val by eassumption.
    simplify with monad laws.
    rewrite refine_pick_val by eassumption.
    simplify with monad laws.
    finish honing.
  }

  finish sharpening.
Defined.
