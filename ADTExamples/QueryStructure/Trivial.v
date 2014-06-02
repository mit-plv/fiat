Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation BuildADTRefinements
        QueryStructureSchema QueryStructure
        QueryQSSpecs InsertQSSpecs EmptyQSSpecs
        GeneralInsertRefinements GeneralQueryRefinements
        GeneralQueryStructureRefinements
        ListQueryRefinements ListInsertRefinements
        ListQueryStructureRefinements
        ProcessScheduler.AdditionalLemmas
        QueryStructureNotations.

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
      For (d in "Dog") (o in "Person")
      Where (o!"Age" > ageLimit)
      Where (d!"Owner" = o!"Name")
      Return d!"Breed"
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

  hone method "YoungOwners'Breeds".
  rewrite Equivalent_Swap_In.
  rewrite refine_Query_For_In_Equivalent;
    [ | apply Equivalent_Swap_In_Where with (qs := _)]; cbv beta.
  finish honing.

  hone representation using MyListImpl_abs.
  implement_empty_list "Empty" MyListImpl_abs.

  hone method "YoungOwners'Breeds".
  unfold MyListImpl_abs in H; split_and.
  setoid_rewrite refineEquiv_pick_ex_computes_to_and.
  simplify with monad laws.
  simpl.
  setoid_rewrite Equivalent_UnConstr_In_EnsembleListEquivalence;
    [ | eassumption ].
  setoid_rewrite Equivalent_List_In_Where with (P_dec := _).
  setoid_rewrite Equivalent_Join_Lists; [ | eassumption ].
  setoid_rewrite Equivalent_List_In_Where with (P_dec := _).
  setoid_rewrite refine_For_List_Return.
  simplify with monad laws.
  unfold MyListImpl_abs.
  setoid_rewrite refineEquiv_pick_pair_pair.
  setoid_rewrite refineEquiv_pick_eq'.
  simplify with monad laws.
  rewrite refine_pick_val by eassumption.
  simplify with monad laws.
  rewrite refine_pick_val by eassumption.
  simplify with monad laws.
  finish honing.

  finish sharpening.
Defined.
