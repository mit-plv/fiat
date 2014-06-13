Require Import QueryStructureNotations.
Require Import ListImplementation.

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

Definition People := GetRelationKey MySchema "Person".
Definition Dogs := GetRelationKey MySchema "Dog".

Definition Age := GetAttributeKey People "Age".
Definition Name := GetAttributeKey People "Name".

Definition Owner := GetAttributeKey Dogs "Owner".
Definition Breed := GetAttributeKey Dogs "Breed".

Definition My :
  Sharpened MySpec.
Proof.
  unfold MySpec.

  start honing QueryStructure.

  (* Need to fix TypeClass lookup for this to go through. *)
  (* hone method "YoungOwners'Breeds".


  etransitivity.
  setoid_rewrite refine_For_Equivalent_Trace_Ensembles;
    [ reflexivity
    | eapply (Equivalent_Swap_In r_n (GetRelationKey MySchema "Dog")
                                 (GetRelationKey MySchema "Person")
                                 (fun (d : Dog) (o : Person) =>
                                    Where (o!"Age" > n)
                                          Where (d!"Owner" = o!"Name")
                                          Return d!"Breed"))].
  etransitivity.
  setoid_rewrite refine_For_Equivalent_Trace_Ensembles.
  reflexivity.
  eapply Equivalent_Under_In; simpl.
  intros; generalize (Equivalent_Swap_In_Where r_n {|bindex := "Dog" |}
          (fun (tup : Person) (tup' : Dog) =>
             Where (tup!"Owner" = tup!"Name")
                   Return tup'!"Breed")).
                      ).
  rewrite refine_Query_For_In_Equivalent;
    [ | apply Equivalent_Swap_In_Where with (qs := _)]; cbv beta.
  finish honing. *)

  hone representation using MyListImpl_abs.
  implement_empty_list "Empty" MyListImpl_abs.

  hone method "YoungOwners'Breeds".
  {
    unfold MyListImpl_abs in H; split_and.
    setoid_rewrite refineEquiv_pick_ex_computes_to_and.
    simplify with monad laws.
    simpl.
    etransitivity.
    { setoid_rewrite refine_For_Equivalent_Trace_Ensembles;
      [ reflexivity | ].
      eapply (@Equivalent_UnConstr_In_EnsembleListEquivalence 
                _ _ _ c _
                (snd r_n)
                (fun b : Tuple =>
                   UnConstrQuery_In c People
                                    (fun o : Person =>
                                       Where (o Age > n)
                                             Where (b Owner = o Name)
                                             Return (b Breed) ))).
      eauto.
    }
    simpl; etransitivity.
    { apply refine_bind.
      eapply refine_For_Equivalent_Trace_Ensembles.
      eapply (@Equivalent_Join_Lists string unit _ _ c People (snd r_n)
                                 _ (fun el (o : Person) =>
         Where (o Age > n)
               Where (el Owner = o Name)
               Return (el Breed)) H1).
      unfold pointwise_relation; intros.
      higher_order_1_reflexivity.
    } simpl; etransitivity.
    { apply refine_bind.
      eapply refine_For_Equivalent_Trace_Ensembles.
      eapply Equivalent_List_In_Where with (P_dec := _).
  simpl; intros.
  eapply X.
  setoid_rewrite Equivalent_Join_Lists; [ | eassumption ].
  simpl in X.
  eapply X.
  setoid_rewrite Equivalent_UnConstr_In_EnsembleListEquivalence.
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
