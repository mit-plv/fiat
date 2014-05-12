Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation QueryStructureSchema
        QueryQSSpecs QueryStructure.

Definition Equivalent_Ensembles {A : Type}
           (P Q : Ensemble A) := forall a, P a <-> Q a.

  Lemma Equivalent_Swap_In {A}
        (qs : QueryStructureHint) (R R' : _)
        (bod : Tuple -> Tuple -> Ensemble A)
  :
    Equivalent_Ensembles
      (@Query_In qs _ R (fun tup => @Query_In qs _ R' (bod tup)))
      (@Query_In qs _ R' (fun tup => @Query_In qs _ R
                                               (fun tup' => bod tup' tup))).
  Proof.
    unfold Equivalent_Ensembles, Query_In; split; intros;
    repeat (progress (destruct_ex; intuition)); eexists;
    split; eauto.
  Qed.

  Lemma Equivalent_Swap_In_Where {A}
        (qs : QueryStructureHint) (R : _)
        {heading}
        (bod : @Tuple heading -> Tuple -> Ensemble A)
        (P : @Tuple heading -> Prop)
  :
    pointwise_relation
      Tuple Equivalent_Ensembles
      (fun tup' : Tuple =>
         (@Query_In qs _ R
                    (fun tup => Query_Where (P tup') (bod tup' tup))))
      (fun tup' : Tuple =>
         Query_Where (P tup') (@Query_In qs _ R (bod tup'))).
  Proof.
    unfold Equivalent_Ensembles, Query_In, Query_Where; split; intros;
    repeat (progress (destruct_ex; intuition)); eexists;
    split; eauto.
  Qed.

  Add Parametric Morphism {A: Type} :
    (Query_For)
      with signature (@Equivalent_Ensembles A ==> refine)
        as refine_Query_For_Equivalent.
  Proof.
    unfold impl, Query_For, refine; intros.
    inversion_by computes_to_inv.
    econstructor; split_iff; split; intros; eauto.
    apply H; apply H1; auto.
    apply H2; apply H; auto.
  Qed.

  Add Parametric Morphism {A: Type}
      (qs : QueryStructureHint) (R : _)
  :
    (fun bod => Query_For (@Query_In qs _ R bod))
      with signature ((pointwise_relation Tuple (@Equivalent_Ensembles A) ==> refine ))
        as refine_Query_For_In_Equivalent.
  Proof.
    unfold impl, Query_For, pointwise_relation, Query_In, In, refine.
    intros; inversion_by computes_to_inv.
    econstructor; split_iff; split; intros; eauto.
    destruct (H1 _ H0); eexists; intuition; eauto.
    apply H; auto.
    destruct_ex; apply H2; eexists; intuition; eauto.
    apply H; auto.
  Qed.
