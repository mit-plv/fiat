Require Export QueryStructureNotations QueryQSSpecs ListImplementation.
Require Import List Compare_dec AdditionalLemmas AdditionalPermutationLemmas AdditionalMorphisms EnsembleListEquivalenceProperties flattenCompListProperties.

Unset Implicit Arguments.

Definition gtb x y :=
  andb (leb y x) (negb (beq_nat x y)). 

Transparent Count Query_For.

Lemma For_computes_to_In :
  forall {heading} P,
    (forall a, P a \/ ~ P a) ->
    forall seq ens,
      computes_to (For (QueryResultComp (heading := heading) ens 
                                        (fun tup => Where (P tup) Return tup))) seq ->
      forall x, 
        List.In x seq -> (P x /\ (exists x0, ens x0 /\ indexedTuple x0 = x)).
Proof.
  unfold refine, decides, Count, Query_In, UnConstrQuery_In,  Query_Where, Query_Return; 
  unfold Query_For, QueryResultComp; intros * excl;
  induction seq as [ | head seq' IH ]; intros.
  
  exfalso; intuition.
  
  inversion_by computes_to_inv.
  
  pose proof (permutation_cons_in H4) as in_x0.
  apply in_split in in_x0.
  destruct in_x0 as [ x0_before [ x0_after ? ] ]; subst. 
  symmetry in H4. apply Permutation_cons_app_inv in H4.

  rewrite map_map in H5.
  destruct (flatten_CompList_app_cons_inv _ excl _ _ _ _ H5) as [ x1_before [ x1_middle [ head' [ x1_after (_eq & in_orig & before & middle & after) ] ] ] ]; subst.
  
  unfold boxed_option in middle; simpl in middle. 
  apply computes_to_inv in middle.
  destruct middle as [head'' (middle1 & middle2)].
  apply computes_to_inv in middle1.
  apply computes_to_inv in middle2.
  destruct middle1 as ( spec1 & spec2 ).
  destruct middle2 as [ nil' (ret_nil & ret_cons) ].
  apply computes_to_inv in ret_nil; subst.
  rewrite app_nil_r in *; subst.
  apply computes_to_inv in ret_cons; subst.

  rewrite singleton_neq_nil in spec2.
  destruct (excl head') as [ H | H ]; try solve [exfalso; intuition].
  specialize (spec1 H).

  apply computes_to_inv in spec1.
  injection spec1; intros; subst.

  destruct H0.

  - subst x; split; [ | exists head'; split; [ apply H3  | ] ]; auto.
  - pose proof (EnsembleListEquivalence_slice _ _ _ H3) as smaller_equiv.
    pose proof (flatten_CompList_app _ _ _ _ before after) as flatten_app. 
    set (smaller_ens := (fun x : IndexedTuple => ens x /\ ~ In x x1_middle)).
    split.

    + eapply H1; try assumption.
      econstructor; [ | constructor; symmetry; eassumption ]. 
      econstructor.
      constructor. 

      apply smaller_equiv.

      unfold boxed_option in *.
      rewrite !map_app, !map_map.
      apply flatten_app. 
    + assert (exists x0 : IndexedTuple, smaller_ens x0 /\ indexedTuple x0 = x) as temp.
      apply H2; try eassumption.
      econstructor; [ | constructor; symmetry; eassumption ]. 
      econstructor.
      constructor. 

      eassumption.
      unfold boxed_option in *.
      rewrite !map_app, !map_map.
      apply flatten_app. 
      
      destruct temp as [ x0 ( ens_x & _eq ) ]; subst.
      eexists; split; eauto.

      unfold smaller_ens in ens_x; intuition.
Qed.


Lemma For_computes_to_nil :
  forall {heading} P,
  forall ens,
    computes_to (For (QueryResultComp (heading := heading) ens 
                                      (fun tup => Where (P tup) Return tup))) [] ->
    forall x,
      ens x -> ~ (P (indexedTuple x)).
Proof.
  unfold refine, decides, Count, Query_In, UnConstrQuery_In,  Query_Where, Query_Return; 
  unfold Query_For, QueryResultComp; intros **.

                                            inversion_by computes_to_inv.
  symmetry in H2; apply Permutation_nil in H2; subst.
  apply H1 in H0.
  apply in_split in H0.
  destruct H0 as [ x1_before [ x1_after _eq ] ]; subst.
  
  rewrite map_map in H3.
  eapply flatten_CompList_nil; unfold boxed_option; eauto; intuition.
Qed.

Lemma decidable_excl :
  forall {A : Type} (P : Ensemble A) (P_dec : DecideableEnsemble P),
    (forall (a: A), P a \/ ~ P a).
Proof.
  intros ** a.
  destruct (dec a) eqn:eqdec;
    [ rewrite dec_decides_P in eqdec | rewrite Decides_false in eqdec ]; intuition.
Qed.

Lemma refine_foreign_key_constraint_via_select :
  forall {schm tbl} P (P_dec : DecideableEnsemble P),
  forall (c : UnConstrQueryStructure schm),
    refine
      (Pick (fun (b : bool) =>
               decides b
                       (exists tup2: @IndexedTuple _,
                          (GetUnConstrRelation c tbl tup2 /\ P (indexedTuple tup2)))))
      (Bind 
         (Count (For (UnConstrQuery_In c tbl (fun tup => Where (P tup) Return tup))))
         (fun count => ret (gtb count 0))).
Proof.
  unfold refine, Count, UnConstrQuery_In; intros * excl * pick_comp ** .
  inversion_by computes_to_inv; subst.

  constructor.

  destruct (Datatypes.length x0) eqn:eq_length;
    destruct x0 as [ | head tail ]; simpl in *; try discriminate; unfold gtb; simpl.

  pose proof (For_computes_to_nil _ (GetUnConstrRelation c tbl) H0). 
  rewrite not_exists_forall; intro a; rewrite not_and_implication; intros.
  apply H; trivial.

  apply For_computes_to_In with (x := head) in H0; try solve [intuition].
  destruct H0 as ( p & [ x0 ( in_ens & _eq ) ] ); subst.
  eexists; split; eauto.

  apply decidable_excl; assumption.
Qed.
