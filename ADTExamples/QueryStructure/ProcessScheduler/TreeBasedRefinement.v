Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation BuildADTRefinements
        QueryStructureSchema QueryStructure
        QueryQSSpecs InsertQSSpecs EmptyQSSpecs
        GeneralInsertRefinements GeneralQueryRefinements
        GeneralQueryStructureRefinements
        ListQueryRefinements ListInsertRefinements
        ListQueryStructureRefinements.

Require Import BagsOfTuples CachingBags Bool.
Require Import DBSchema SetEq AdditionalLemmas.
Require Export ADTRefinement.BuildADTRefinements.

Unset Implicit Arguments.

Definition StatePIDIndexedTree : @BagPlusBagProof (@Tuple ProcessSchema).
  mkIndex ProcessSchema [STATE; PID].
Defined.

Definition Storage := AddCachingLayer (BagProof StatePIDIndexedTree) 
                                      (fun p => p PID)
                                      0 max (ListMax_cacheable 0).

Definition StorageType           := BagType Storage.
Definition StorageIsBag          := BagProof Storage.
Definition StorageSearchTermType := SearchTermType Storage.

Section TreeBasedRefinement.
  Open Scope type_scope.
  Open Scope Tuple_scope.

  Notation "x '∈' y" := (In _ y x) (at level 50, no associativity).

  Tactic Notation "call" "eapply" constr(hypothesis) "after" tactic1(preprocessor) :=
    first [ preprocessor; eapply hypothesis | eapply hypothesis ].

  (* The following tactic is useful when we have a set of hypotheses
     of the form

     H0 : In DB tuple 
     H  : tupleAgree tuple <COL :: x, ...> COL
     H' : forall tuple', In DB tuple' -> (tuple'!COL <> x)

     which essentially means that we have a tuple that's in the DB and
     matches another one on the COL column, and an hypothesis H' that
     guarantees that such a match is in fact impossible. In that case,
     it's essentially enough to call exfalso, which this tactic does
   *)

  Tactic Notation "prove" "trivial" "constraints" :=
    unfold decides, not in *;
    intros;
    match goal with 
      | [ H: tupleAgree _ _ (?column :: _) |- _ ] => 
        specialize (H column); 
        exfalso; 
        match goal with
          | [ H': _ |- _] => 
            eapply H'; 
            try eassumption;
            call eapply H after symmetry;
            simpl;
            auto
        end
    end.

  Lemma NeatScheduler :
    Sharpened ProcessSchedulerSpec.
  Proof.
    unfold ProcessSchedulerSpec.

    unfold ForAll_In; start honing QueryStructure.

    Definition equivalence := fun set_db (db: StorageType) =>
      EnsembleListEquivalence (GetUnConstrRelation set_db PROCESSES) (benumerate db).

    hone representation using equivalence. (* TODO: unfolding equiv here slows everything down. Why? *)
    
    hone constructor INIT. {
      repeat setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      repeat setoid_rewrite refineEquiv_pick_eq'.
      simplify with monad laws.

      rewrite (refine_pick_val' bempty) by apply EnsembleListEquivalence_Empty.
      subst_body; higher_order_1_reflexivity. 
    }

    hone method ENUMERATE. {
      unfold equivalence in H.

      setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      setoid_rewrite refineEquiv_pick_pair.
      setoid_rewrite refineEquiv_pick_eq'. 
      simplify with monad laws.
      simpl.

      rewrite (Equivalent_UnConstr_In_EnsembleListEquivalence) by eassumption.

      setoid_rewrite Equivalent_List_In_Where.

      (* Full qualification of bfind_matcher needed to avoid apparition of spurious existentials *)
      rewrite (filter_by_equiv dec (@bfind_matcher _ _ _ StorageIsBag (Some n, (None, [])))) by prove_observational_eq.

      setoid_rewrite (@bfind_correct _ _ _ StorageIsBag r_n (Some n, (None, []))).
      setoid_rewrite refine_For_List_Return.
      simplify with monad laws.

      rewrite refine_pick_val by eassumption.
      simplify with monad laws.
      finish honing.
    }    

    (* TODO: s/Decideable/Decidable/ *)
    (* TODO: Use rewrite by instead of [ ... | eassumption ] *)
    (* TODO: Handle the 'projection' parameter differently; 
             right now it appears explicitly in plenty of 
             places, and since it is infered in KeyFilter 
             it makes it possble to swap same-type search terms,
             delaying the failure until the call to bfind_correct *)
    (* TODO: The backtick notation from bounded indexes cannot be input *)

    hone method GET_CPU_TIME. {
      unfold equivalence in H.

      setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      setoid_rewrite refineEquiv_pick_pair.
      setoid_rewrite refineEquiv_pick_eq'. 
      simplify with monad laws.
      simpl.

      rewrite (Equivalent_UnConstr_In_EnsembleListEquivalence) by eassumption.

      setoid_rewrite Equivalent_List_In_Where.

      (* Full qualification of bfind_matcher needed to avoid apparition of spurious existentials *)
      rewrite (filter_by_equiv _ (@bfind_matcher _ _ _ StorageIsBag (None, (Some n, [])))) by prove_observational_eq.

      setoid_rewrite (@bfind_correct _ _ _ StorageIsBag r_n (None, (Some n, []))).
      setoid_rewrite refine_For_List_Return.
      simplify with monad laws.

      rewrite refine_pick_val by eassumption.
      simplify with monad laws.
      finish honing.
    }    

    hone method SPAWN. {
      unfold equivalence in H.
      
      setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      setoid_rewrite refineEquiv_pick_pair.
      setoid_rewrite refineEquiv_pick_eq'. 
      simplify with monad laws.
      simpl.
 
      assert (forall tup : Process, tup ∈ GetUnConstrRelation c PROCESSES -> S (ccached_value r_n) <> tup!PID_COLUMN)
        by (rewrite <- EnsembleListEquivalence_lift_property by eassumption;
            apply (assert_cache_property (cfresh_cache r_n) (max_cached_neq_projected _ _))).

      rewrite refine_pick_val by eassumption.
      simplify with monad laws.

      rewrite (refine_pick_val' true) by prove trivial constraints.
      simplify with monad laws.

      rewrite (refine_pick_val' true) by prove trivial constraints.
      simplify with monad laws.

      unfold equivalence.

      rewrite refine_pick_val by (apply binsert_correct_DB; eassumption).

      simplify with monad laws.

      finish honing.
    }

    finish sharpening.
  Defined.
End TreeBasedRefinement.
