Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation BuildADTRefinements
        QueryStructureSchema QueryStructure
        QueryQSSpecs InsertQSSpecs EmptyQSSpecs
        GeneralInsertRefinements GeneralQueryRefinements
        GeneralQueryStructureRefinements
        ListQueryRefinements ListInsertRefinements
        ListQueryStructureRefinements.

Require Import BagsOfTuples CachingBags Bool.
Require Import DBSchema AdditionalLemmas.
Require Export ADTRefinement.BuildADTRefinements.

Unset Implicit Arguments.

Definition StatePIDIndexedTree : @BagPlusBagProof Process.
  mkIndex ProcessSchema [STATE; PID].
Defined.

Definition Storage := AddCachingLayer (BagProof StatePIDIndexedTree)
                                      (fun p => p PID)
                                      0 eq _ max ListMax_cacheable.

Definition StorageType           := BagType Storage.
Definition StorageIsBag          := BagProof Storage.
Definition StorageSearchTermType := SearchTermType Storage.

Section TreeBasedRefinement.
  Open Scope type_scope.
  Open Scope Tuple_scope.

  Notation "x '∈' y" := (In _ y x) (at level 50, no associativity).

  Tactic Notation "lift" "list" "property" constr(prop) "as" ident(name) :=
    pose proof prop as name;
    setoid_rewrite EnsembleIndexedListEquivalence_lift_property in name;
    [ | eassumption].

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

  Opaque Query_For.

  Definition equivalence (set_db: UnConstrQueryStructure ProcessSchedulerSchema) (db: StorageType) :=
    EnsembleIndexedListEquivalence (GetUnConstrRelation set_db PROCESSES) (benumerate db).

  Lemma NeatScheduler :
    Sharpened ProcessSchedulerSpec.
  Proof.
    unfold ProcessSchedulerSpec.

    unfold ForAll_In; start honing QueryStructure.

    hone representation using equivalence.

    hone constructor INIT. {
      unfold equivalence.

      repeat setoid_rewrite refineEquiv_pick_ex_computes_to_and;
      repeat setoid_rewrite refineEquiv_pick_eq';
      simplify with monad laws.

      rewrite (refine_pick_val' bempty) by intuition (apply EnsembleIndexedListEquivalence_Empty).
      subst_body; higher_order_1_reflexivity.
    }

    hone method ENUMERATE. {
      unfold equivalence in H.

      setoid_rewrite refineEquiv_pick_ex_computes_to_and;
      setoid_rewrite refineEquiv_pick_pair;
      setoid_rewrite refineEquiv_pick_eq';
      simplify with monad laws; cbv beta;
      simpl.

      rewrite refine_List_Query_In by eassumption.
      rewrite refine_List_Query_In_Where.
      rewrite refine_List_For_Query_In_Return_Permutation.

      rewrite (filter_by_equiv _ (bfind_matcher (Bag := StorageIsBag) (Some n, (None, []))))
        by prove_observational_eq.
      setoid_rewrite (bfind_correct _).
      setoid_rewrite refine_Permutation_Reflexivity.
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

      setoid_rewrite refineEquiv_pick_ex_computes_to_and;
      setoid_rewrite refineEquiv_pick_pair;
      setoid_rewrite refineEquiv_pick_eq';
      simplify with monad laws; cbv beta;
      simpl.

      rewrite refine_List_Query_In; eauto.
      rewrite refine_List_Query_In_Where.
      rewrite refine_List_For_Query_In_Return_Permutation.

      rewrite (filter_by_equiv _ (bfind_matcher (Bag := StorageIsBag) (None, (Some n, []))))
        by prove_observational_eq.

      setoid_rewrite (bfind_correct _).
      setoid_rewrite refine_Permutation_Reflexivity.
      simplify with monad laws.

      rewrite refine_pick_val by eassumption.
      simplify with monad laws.
      finish honing.
    }

    hone method SPAWN. {
      unfold equivalence in H.

      lift list property (assert_cache_property (cfresh_cache r_n) max_cached_neq_projected _) as cache.
    
      setoid_rewrite refineEquiv_pick_ex_computes_to_and;
      setoid_rewrite refineEquiv_pick_pair;
      setoid_rewrite refineEquiv_pick_eq';
      simplify with monad laws; cbv beta;
      simpl.

      rewrite refine_pick_val by eassumption.
      simplify with monad laws.
 
      rewrite refine_pick_val by eauto using EnsembleIndexedListEquivalence_pick_new_index.
      simplify with monad laws.

      rewrite refine_tupleAgree_refl_True.
      simplify with monad laws.

      rewrite (refine_pick_val' true) by prove trivial constraints.
      simplify with monad laws.

      rewrite (refine_pick_val' true) by prove trivial constraints.
      simplify with monad laws.

      rewrite refine_pick_val by (apply binsert_correct_DB; eauto).
      simplify with monad laws.

      finish honing.
    }

    finish sharpening.
  Defined.
End TreeBasedRefinement.
