Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation BuildADTRefinements
        QueryStructureSchema QueryStructure
        QueryQSSpecs InsertQSSpecs EmptyQSSpecs
        GeneralInsertRefinements GeneralQueryRefinements
        GeneralQueryStructureRefinements
        ListQueryRefinements ListInsertRefinements
        ListQueryStructureRefinements
        ProcessScheduler.AdditionalLemmas
        DBSchema SetEq.

Require Import Bags.
Require Import FMapAVL OrderedTypeEx.
Require Import FMapExtensions.
Require Import DBSchema SetEq AdditionalLemmas.
Require Export ADTRefinement.BuildADTRefinements.

Unset Implicit Arguments.

Module GenericTreeDB := FMapAVL.Make(Nat_as_OT). (* TODO: Add the generic implementation *)
(*Module Import DBExtraFacts := FMapExtensions GenericTreeDB.*)

Definition PIDIndex : BagPlusBagProof ProcessSchema.
Proof.
  mkIndex ProcessSchema [STATE; PID].
Defined.

Definition PIDIndexedTree := BagType _ PIDIndex.

Section TreeBasedRefinement.
  Open Scope type_scope.
  Open Scope Tuple_scope.

  Definition NeatDB :=
    (nat * PIDIndexedTree).

  Definition NeatDB_equivalence old_rep (neat_db: NeatDB) :=
    (*TODO: Would be cleaner: let (next_pid, database) := neat_db in*)
    let set_db := GetUnConstrRelation old_rep PROCESSES in
    (forall tuple, In _ set_db tuple -> gt (fst neat_db) (tuple PID)) /\
    (EnsembleListEquivalence set_db (benumerate (snd neat_db))).

  Definition ObservationalEq {A B} f g :=
    forall (a: A), @eq B (f a) (g a).

  Lemma filter_by_equiv :
    forall {A} f g,
      ObservationalEq f g ->
      forall seq, @List.filter A f seq = @List.filter A g seq.
  Proof.
    intros A f g obs seq; unfold ObservationalEq in obs; induction seq; simpl; try rewrite obs; try rewrite IHseq; trivial.
  Qed.

  Lemma filter_on_key :
    forall (tree: PIDIndexedTree) (key: nat),
      SetEq
        (List.filter
           (fun (p: Process) => beq_nat (p PID) key)
           (benumerate tree))
        (bfind tree (None, (Some key, bstar))).
  Proof.
    intros tree key.

    rewrite (filter_by_equiv _ (@bfind_matcher _ _ _ (BagProof _ PIDIndex) (None, (Some key, bstar)))).
    apply (bfind_correct).

    unfold ObservationalEq.
    simpl.
    intros.
    rewrite (NatTreeExts.KeyFilter_beq beq_nat) by apply NPeano.Nat.eqb_spec.
    rewrite andb_true_r; unfold cast; trivial.
  Qed.

  Notation "x '∈' y" := (In _ y x) (at level 50, no associativity).

  Lemma no_collisions_when_using_a_fresh_pid :
    forall pid c (tup tup': Process),
      tupleAgree tup tup' [PID_COLUMN]%SchemaConstraints ->
      (forall a, (GetUnConstrRelation c PROCESSES) a -> pid > (a PID)) ->
      tup PID = pid ->
      GetUnConstrRelation c PROCESSES tup' ->
      False.
  Proof.
    unfold tupleAgree, GetAttribute;
    simpl;
    intuition;
    specialize (H0 tup' H2);
    specialize (H PID);
      subst;
      intuition.
  Qed.

  Lemma insert_always_happens :
    forall pid c,
      (forall a, (GetUnConstrRelation c PROCESSES) a -> pid > (a PID)) ->
      refine
        {b |
         decides b
                 (forall tup' : Tuple,
                    GetUnConstrRelation c PROCESSES tup' ->
                    tupleAgree
                      (<PID_COLUMN :: pid, STATE_COLUMN :: SLEEPING, CPU_COLUMN :: 0>) tup'
                      [PID_COLUMN]%SchemaConstraints ->
                    tupleAgree
                      (<PID_COLUMN :: pid, STATE_COLUMN :: SLEEPING, CPU_COLUMN :: 0>) tup'
                      [CPU_COLUMN; STATE_COLUMN]%SchemaConstraints)
                    }
        (ret true).
  Proof.
    intros; constructor; inversion_by computes_to_inv; subst; simpl.
    intros; exfalso; apply (no_collisions_when_using_a_fresh_pid pid c _ _ H1); trivial.
  Qed.

  Lemma tupleAgree_sym :
    forall (heading: Heading) tup1 tup2 attrs,
      @tupleAgree heading tup1 tup2 attrs <-> @tupleAgree heading tup2 tup1 attrs.
  Proof.
    intros; unfold tupleAgree.
    intuition; symmetry; intuition.
  Qed.

  Lemma insert_always_happens' :
    forall pid c,
      (forall a, (GetUnConstrRelation c PROCESSES) a -> pid > (a PID)) ->
      refine
        {b |
         decides b
                 (forall tup' : Tuple,
                    GetUnConstrRelation c PROCESSES tup' ->
                    tupleAgree
                      tup' (<PID_COLUMN :: pid, STATE_COLUMN :: SLEEPING, CPU_COLUMN :: 0>)
                      [PID_COLUMN]%SchemaConstraints ->
                    tupleAgree
                      tup' (<PID_COLUMN :: pid, STATE_COLUMN :: SLEEPING, CPU_COLUMN :: 0>)
                      [CPU_COLUMN; STATE_COLUMN]%SchemaConstraints)
                    }
        (ret true).
  Proof.
    intros; constructor; inversion_by computes_to_inv; subst; simpl.
    intros; exfalso; rewrite tupleAgree_sym in H1; apply (no_collisions_when_using_a_fresh_pid pid c _ _ H1); trivial.
  Qed.

  Lemma get_update_unconstr_iff :
    forall db_schema qs table new_contents,
    forall x,
      x ∈ GetUnConstrRelation (UpdateUnConstrRelation db_schema qs table new_contents) table <->
      x ∈ new_contents.
  Proof.
    unfold GetUnConstrRelation, UpdateUnConstrRelation, RelationInsert;
    intros; rewrite ith_replace_BoundIndex_eq;
    reflexivity.
  Qed.

  Lemma NeatScheduler :
    Sharpened ProcessSchedulerSpec.
  Proof.
    unfold ProcessSchedulerSpec.

    unfold ForAll_In; start honing QueryStructure.

    hone representation using NeatDB_equivalence.

    (* (* TODO: Why does adding this followed simpl break the
          Equivalent_UnConstr_In_EnsembleListEquivalence rewrite? *)
      unfold UnConstrQuery_In.
     (*simpl.*) *)

    hone constructor INIT. {
      unfold NeatDB_equivalence, DropQSConstraints_AbsR.
      repeat setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      repeat setoid_rewrite refineEquiv_pick_eq'.
      simplify with monad laws.

      setoid_rewrite (* TODO *)
        (refineEquiv_pick_pair_snd_dep
           (fun frist => forall tuple : Tuple, tuple ∈ _ -> frist > tuple PID)
           (fun pair  => EnsembleListEquivalence _ (benumerate (snd pair)))).

      rewrite refine_pick_val;
        [ simplify with monad laws | instantiate (1 := 0) ].

      rewrite refine_pick_val;
        [ simplify with monad laws | instantiate (1 := bempty); apply EnsembleListEquivalence_Empty ].

      subst_body; higher_order_1_reflexivity. (* TODO: finish constructing? *)

      (* Buffered pid value correct *)
      intros tuple in_empty;
      apply EnsembleListEquivalence_Empty in in_empty;
      intuition.
    }

    hone method ENUMERATE. {
      pose proof H;
      unfold NeatDB_equivalence in H;
      destruct H as (next_pid_correct & db_equiv);
      simpl Domain in next_pid_correct.

      setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      setoid_rewrite refineEquiv_pick_pair.
      setoid_rewrite refineEquiv_pick_eq'.
      simplify with monad laws.
      simpl.

      rewrite (Equivalent_UnConstr_In_EnsembleListEquivalence);
        eauto. (* TODO: Could explicitly pass the right list *)

      setoid_rewrite Equivalent_List_In_Where.

      rewrite (filter_by_equiv dec (@bfind_matcher _ _ _ (BagProof _ PIDIndex) (Some n, (None, []))))
        by (
            unfold ObservationalEq; simpl;
            unfold NatTreeExts.KeyFilter;
            unfold NatTreeExts.MoreFacts.BasicProperties.F.eq_dec;

            intros;
            rewrite ?andb_true_r, ?andb_true_l;
            intuition
          ).

      setoid_rewrite (@bfind_correct _ _ _ (BagProof _ PIDIndex) (snd r_n) (Some n, (None, []))).
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
    (* TODO: The insert_always_happens scripts could probably be made more generic *)

    hone method GET_CPU_TIME. {
      pose proof H;
      unfold NeatDB_equivalence in H;
      destruct H as (next_pid_correct & db_equiv);
      simpl Domain in next_pid_correct.

      setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      setoid_rewrite refineEquiv_pick_pair.
      setoid_rewrite refineEquiv_pick_eq'.
      simplify with monad laws.
      simpl.

      rewrite (Equivalent_UnConstr_In_EnsembleListEquivalence);
        eauto. (* TODO: Could explicitly pass the right list *)

      setoid_rewrite Equivalent_List_In_Where.
      rewrite (filter_by_equiv dec (@bfind_matcher _ _ _ (BagProof _ PIDIndex) (None, (Some n, []))))
        by (
            unfold ObservationalEq; simpl;
            unfold NatTreeExts.KeyFilter;
            unfold NatTreeExts.MoreFacts.BasicProperties.F.eq_dec;

            intros;
            rewrite ?andb_true_r, ?andb_true_l;
            intuition
          ).
      setoid_rewrite (@bfind_correct _ _ _ (BagProof _ PIDIndex) (snd r_n) (None, (Some n, []))).
      setoid_rewrite refine_For_List_Return.
      simplify with monad laws.

      rewrite refine_pick_val by eassumption.
      simplify with monad laws.
      finish honing.
    }

    hone method SPAWN. {
      pose proof H;
      unfold NeatDB_equivalence in H;
      destruct H as (next_pid_correct & db_equiv);
      simpl Domain in next_pid_correct.

      setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      setoid_rewrite refineEquiv_pick_pair.
      setoid_rewrite refineEquiv_pick_eq'.
      simplify with monad laws.
      simpl.

      rewrite refine_pick_val by eassumption.
      simplify with monad laws.

      rewrite insert_always_happens by eassumption.
      simplify with monad laws.

      rewrite insert_always_happens' by eassumption.
      simplify with monad laws.

      unfold NeatDB, NeatDB_equivalence.

      setoid_rewrite
        (refineEquiv_pick_pair_snd_dep
           (fun frist => forall tuple : Tuple, tuple ∈ _ -> frist > tuple PID)
           (fun pair  => EnsembleListEquivalence _ (benumerate (snd pair)))).

      simplify with monad laws.

      rewrite refine_pick_val;
        [ | instantiate (1 := S (fst r_n)) ].
      simplify with monad laws.

      rewrite refine_pick_val;
        [ | instantiate (1 := (binsert (snd r_n) <PID_COLUMN :: fst r_n, STATE_COLUMN :: SLEEPING, CPU_COLUMN :: 0>))].

      simplify with monad laws.

      finish honing.

      (* Insert correct *)
      unfold EnsembleListEquivalence in db_equiv |- *.

      setoid_rewrite (@binsert_enumerate _ _ _ (BagProof _ PIDIndex)).
      setoid_rewrite get_update_unconstr_iff.
      setoid_rewrite <- db_equiv.
      unfold RelationInsert, In in db_equiv |- *;
      intuition.

      (* Buffered value for next_pid correct *)
      unfold In, GetUnConstrRelation, UpdateUnConstrRelation, RelationInsert in next_pid_correct |- *;
      simpl in next_pid_correct |- *;
      intros tuple [ is_new | is_old ];
        [ subst | apply lt_S ];
        intuition.
    }

    finish sharpening.
  Defined.
End TreeBasedRefinement.
