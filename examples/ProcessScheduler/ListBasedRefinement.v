Require Import DBSchema SetEq.
Require Import QueryStructureNotations.
Require Import ListImplementation.


Unset Implicit Arguments.
Notation "x '∈' y" := (In _ y x) (at level 50, no associativity).

Section ListBasedRefinement.

  Definition SimpleDB := prod nat (list Process).

  Definition SimpleDB_equivalence
             (rep : UnConstrQueryStructure ProcessSchedulerSchema)
             (db: SimpleDB) :=
    (forall a, List.In a (snd db) -> fst db > (a ! "pid")) /\
    rep ! "processes" ≃ snd db.

  Lemma refine_decision :
    forall n c,
    (forall a, (GetUnConstrRelation c PROCESSES) a ->
               n > (a ! "pid")) ->
      refine
        ({b |
          decides b
                  (forall tup' : IndexedTuple,
              GetUnConstrRelation c PROCESSES tup' ->
              tupleAgree
                <PID_COLUMN :: n, STATE_COLUMN :: SLEEPING,
                   CPU_COLUMN :: 0> tup' [PID_COLUMN]%SchemaConstraints ->
              tupleAgree
                <PID_COLUMN :: n, STATE_COLUMN :: SLEEPING,
                   CPU_COLUMN :: 0> tup'
                [CPU_COLUMN; STATE_COLUMN]%SchemaConstraints)})
        (ret true).
  Proof.
    unfold refine, decides; intros; constructor; inversion_by computes_to_inv; subst.
    unfold tupleAgree; intros.
    elimtype False; generalize (H _ H0), (H1 {| bindex := "pid" |}).
    unfold BuildTuple, GetAttribute; simpl; intros.
    rewrite H4 in H3; eauto.
    omega.
  Qed.

  Lemma refine_decision' :
    forall n c,
    (forall a, (GetUnConstrRelation c PROCESSES) a ->
               n > a ! "pid" ) ->
      refine
        ({b |
          decides b
                  (forall tup' : IndexedTuple,
              GetUnConstrRelation c PROCESSES tup' ->
              tupleAgree tup'
                <PID_COLUMN :: n, STATE_COLUMN :: SLEEPING,
                   CPU_COLUMN :: 0> [PID_COLUMN]%SchemaConstraints ->
              tupleAgree tup'
                <PID_COLUMN :: n, STATE_COLUMN :: SLEEPING,
                   CPU_COLUMN :: 0>
                [CPU_COLUMN; STATE_COLUMN]%SchemaConstraints)})
        (ret true).
  Proof.
    unfold refine, decides; intros; constructor; inversion_by computes_to_inv; subst.
    unfold tupleAgree; intros.
    elimtype False; generalize (H _ H0), (H1 {| bindex := "pid" |}).
    unfold BuildTuple, GetAttribute; simpl; intros.
    rewrite H4 in H3; eauto.
    omega.
  Qed.

  Opaque Query_For.

  Definition ProcessScheduler :
    Sharpened ProcessSchedulerSpec.
  Proof.
    unfold ProcessSchedulerSpec, ForAll_In.

    start honing QueryStructure.

    (* == Introduce the list-based (SimpleDB) representation == *)
    hone representation using SimpleDB_equivalence.

    (* == Implement ENUMERATE == *)
    hone method ENUMERATE.
    {
      unfold SimpleDB_equivalence in *; split_and; subst.
      setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      simplify with monad laws.
      rewrite refine_List_Query_In; eauto.
      rewrite refine_List_Query_In_Where.
      rewrite refine_List_For_Query_In_Return;
        simplify with monad laws; simpl.

      rewrite refineEquiv_pick_pair with
      (PA := fun a => (forall a0 : Process, List.In a0 (snd a) -> fst a > a0 PID)
                      /\ _ (snd a)).
      rewrite refineEquiv_pick_pair_fst_dep with
      (PA := fun a => (forall a0 : Process, List.In a0 (snd a) -> fst a > a0 PID)).
      repeat (rewrite refine_pick_val; [simplify with monad laws | eassumption]).
      setoid_rewrite refineEquiv_pick_eq'.
      simplify with monad laws.
      finish honing.
    }

    (* == Implement GET_CPU_TIME == *)
    hone method GET_CPU_TIME.
    {
      unfold SimpleDB_equivalence in *; split_and.
      setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      simplify with monad laws.

      rewrite refine_List_Query_In; eauto.
      rewrite refine_List_Query_In_Where.
      rewrite refine_List_For_Query_In_Return;
        simplify with monad laws; simpl.

      simpl; rewrite refineEquiv_pick_pair with
      (PA := fun a : SimpleDB => (forall a0 : Process, List.In a0 (snd a) -> fst a > a0 PID)
                      /\ EnsembleIndexedListEquivalence
        (c!"processes")%QueryImpl (snd a)).
      rewrite refineEquiv_pick_pair_fst_dep with
      (PA := fun a => (forall a0 : Process, List.In a0 (snd a) -> (fst a) > a0 PID)).
      repeat (rewrite refine_pick_val; [simplify with monad laws | eassumption]).
      setoid_rewrite refineEquiv_pick_eq'.
      simplify with monad laws.
      finish honing.
    }

    hone constructor INIT.
    {
      unfold SimpleDB_equivalence, DropQSConstraints_AbsR.
      repeat setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      repeat setoid_rewrite refineEquiv_pick_eq'.
      simplify with monad laws.
      rewrite refineEquiv_pick_pair_fst_dep with
      (PA := fun a => (forall a0 : Process, List.In a0 (snd a) -> (fst a) > a0 PID)).
      repeat (rewrite refine_pick_val;
              [simplify with monad laws
              | apply EnsembleListEquivalence_Empty]).
      rewrite refine_pick_val; simpl;
      eauto using EnsembleIndexedListEquivalence_Empty.
      simplify with monad laws.
      rewrite refine_pick_val with (A := nat) (a := 0).
      simplify with monad laws; 
      subst_body; higher_order_1_reflexivity.
      simpl; intros; intuition.
    }

    hone method SPAWN.
    {
      unfold SimpleDB_equivalence in *; split_and.
      setoid_rewrite refineEquiv_pick_ex_computes_to_bind_and.
      rewrite refine_pick_val with (A := nat) (a := fst r_n).
      simplify with monad laws.
      setoid_rewrite refineEquiv_split_ex.
      setoid_rewrite refineEquiv_pick_computes_to_and.
      simplify with monad laws.
      setoid_rewrite (refine_pick_val _ (a := length (snd r_n))); eauto.
      simplify with monad laws.
      setoid_rewrite refine_decision; eauto; try simplify with monad laws.
      setoid_rewrite refine_decision'; eauto; try simplify with monad laws.
      rewrite refine_pick_eq_ex_bind; simpl.
      rewrite refineEquiv_pick_pair with
      (PA := fun a => (forall a0 : Process, List.In a0 (snd a) -> fst a > a0 PID)
                      /\ _ (snd a)).
      rewrite refineEquiv_pick_pair_fst_dep with
      (PA := fun a => forall t : Tuple, List.In t (snd a) -> fst a > t PID).
      simplify with monad laws.
      setoid_rewrite (@ImplementListInsert_eq ProcessSchedulerSchema); eauto;
      simplify with monad laws.
      setoid_rewrite (refine_pick_val _ (a := S (fst r_n))); eauto.
      simplify with monad laws.
      setoid_rewrite refineEquiv_pick_eq';
        simplify with monad laws; simpl.
      finish honing.
      simpl; intros; intuition.
      subst; unfold BuildTuple, PID; simpl; omega.
      subst; unfold BuildTuple, PID, PID_COLUMN, GetAttribute in *;
      simpl; generalize (H1 _ H3); simpl; omega.
      destruct H2 as [_ [l [l_eq [NoDup l_equiv ]]]]; subst;
      intros; eapply H1; rewrite <- l_eq; eapply in_map; eapply l_equiv;
      eauto.
      destruct H2 as [_ [l [l_eq [NoDup l_equiv ]]]]; subst;
      intros; eapply H1; rewrite <- l_eq; eapply in_map; eapply l_equiv;
      eauto.
      unfold not, BuildTuple, PID, PID_COLUMN in *; intros; subst; simpl.
      destruct H2 as [tup_le _]; subst.
      apply tup_le in H; destruct tup; simpl in *; subst.
      eapply lt_irrefl; eapply H.
      unfold not; intros; destruct H2 as [_ [l [l_eq [NoDup l_equiv ]]]]; subst.
      rewrite H3 in H1; pose proof (H1 (indexedTuple tup)); rewrite <- l_eq in *.
      eapply lt_irrefl; eapply H2.
      eapply in_map_iff; eexists; split; eauto.
      eapply l_equiv; eauto.
    }

    finish sharpening.
  Defined.
End ListBasedRefinement.
