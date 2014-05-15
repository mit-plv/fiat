Require Import List Omega Ensembles.

Require Import FMapAVL OrderedTypeEx.
Require Import FMapExtensions.
Require Import DBSchema SetEq AdditionalLemmas.
Require Export ADTRefinement.BuildADTRefinements.
Require Import GeneralInsertRefinements ListInsertRefinements
        GeneralQueryRefinements ListQueryRefinements.

Unset Implicit Arguments.
Notation "x '∈' y" := (In _ y x) (at level 50, no associativity).

Section ListBasedRefinement.
  Local Open Scope Tuple_scope.

  Definition SimpleDB := prod nat (list Process).

  Definition SimpleDB_equivalence rep (db: SimpleDB) :=
    (forall a, List.In a (snd db) -> fst db > (a PID)) /\
    EnsembleListEquivalence (GetUnConstrRelation rep PROCESSES) (snd db).

  Lemma refine_decision :
    forall n c,
    (forall a, (GetUnConstrRelation c PROCESSES) a ->
               n > (a PID)) ->
      refine
        ({b |
          decides b
                  (forall tup' : Tuple,
              GetUnConstrRelation c PROCESSES tup' ->
              tupleAgree
                <PID_COLUMN :: n, STATE_COLUMN :: Sleeping,
                   CPU_COLUMN :: 0> tup' [PID_COLUMN]%SchemaConstraints ->
              tupleAgree
                <PID_COLUMN :: n, STATE_COLUMN :: Sleeping,
                   CPU_COLUMN :: 0> tup'
                [CPU_COLUMN; STATE_COLUMN]%SchemaConstraints)})
        (ret true).
  Proof.
    unfold refine, decides; intros; constructor; inversion_by computes_to_inv; subst.
    unfold tupleAgree; intros.
    elimtype False; generalize (H _ H0), (H1 PID).
    unfold BuildTuple, PID, ith_Bounded; simpl; intros.
    rewrite H4 in H3; eauto.
    omega.
  Qed.

  Lemma refine_decision' :
    forall n c,
    (forall a, (GetUnConstrRelation c PROCESSES) a ->
               n > (a PID)) ->
      refine
        ({b |
          decides b
                  (forall tup' : Tuple,
              GetUnConstrRelation c PROCESSES tup' ->
              tupleAgree tup'
                <PID_COLUMN :: n, STATE_COLUMN :: Sleeping,
                   CPU_COLUMN :: 0> [PID_COLUMN]%SchemaConstraints ->
              tupleAgree tup'
                <PID_COLUMN :: n, STATE_COLUMN :: Sleeping,
                   CPU_COLUMN :: 0>
                [CPU_COLUMN; STATE_COLUMN]%SchemaConstraints)})
        (ret true).
  Proof.
    unfold refine, decides; intros; constructor; inversion_by computes_to_inv; subst.
    unfold tupleAgree; intros.
    elimtype False; generalize (H _ H0), (H1 PID).
    unfold BuildTuple, PID, ith_Bounded; simpl; intros.
    rewrite H4 in H3; eauto.
    omega.
  Qed.

  Lemma tupleAgree_sym :
    forall h: Heading,
    forall t1 t2 attrs,
      @tupleAgree h t1 t2 attrs <-> @tupleAgree h t2 t1 attrs.
  Proof.
    intros h t1 t2 attrs; unfold tupleAgree.
    assert (forall attr, t1 attr = t2 attr <-> t2 attr = t1 attr) as inner_sym by (split; symmetry; trivial).
    setoid_rewrite inner_sym.
    f_equiv.
  Qed.

  Require Import Computation.Refinements.Tactics.

  Definition ProcessScheduler :
    Sharpened ProcessSchedulerSpec.
  Proof.
    unfold ProcessSchedulerSpec.

    hone representation using (@DropQSConstraints_SiR ProcessSchedulerSchema).

    hone mutator SPAWN.
    {
      unfold ForAll_In.
      remove trivial insertion checks.
      finish honing.
    }

    (* == Introduce the list-based (SimpleDB) representation == *)
    hone representation using SimpleDB_equivalence.

    (* == Implement ENUMERATE == *)
    hone observer ENUMERATE.
    {
      unfold SimpleDB_equivalence in *.
      implement queries for lists.
      finish honing.
    }

    (* == Implement GET_CPU_TIME == *)
    hone observer GET_CPU_TIME.
    {
      unfold SimpleDB_equivalence in *.
      implement queries for lists.
      finish honing.
    }

    hone mutator SPAWN.
    {  
      unfold SimpleDB_equivalence in *; split_and.
       setoid_rewrite refineEquiv_split_ex.
       setoid_rewrite refineEquiv_pick_computes_to_and.
       setoid_rewrite (refine_pick_val _ (a := fst r_n)); eauto.
       simplify with monad laws.
       setoid_rewrite refine_decision; eauto; simplify with monad laws.
       setoid_rewrite refine_decision'; eauto; simplify with monad laws.
       rewrite refine_pick_eq_ex_bind.
       rewrite refineEquiv_pick_pair_fst_dep with
       (PA := fun (a : nat) (b : list Process) => forall t : Tuple, List.In t b -> a > t PID).
       setoid_rewrite ImplementListInsert_eq; eauto;
       simplify with monad laws.
       setoid_rewrite (refine_pick_val _ (a := S (fst r_n))); eauto;
       simplify with monad laws.
       finish honing.
       simpl; intros; intuition.
       subst; unfold BuildTuple, PID, ith_Bounded; simpl; omega.
       generalize (H1 _ H3); omega.
       intros; eapply H1; eapply H2; eauto.
       intros; eapply H1; eapply H2; eauto.
       intros; eapply H1; eapply H2; eauto.
    }

    finish sharpening.
  Defined.
End ListBasedRefinement.
