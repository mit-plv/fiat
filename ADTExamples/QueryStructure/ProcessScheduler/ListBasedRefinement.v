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
    EnsembleListEquivalence (GetUnConstrRelation rep PROCESSES) (snd db).

  Lemma refine_decision :
    forall c,
      refine
        ({ b
         | decides 
             b
             (forall tup' : Tuple,
                GetUnConstrRelation c PROCESSES tup' ->
                tupleAgree
                  (<PID_COLUMN :: 0, STATE_COLUMN :: Sleeping, CPU_COLUMN :: 0>) tup'
                  [CPU_COLUMN; STATE_COLUMN]%SchemaConstraints -> 
                tupleAgree
                  (<PID_COLUMN :: 0, STATE_COLUMN :: Sleeping, CPU_COLUMN :: 0>) tup' 
                  [PID_COLUMN]%SchemaConstraints) })
        (ret true).
  Proof.
    unfold refine, decides; intros; constructor; inversion_by computes_to_inv; subst.
    admit.
  Qed.

  Lemma refine_decision' :
    forall c,
      refine ({b |
               decides b
                       (forall tup' : Tuple,
                          GetUnConstrRelation c PROCESSES tup' ->
                          tupleAgree tup'
                          <PID_COLUMN :: 0, STATE_COLUMN :: Sleeping, 
                          CPU_COLUMN :: 0>
                          [CPU_COLUMN; STATE_COLUMN]%SchemaConstraints -> 
                          tupleAgree tup'
                          <PID_COLUMN :: 0, STATE_COLUMN :: Sleeping, 
                          CPU_COLUMN :: 0> [PID_COLUMN]%SchemaConstraints)}) (ret true).
  Proof.
    admit.
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

  Lemma refine_snd :
    forall {A B: Type} (P: B -> Prop),
      refine 
        { pair | P (snd pair) }
        (_fst <- Pick (fun (x: A) => True);
         _snd <- Pick (fun (y: B) => P y);
         ret (_fst, _snd)).
  Proof.
    t_refine.
  Qed.

  Lemma refine_ret_eq :
    forall {A: Type} (a: A) b,
      b = ret a -> refine (ret a) (b).
  Proof.
    t_refine.
  Qed.

  Lemma ret_computes_to :
    forall {A: Type} (a1 a2: A),
      ret a1 ↝ a2 <-> a1 = a2.
  Proof.
    t_refine.
  Qed.

  Definition ProcessScheduler :
    Sharpened ProcessSchedulerSpec.
  Proof.
    unfold ProcessSchedulerSpec.

    hone representation using (@DropQSConstraints_SiR ProcessSchedulerSchema).

    hone mutator SPAWN.
    {
      remove trivial insertion checks.
      finish honing.
    }

    (* == Introduce the list-based (SimpleDB) representation == *)
    hone representation using SimpleDB_equivalence.

    (* == Implement ENUMERATE == *)
    hone_observer' ENUMERATE.

    intros db state result computes set_db_unconstr set_db constr_unconstr_equiv db_equiv.

    unfold SimpleDB_equivalence, DropQSConstraints_SiR in *;
      rewrite <- constr_unconstr_equiv, GetRelDropConstraints in db_equiv.

    rewrite (refine_ensemble_into_list_with_extraction (snd db) _ _ _ (fun p => beq_state p!STATE state));
      eauto using beq_process_iff__state.

    refine_eq_into_ret;
      eexists.

    (* == Implement GET_CPU_TIME == *)
    hone_observer' GET_CPU_TIME.

    intros db pid result computes set_db_unconstr set_db constr_unconstr_equiv db_equiv.

    unfold SimpleDB_equivalence, DropQSConstraints_SiR in *;
      rewrite <- constr_unconstr_equiv, GetRelDropConstraints in db_equiv.

    rewrite (refine_ensemble_into_list_with_extraction (snd db) _ _ _ (fun p => beq_nat p!PID pid) _);
      eauto using beq_process_iff__pid.

    refine_eq_into_ret;
      eexists.
    
    (* == Implement SPAWN == *)
    hone mutator SPAWN.

    setoid_rewrite refineEquiv_split_ex.
    setoid_rewrite refineEquiv_pick_computes_to_and.
    simplify with monad laws.

    setoid_rewrite refine_pick_eq_ex_bind. 
    setoid_rewrite refine_decision; setoid_rewrite refine_decision'; 
    simplify with monad laws.

    (* Check refineEquiv_pick_pair. *)
    unfold SimpleDB_equivalence. 
    setoid_rewrite (refine_snd (fun b => EnsembleListEquivalence _ b)).
    setoid_rewrite (refine_pick_val _ (a := S (fst r_n))); eauto.
    simplify with monad laws.
    setoid_rewrite ImplementListInsert_eq; eauto.
    simplify with monad laws.
    apply refine_ret_eq; unfold H0; clear H0; eexists.

    finish sharpening.
  Defined.
End ListBasedRefinement.
