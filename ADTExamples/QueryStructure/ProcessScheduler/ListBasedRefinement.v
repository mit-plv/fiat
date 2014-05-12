Require Import List Omega Ensembles.

Require Import FMapAVL OrderedTypeEx.
Require Import FMapExtensions.
Require Import DBSchema SetEq AdditionalLemmas.
Require Export ADTRefinement.BuildADTRefinements.

Unset Implicit Arguments.

Section ListBasedRefinement.
  Local Open Scope Tuple_scope.

  Definition SimpleDB := list Process.

  Definition SimpleDB_equivalence (rep: ProcessSchedulerRefRep) (db: SimpleDB) :=
    forall a, In _ (GetRelation rep PROCESSES) a <-> List.In a db.

(*
  Definition rels_builder (db: SimpleDB) _constr_
    : ilist (fun ns : NamedSchema => Relation (relSchema ns))
            (qschemaSchemas ProcessSchedulerSchema) :=
    icons (B := fun ns => Relation (relSchema ns)) _
          {| rel := db; constr := _constr_ |} (inil _).

  Definition ref_rep_builder db _constr_ _crossConstr_
    : QueryStructure ProcessSchedulerSchema :=
    {| rels := rels_builder db _constr_; crossConstr := _crossConstr_ |}.
*)

  (*TODO: Why doesn't
        hone' observer ENUMERATE; simpl in *.
      behave the same as
        hone' observer ENUMERATE. simpl in *.
   *)

  Definition ProcessScheduler :
    Sharpened ProcessSchedulerSpec.
  Proof.
    (* == Introduce the list-based (SimpleDB) representation == *)
    hone representation' using SimpleDB_equivalence.

    (* == Implement ENUMERATE == *)

    hone_observer' ENUMERATE.

    intros db state result computes set_db db_equiv.

    rewrite (refine_ensemble_into_list_with_extraction db _ _ _ (fun p => beq_state p!STATE state));
      eauto using beq_process_iff__state.

    refine_eq_into_ret;
      eexists.

    hone_observer' GET_CPU_TIME.

    intros db pid result computes set_db db_equiv.

    Check refine_ensemble_into_list_with_extraction.
    rewrite (refine_ensemble_into_list_with_extraction db _ _ _ (fun p => beq_nat p!PID pid) _);
      eauto using beq_process_iff__pid.

    refine_eq_into_ret;
      eexists.

    (* == Implement SPAWN == *)
    (*
    hone' mutator SPAWN using SimpleDB_spawn;
      [ rinse SimpleDB_spawn ns | ].

    apply (BindComputes _ (comp_a_value :=
             <NS : ns, PID : 0, STATE : Sleeping, CPU : 0> :: newrep));
      constructor;
      [ | trivial].

    intros oldrep oldrep_equiv_newrep;
      eexists (ref_rep_builder
                 (<NS : ns, PID : 0, STATE : Sleeping, CPU : 0> :: newrep)
                 _ _);
      constructor.

    (* QSInsertSpec computes to the
       representation introduced above *)
    constructor;
      rewrite <- oldrep_equiv_newrep;
      unfold QSInsertSpec, GetRelation;
      trivial.

    (* That representation is equivalent (modulo
       SimpleDB_equivalence) to our implementation *)
    unfold ref_rep_builder, rels_builder,
           QSInsertSpec, SimpleDB_equivalence, GetRelation;
      trivial.

    finish sharpening.

    (* == Prove that DB constraints are satisfied == *)
    Grab Existential Variables.

    (* Cross-table constraints (?) *)
    simpl; trivial.

    (* Single-table constraints *)
    intros; simpl in *.

    (*
      unfold tupleAgree; simpl. intros. simpl in H.
      specialize (H0 attr).
      destruct H1; subst; simpl in H0.
     *)
    (* TODO: Verify this. Shouldn't tup2 be in <...> :: newrep as well? *)
     *)
  Admitted.
End ListBasedRefinement.
