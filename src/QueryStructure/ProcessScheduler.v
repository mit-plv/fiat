Require Import String Omega List FunctionalExtensionality Ensembles.
Require Export Computation ADT ADTRefinement ADT.Pick
        ADTRefinement.BuildADTRefinements ADTNotation ADTNotation.BuildADT GeneralBuildADTRefinements
        QueryStructureSchema QueryQSSpecs InsertQSSpecs QueryStructure.

Generalizable All Variables.
Set Implicit Arguments.

Section ProcessSchedulerExample.
  Open Scope QSSchema.
  Local Open Scope ADTSig_scope.
  Local Open Scope QueryStructureParsing_scope.
  Local Open Scope Schema.
  Local Open Scope QuerySpec.
  Open Scope string_scope.

  Inductive State := Sleeping | Running.

  Instance State_eq : Query_eq State.
  Proof.
    constructor; decide equality.
  Defined.

  Definition PROCESSES_TABLE := "Processes".
  Definition NS    := "ns".
  Definition PID   := "pid".
  Definition STATE := "state".
  Definition CPU   := "cpu".

  Definition ProcessSchedulerSchema := query structure schema [
    relation PROCESSES_TABLE has schema <NS    : nat,
                                         PID   : nat,
                                         STATE : State,
                                         CPU   : nat>
    where attributes [CPU; STATE] depend on [NS; PID]
  ] enforcing [].

  Definition ProcessSchedulerRefRep := @QueryStructure ProcessSchedulerSchema.

  Definition ProcessSchema := schemaHeading (GetNamedSchema ProcessSchedulerSchema PROCESSES_TABLE).

  Definition Process := (Tuple ProcessSchema).

  Definition SPAWN     := "Spawn".
  Definition ENUMERATE := "Enumerate".q
  Definition COUNT     := "Count".

  Definition ProcessSchedulerSig := ADTsignature {
    SPAWN     : rep × nat     → rep(*,
    "Kill"    : rep × nat     → rep,
    "Suspend" : rep × nat     → rep,
    "Resume"  : rep × nat     → rep*);
    ENUMERATE : rep × State   → list (prod nat nat)(*,
    COUNT     : rep × unit    → nat*)
  }.

  (*Arguments qsSchemaHint _ /.*)

  Local Open Scope Tuple_scope.

  Definition ProcessSchedulerSpec : ADT ProcessSchedulerSig :=
    QueryADTRep
      ProcessSchedulerRefRep {
        def update SPAWN (ns : nat) : rep := (* TODO: pid/0 *)
          Insert <NS: ns, PID: 0, STATE: Sleeping, CPU: 0> into PROCESSES_TABLE;

        def query ENUMERATE (state : State) : list (prod nat nat) :=
          For (p in PROCESSES_TABLE)
              Where (p!STATE == state)
              Return (p!NS, p!PID)(*,

        def query COUNT (_: unit) : nat :=
          Count (For (p in PROCESSES_TABLE)
                 Return 1)*)
      }.

  Local Close Scope QueryStructureParsing_scope.

  Definition SimpleDB := list Process.

  Definition beq_state s1 s2 :=
    match s1, s2 with
      | Sleeping, Sleeping => true
      | Running , Running  => true
      | _       , _        => false
    end.

  Definition ExtractNSAndPID (processes : list Process) :=
    map (fun p => (p!NS, p!PID)) processes.

  Definition SimpleDB_equivalence (rep: ProcessSchedulerRefRep) (db: SimpleDB) :=
    (GetRelation rep PROCESSES_TABLE) = db.

  Definition SimpleDB_enumerate db state :=
    ret (ExtractNSAndPID
           (filter (fun (p: Process) => beq_state p!STATE state) db)).

  Definition SimpleDB_spawn (db: list Process) (ns: nat) :=
    ret (<NS: ns, PID: 0, STATE: Sleeping, CPU: 0> :: db).

  Lemma eq_ret_compute :
    forall (A: Type) (x y: A), x = y -> ret x ↝ y.
  Proof.
    intros; subst; apply ReturnComputes; trivial.
  Qed.

  Lemma eq_indistinguishable :
    forall {A: Type} (l1 l2: list A), l1 = l2 -> indistinguishable l1 l2.
  Proof.
    intros A l1 l2 eq12; unfold indistinguishable; subst l2; induction l1; [apply perm_nil | apply perm_skip]; trivial.
  Qed.

  Ltac rinse func param_name :=
    intros r_o newrep param_name eq_ro_newrep;
    subst r_o;
    unfold refine;
    intros v new_impl_computes_to_v;
    unfold func in new_impl_computes_to_v;
    inversion_by computes_to_inv;
    subst v.

  Definition ProcessScheduler :
    Sharpened ProcessSchedulerSpec.
  Proof.
    hone representation' using SimpleDB_equivalence.

    hone' observer ENUMERATE using SimpleDB_enumerate;
      [ rinse SimpleDB_enumerate state | ].

    constructor 3;
      intros oldrep oldrep_equiv_newrep;
      constructor 3.

    rewrite oldrep_equiv_newrep;
      clear oldrep_equiv_newrep.

    apply eq_indistinguishable.

    induction newrep as [ | head tail IH];
      simpl in *;
      [ | rewrite <- IH;
          destruct (head!(STATE)), state;
          simpl ];
      trivial.

    hone' mutator SPAWN using SimpleDB_spawn;
      [ rinse SimpleDB_spawn ns | ].

    apply (BindComputes _ (comp_a_value := <NS : ns, PID : 0, STATE : Sleeping, CPU : 0> :: newrep));
      constructor; [ | trivial].

    intros oldrep oldrep_equiv_newrep.

    Definition rels_builder (db: SimpleDB) _constr_ :
      ilist (fun ns : NamedSchema => Relation (relSchema ns))
            (qschemaSchemas ProcessSchedulerSchema) :=
      icons (B := fun ns => Relation (relSchema ns)) _
            {| rel := db; constr := _constr_ |} (inil _).

    Definition ref_rep_builder db _constr_ _crossConstr_ : QueryStructure ProcessSchedulerSchema :=
      {| rels := rels_builder db _constr_; crossConstr := _crossConstr_ |}.

    eexists (ref_rep_builder (<NS : ns, PID : 0, STATE : Sleeping, CPU : 0> :: newrep) _ _).

    constructor;
      [ constructor | ].

    rewrite <- oldrep_equiv_newrep;
      unfold QSInsertSpec;
      simpl;
      intros;
      unfold GetRelation;
      simpl;
      trivial.

    unfold ref_rep_builder, rels_builder, QSInsertSpec, SimpleDB_equivalence, GetRelation;
      simpl;
      trivial.

    finish sharpening.

    Grab Existential Variables.

    simpl; trivial.

    intros; simpl in *. (* TODO: Verify this. Shouldn't tup2 be in <...> :: newrep as well? *)
    (*
      unfold tupleAgree; simpl. intros. simpl in H.
      specialize (H0 attr).
      destruct H1; subst; simpl in H0.
    *)
  Admitted.

  Inductive BinaryTree :=
  | Empty : BinaryTree
  | Leaf : Process -> BinaryTree
  | Branch : BinaryTree -> BinaryTree -> BinaryTree.

  Fixpoint InTree process tree :=
    match tree with
      | Empty => False
      | Leaf p => process = p
      | Branch lbranch rbranch => InTree process lbranch \/ InTree process rbranch
    end.

  Fixpoint IsSearchTree tree :=
    match tree with
      | Empty => True
      | Leaf _ => True
      | Branch lbranch rbranch =>
        IsSearchTree lbranch
        /\ IsSearchTree rbranch
        /\ (forall (procl procr : Process),
              InTree procl lbranch ->
              InTree procr rbranch ->
              le procl!PID procr!PID)
    end.

  (* TODO: Look at fmap *)

  Fixpoint ValuesMatch (*prop*) value tree :=
    match tree with
      | Empty => True
      | Leaf p => p!STATE = value
      | Branch lbranch rbranch => ValuesMatch (*prop*) value lbranch /\ ValuesMatch (*prop*) value rbranch
    end.

  Definition SortedDB_table state :=
    sig (fun table : BinaryTree => ValuesMatch state table /\ IsSearchTree table).

  Definition SortedDB := prod (SortedDB_table Running) (SortedDB_table Sleeping).

  Definition ExtractTree {state : State} (table : SortedDB_table state) := proj1_sig table.

  Fixpoint Flatten tree :=
    match tree with
      | Empty => []
      | Leaf l => [l]
      | Branch lbranch rbranch => (Flatten lbranch ++ Flatten rbranch) % list
    end.

  Check sig.

  Definition ExtractCorrespondingTree (state: State) (db: SortedDB) :=
    ExtractTree (
        match state with
          | Running => fst db
          | Sleeping => snd db
        end
      ).

  Definition InDB x db :=
    InTree x (ExtractCorrespondingTree x!STATE db).

  Definition SortedDB_enumerate (db : SortedDB) state :=
    ret (ExtractNSAndPID (Flatten (ExtractCorrespondingTree state db))).

  Definition SortedDB_equivalence (ref: ProcessSchedulerRefRep) (db : SortedDB) :=
    forall x, List.In x (GetRelation ref PROCESSES_TABLE) <-> InDB x db.

  Lemma sharpened_btree :
    Sharpened ProcessSchedulerSpec.
  Proof.
    hone representation' using SortedDB_equivalence.

    hone' observer ENUMERATE using SortedDB_enumerate;
      [ rinse SortedDB_enumerate state | ].

    unfold GetRelation;
      constructor 3;
      intros oldrep oldrep_equiv_newrep;
      constructor.

    unfold ExtractNSAndPID, Flatten, ExtractCorrespondingTree; destruct state, newrep; simpl.

    (*
      Lemma lists_without_elements_are_empty:
        forall (A: Type) (lst: list A), (forall item, List.In item lst <-> False) -> lst = [].
      Proof.
        intros A lst H; destruct lst as [|a]; intuition.
        specialize (H a); simpl in H.
        exfalso; apply H; intuition.
      Qed.
    *)

    (* Notations improvements: Hide types? Devise a better indentation strategy? *)
  Admitted.
End ProcessSchedulerExample.
