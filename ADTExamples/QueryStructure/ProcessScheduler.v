Require Import String Omega List FunctionalExtensionality Ensembles. 
Require Export Computation ADT ADTRefinement ADT.Pick
        ADTRefinement.BuildADTRefinements ADTNotation ADTNotation.BuildADT GeneralBuildADTRefinements
        QueryStructureSchema QueryQSSpecs InsertQSSpecs QueryStructure.

Require Import FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.

Require Import Bool DecidableType DecidableTypeEx OrderedType Morphisms.
Require Export FMapInterface.
Set Implicit Arguments.
Require Import Coq.FSets.FMapFacts.

Unset Implicit Arguments.

Definition SetEq {A: Type} (seq1: list A) (seq2: list A) :=
  forall x,
    List.In x seq1 <-> List.In x seq2.

Ltac autospecialize :=
  repeat match goal with
             [ H: forall _, _ |- List.In ?x _ ] => try specialize (H x)
         end.

Lemma SetEq_Reflexive :
  forall {A: Type}, forall (x: list A), SetEq x x.
Proof.
  unfold Reflexive, SetEq; 
  intuition;
  autospecialize;
  intuition.
Qed. 

Lemma SetEq_Symmetric :
  forall {A: Type}, forall (x y: list A), SetEq x y -> SetEq y x.
Proof.
  unfold Symmetric, SetEq; 
  intuition; autospecialize; intuition.
Qed.

Lemma SetEq_Symmetric_iff:
  forall {A: Type}, forall (x y: list A), SetEq x y <-> SetEq y x.
Proof.
  split; eauto using SetEq_Symmetric.
Qed.

Lemma SetEq_Transitive :
  forall {A: Type}, forall (x y z: list A), SetEq x y -> SetEq y z -> SetEq x z.
Proof.
  unfold Transitive, SetEq; 
  intuition; autospecialize; intuition.
Qed.

Lemma SetEq_Equivalence:
  forall {A: Type}, Equivalence (SetEq (A:=A)).
Proof.
  intros; constructor; eauto using SetEq_Transitive, SetEq_Symmetric, SetEq_Reflexive.
Qed.

Require Import Setoid.

Add Parametric Relation (A: Type) : (list A) (@SetEq A)
    reflexivity proved by SetEq_Reflexive
    symmetry proved by SetEq_Symmetric
    transitivity proved by SetEq_Transitive
      as set_eq.

Ltac seteq_equivalence :=
  eauto using SetEq_Transitive, SetEq_Symmetric, SetEq_Reflexive.

Lemma SetEq_trans_iff:
  forall {A: Type} (seq1 seq1' seq2: list A),
    SetEq seq1 seq1' ->
    (SetEq seq1 seq2 <-> SetEq seq1' seq2).
Proof.
  intuition; seteq_equivalence.
Qed.

Lemma SetEq_trans_iff_2:
  forall {A: Type} (seq1 seq2 seq2': list A),
    SetEq seq2 seq2' ->
    (SetEq seq1 seq2 <-> SetEq seq1 seq2').
Proof.
  intuition; seteq_equivalence.
Qed.

Definition ValueFilter {A B: Type} (pred: B -> bool) :=
  (fun (key: A) (value: B) => pred value).

Definition IsSetEqSafe {A B: Type} (proc: list A -> list B) :=
  forall (seq1 seq2: list A), 
    SetEq seq1 seq2 -> 
    SetEq (proc seq1) (proc seq2).

Lemma SetEq_modulo_SetEqSafe_fun : 
  forall {A B: Type},
  forall (seq1: list B) (seq2 seq3: list A),
  forall (proc: list A -> list B),
    SetEq seq2 seq3 ->
    IsSetEqSafe proc ->
    (SetEq seq1 (proc seq2) <-> SetEq seq1 (proc seq3)).
Proof.
  intros; eauto using SetEq_trans_iff_2.
Qed.

Lemma SetEq_after_map : 
  forall {A B: Type} (seq1 seq2: list A),
  forall (proc: A -> B),
    SetEq seq1 seq2 -> SetEq (map proc seq1) (map proc seq2).
Proof.
  intros ? ? ? ? ? set_eq;
  unfold SetEq in *;
  intro x;
  split;
  intros in_map;
  rewrite in_map_iff in in_map;
  destruct in_map as [pred (is_pred, pred_in_list)];
  specialize (set_eq pred);
  subst;
  intuition;
  eauto using in_map.
Qed.

Lemma map_modulo_SetEq :
  forall {A B: Type} (seq1 seq1': list A) (seq2: list B), 
  forall (proc: A -> B),
    SetEq seq1 seq1' -> 
    (SetEq (map proc seq1) (seq2) <-> SetEq (map proc seq1') (seq2)).
Proof.
  intros; 
  simpl;
  apply SetEq_trans_iff;
  apply SetEq_after_map;
  trivial.
Qed.

Lemma IsSetEqSafe_map :
  forall {A B: Type} (proc: A -> B), 
    IsSetEqSafe (fun x => List.map proc x).
Proof.
  unfold IsSetEqSafe; 
  eauto using SetEq_after_map.
Qed.

Lemma IsSetEqSafe_filter :
  forall {A: Type} (pred: A -> bool),
    IsSetEqSafe (fun x => List.filter pred x).
Proof.
  unfold IsSetEqSafe, SetEq; 
  intros;
  repeat rewrite filter_In;
  specialize (H x);
  intuition.
Qed.

Lemma not_InA_not_In : 
  forall {A: Type} l eqA (x: A), 
    Equivalence eqA ->
    not (InA eqA x l) -> not (List.In x l).
Proof.
  intros A l;
  induction l;
  intros ? ? equiv not_inA in_l;
  simpl in *;
  
  [ trivial
  | destruct in_l as [eq | in_l];
    subst;
    apply not_inA;
    pose proof equiv as (?,?,?);
    eauto using InA_cons_hd, InA_cons_tl, (In_InA equiv)
  ].
Qed.

Lemma NoDupA_stronger_than_NoDup : 
  forall {A: Type} (seq: list A) eqA, 
    Equivalence eqA ->
    NoDupA eqA seq -> NoDup seq.
Proof.
  intros ? ? ? ? nodupA;
  induction nodupA;
  constructor;
  [ apply (not_InA_not_In _ _ _ _ H0)
  | trivial].
(* Alternative proof: red; intros; apply (In_InA (eqA:=eqA)) in H2; intuition. *)
Qed.

Module MoreFMapFacts_fun (E: DecidableType) (Import M: WSfun E).
  Module Export BasicFacts := WFacts_fun E M.
  Module Export BasicProperties := WProperties_fun E M.

  Definition GetValues {A: Type} (db: t A) :=
    List.map snd (elements db).

  Definition SameElements {A: Type} (seq: list A) (db: t A) :=
    SetEq seq (GetValues db).

  Lemma InA_In:
    forall (A : Type) (x : A) (l : list A),
      InA eq x l -> List.In x l.
  Proof.
    intros ? ? ? H; 
    induction H; 
    simpl;
    intuition.
  Qed.

  Lemma elements_iff :
    forall (elt : Type) (m : t elt) (x : key) (e : elt),
      MapsTo x e m <-> InA (eq_key_elt (elt:=elt)) (x, e) (elements (elt:=elt) m).
  Proof.
    intros; split;
    eauto using elements_1, elements_2.
  Qed.

  Lemma InA_In_snd : 
    forall {A: Type} (k: key) (e: A) (l : list (key*A)),
      InA (eq_key_elt (elt:=A)) (k, e) l -> List.In e (List.map snd l).
  Proof.
    intros ? k e ? in_a;
    rewrite InA_alt, in_map_iff in *;
    destruct in_a as [(k', e') (eq0, ?)];
    destruct eq0; simpl in *;
    exists (k', e'); intuition.
  Qed.

  Lemma Equivalence_eq_key_elt : 
    forall {A: Type}, Equivalence (eq_key_elt (elt := A)).
  Proof.
    unfold eq_key_elt;
    repeat constructor;
    simpl in *; 
    intuition;
    eauto using E.eq_trans, eq_trans.
  Qed.      

  Lemma eq_stronger_than_eq_key_elt : 
    forall {A: Type} x seq, 
      InA eq x seq -> InA (eq_key_elt (elt:=A)) x seq.
  Proof.
    intros.
    apply InA_In in H.
    apply (In_InA Equivalence_eq_key_elt);
      trivial.
  Qed. 

  Lemma in_elements_mapsto : 
    forall {A: Type} k (e: A) (m: t A), 
      List.In (k, e) (elements m) -> MapsTo k e m.
    intros; 
    eauto using elements_2, (In_InA Equivalence_eq_key_elt).
  Qed.

  Lemma in_elements_after_map : 
    forall {A B: Type} (proc: A -> B) (m: t A) (x: B),
      List.In x (List.map snd (elements (map proc m)))
      -> exists k pred, MapsTo k pred m /\ proc pred = x.  
    intros ? ? ? ? ? in_map;
    rewrite in_map_iff in in_map;
    destruct in_map as [(k, e) (is_proc, in_elements)];
    apply in_elements_mapsto in in_elements;
    rewrite map_mapsto_iff in in_elements;
    destruct in_elements as [e_pred (is_pred, maps_to)];
    exists k e_pred;
    subst; intuition.
  Qed.

  SearchAbout InA List.In snd.
  
  Lemma map_list_map_fmap:
    forall {A B: Type} m (proc: A -> B),
    SetEq (GetValues (map proc m)) (List.map proc (GetValues m)).  
  Proof.
    unfold GetValues; split; intros.
 
    apply in_elements_after_map in H;
    destruct H as [k [predecessor (maps_to, is_predecessor)]];
    rewrite in_map_iff;
    exists predecessor;
    subst; 
    intuition;
    apply (InA_In_snd k), elements_1;
    trivial.

    rewrite in_map_iff in H;
    destruct H as [x0 (?, H)];
    rewrite in_map_iff in H;
    destruct H as [x1 (is_pred, ?)].

    apply (InA_In_snd (fst x1));
    rewrite <- elements_mapsto_iff;
    apply map_mapsto_iff;
    exists x0;
    split;
    [ | apply in_elements_mapsto;
        rewrite <- is_pred, <- surjective_pairing ];
    subst;
    congruence.
  Qed.

  Lemma ValueFilter_proper: 
    forall (B: Type) (pred: B->bool), 
      Proper (E.eq ==> eq ==> eq) (ValueFilter pred).
  Proof.
    unfold Proper; compute; intros; subst; trivial.
  Qed.

  Lemma filter_list_filter_fmap :
    forall {A: Type} m pred,
      SetEq (List.filter pred (GetValues (A:=A) m)) (GetValues (filter (ValueFilter pred) m)).
  Proof. 
    intros.
    unfold SetEq; intuition.
    unfold GetValues.

    rewrite filter_In in H.
    destruct H as [inL sat].
    unfold GetValues in inL.
    apply in_map_iff in inL.
    destruct inL as [x0 (ok, inL)].
    
    destruct x0.
    apply in_elements_mapsto in inL.
    subst.
    simpl.

    apply (InA_In_snd k).
    apply elements_mapsto_iff.
    Check filter_iff.
    rewrite filter_iff.
    intuition.

    eauto using ValueFilter_proper.

    unfold GetValues in *.
    rewrite filter_In.

    rewrite in_map_iff in H.
    destruct H as [(k, e) (is_snd, is_in)].

    apply in_elements_mapsto in is_in.

    rewrite filter_iff in is_in; eauto using ValueFilter_proper.

    destruct is_in as [maps_to sat].
    compute in sat.
    simpl in *.
    subst.
    intuition.

    rewrite elements_mapsto_iff in maps_to.
    apply (InA_In_snd k).
    trivial.
  Qed.
  
  Lemma map_modulo_equiv : 
    forall {A B: Type} (db: t A) (seq: list A),
      SameElements seq db -> 
      forall (proc: A -> B), 
        SameElements (List.map proc seq) (map proc db).
  Proof.
    unfold SameElements; intros.
    rewrite (map_modulo_SetEq _ (GetValues db)); trivial.
    clear H; clear seq.
    unfold SetEq.
    symmetry.
    apply map_list_map_fmap.
  Qed.

  Add Parametric Morphism {A B: Type} (proc: A -> B) :
    (List.map proc)
      with signature (@SetEq A ==> @SetEq B)
        as filter_morphism.
  Proof.
    apply IsSetEqSafe_map.
  Qed.

  Add Parametric Morphism {A: Type} (pred: A -> bool) :
    (List.filter pred)
      with signature (@SetEq A ==> @SetEq A)
        as map_morphism.
  Proof.
    apply IsSetEqSafe_filter.
  Qed.
End MoreFMapFacts_fun.

Module MoreFMapFacts (M: WS) := MoreFMapFacts_fun M.E M.

Module GenericTreeDB := FMapAVL.Make(Nat_as_OT). (* TODO: Add the generic implementation *)
Module DBExtraFacts := MoreFMapFacts GenericTreeDB.
Import DBExtraFacts.

Section ProcessSchedulerExample.
  Open Scope QSSchema.
  Local Open Scope ADTSig_scope.
  Local Open Scope QueryStructureParsing_scope.
  Local Open Scope Schema.
  Local Open Scope QuerySpec.
  Local Open Scope string_scope.
  Local Open Scope Tuple_scope.

  Inductive State := Sleeping | Running.

  Instance State_eq : Query_eq State.
  Proof.
    constructor; decide equality.
  Defined.

  Opaque State_eq.

  Definition PID_COLUMN := "pid".
  Definition STATE_COLUMN := "state".
  Definition CPU_COLUMN := "cpu".
  Definition PROCESSES_TABLE := "processes".

  Notation "` A" := {| bindex := A |}.
  Definition ProcessSchedulerSchema := query structure schema [
    relation PROCESSES_TABLE has schema <PID_COLUMN   : nat,
                                         STATE_COLUMN : State,
                                         CPU_COLUMN   : nat>
    where attributes [`CPU_COLUMN; `STATE_COLUMN] depend on [`PID_COLUMN]
  ] enforcing [].

  Definition PROCESSES := GetRelationKey ProcessSchedulerSchema PROCESSES_TABLE.

  Definition PID   := GetAttributeKey PROCESSES PID_COLUMN.
  Definition STATE := GetAttributeKey PROCESSES STATE_COLUMN.
  Definition CPU   := GetAttributeKey PROCESSES CPU_COLUMN.

  Definition ProcessSchedulerRefRep := 
    @QueryStructure ProcessSchedulerSchema.

  Definition ProcessSchema := 
    QSGetNRelSchemaHeading ProcessSchedulerSchema PROCESSES.

  Notation Process := (Tuple ProcessSchema).

  Definition SPAWN        := "Spawn".
  Definition ENUMERATE    := "Enumerate".
  Definition GET_CPU_TIME := "GetCPUTime".
  Definition COUNT        := "Count".

  Definition ProcessSchedulerSig := ADTsignature {
    SPAWN        : rep × nat     → rep(*,
    "Kill"       : rep × nat     → rep,
    "Suspend"    : rep × nat     → rep,
    "Resume"     : rep × nat     → rep*);
    ENUMERATE    : rep × State   → list nat,
    GET_CPU_TIME : rep × nat     → list nat (*,
    COUNT        : rep × unit    → nat*)
  }.

  Require Import Coq.Unicode.Utf8_core.

  Definition ProcessSchedulerSpec : ADT ProcessSchedulerSig := 
    QueryADTRep 
      ProcessSchedulerRefRep {
        def update SPAWN (ns : nat) : rep := (* TODO: pid/0 *)
          Insert <PID_COLUMN: 0, STATE_COLUMN: Sleeping, CPU_COLUMN: 0> into PROCESSES;
          
        def query ENUMERATE (state : State) : list nat :=
          For (p in PROCESSES)
              Where (p!STATE = state)
              Return (p!PID), 

        def query GET_CPU_TIME (id : nat) : list nat :=
          For (p in PROCESSES)
              Where (p!PID = id)
              Return (p!CPU)
(*,
          
        def query COUNT (_: unit) : nat :=
          Count (For (p in PROCESSES_TABLE) 
                 Return 1)*)
      }.

  Definition SimpleDB := list Process.

  Definition beq_state s1 s2 :=
    match s1, s2 with
      | Sleeping, Sleeping => true
      | Running , Running  => true
      | _       , _        => false
    end.

  Ltac beq_state_crush :=
    intros;
    repeat match goal with 
             | [ s: State |- _ ] => destruct s
           end;
    unfold beq_state; intuition; try discriminate.

  Lemma beq_state_true_iff : 
    forall s1 s2, beq_state s1 s2 = true <-> s1 = s2.
  Proof.
    beq_state_crush.
  Qed.

  Lemma beq_state_false_iff : 
    forall s1 s2, beq_state s1 s2 = false <-> s1 <> s2.
  Proof.
    beq_state_crush.
  Qed.

  Lemma beq_state_sym :
    forall s1 s2, beq_state s1 s2 = beq_state s2 s1.
  Proof.
    beq_state_crush.
  Qed.

  Definition SimpleDB_equivalence (rep: ProcessSchedulerRefRep) (db: SimpleDB) :=
    forall a, In _ (GetRelation rep PROCESSES) a <-> List.In a db.

  Lemma eq_ret_compute : 
    forall (A: Type) (x y: A), x = y -> ret x ↝ y.
  Proof.
    intros; subst; apply ReturnComputes; trivial.
  Qed.
  
  (* "Rinse" just cleans up the goal after honing a representation *)
  Ltac rinse func param_name :=
    intros r_o newrep param_name eq_ro_newrep;
    subst r_o;
    unfold refine;
    intros v new_impl_computes_to_v;
    unfold func in new_impl_computes_to_v;
    inversion_by computes_to_inv;
    subst v.
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
  Lemma refine_eqA_into_ret :
    forall {A: Type} {eqA: list A -> list A -> Prop},
      Reflexive eqA ->
      forall (comp : Comp (list A)) (impl result: list A),
        comp = ret impl -> (
          comp ↝ result ->
          eqA result impl 
        ).
  Proof.
    intros; subst; inversion_by computes_to_inv; subst; trivial. 
  Qed.
  
  Definition NonNil {A: Type} (l: list A) :=
    match l with
      | [] => false
      | _  => true
    end.

  Definition dec2bool {A: Type} {P: A -> Prop} (pred: forall (a: A), sumbool (P a) (~ (P a))) :=
    fun (a: A) => 
      match pred a with
        | left _  => true
        | right _ => false
      end.

  Definition box {A: Type} (x: A) := [x].

  Lemma add_filter_nonnil_under_app :
    forall {A: Type} (seq: list (list A)),
      fold_right (app (A := A)) [] seq = 
      fold_right (app (A := A)) [] (List.filter NonNil seq).
  Proof.
    intros; induction seq; simpl; 
    [ | destruct a; simpl; rewrite IHseq]; 
    trivial.
  Qed.

  (*
  Lemma filter_nonnil_plus_where_is_just_filter :
    forall {A B: Type} {P: A -> Prop} (seq: list A),
    forall (pred: forall (a: A), sumbool (P a) (~ (P a))) (extraction: A -> B),
      List.filter NonNil (map (fun p => 
                                 Where (pred p) 
                                       [extraction p]) seq) =
      map box
          (map extraction (List.filter (dec2bool pred) seq)).
    intros; induction seq; simpl;
    [ | unfold dec2bool; destruct (pred a); subst; rewrite IHseq];
    trivial.
  Qed.
*)
  Lemma box_plus_app_is_identity :
    forall {A: Type} (seq: list A),
      fold_right (app (A := A)) [] (map box seq) = seq. 
  Proof.
    intros A seq; induction seq; simpl; congruence.
  Qed.

  (* Note to self: Why do we use two different equivalence principles
     (SimpleDB_equivalence and indistinguishable)?

     Partial answer: SimpleDB_equivalence evaluates equivalence of
     representations, while indistinguishable is concerned with
     output; basically, SimpleDB_equivalence gives a property that
     mutators need to preserve, while observers assert it *)

  Ltac hone_observer name :=
    hone' observer name using _;
    [ intros ro newrep params eq_ro_rn; (* TODO: Why do we have ro and rn? *)
        subst ro; 
        apply refine_pick;

        intros v impl_computes_to_v;
        intros oldrep oldrep_equiv_newrep; 
        constructor;
      
        generalize impl_computes_to_v;
        clear impl_computes_to_v
    | ].
  
  (*
  Lemma uh: forall (A: Type) (x v: A), ret x ↝ v <-> x = v.
  Proof.
    split; intros.
    inversion_by computes_to_inv.
    trivial.
    subst; constructor; trivial.
  Qed.
   *)

  Definition SameElements {A: Type} (ensemble: A -> Prop) (seq: list A) :=
    forall x, In _ ensemble x <-> List.In x seq.

  Lemma extraction :
    forall {A B: Type} (la: list A) (ens: A -> Prop) (lb: list B)  
           (cond_prop: A -> Prop) (cond: A -> bool) 
           (extraction: A -> B),
      (forall a, (cond_prop a <-> cond a = true)) -> 
      (SameElements ens la) -> 
      ((forall (b: B), List.In b lb <-> (exists a0, ens a0 ∧ cond_prop a0 ∧ extraction a0 = b)) <->
       (SetEq lb (map extraction (List.filter cond la)))).
  Proof.
    unfold SetEq, SameElements.

    intros.
    split; intros.
    rewrite in_map_iff.
    destruct (H1 x) as [H1' H1''].

    split; intros.

    specialize (H1' H2).
    destruct H1' as [a1 ?].
    eexists.
    rewrite filter_In, <- H.
    rewrite <- H0.
    instantiate (1 := a1); tauto.

    destruct H2 as [x' H2].
    rewrite filter_In, <- H in H2.
    apply H1''.
    exists x'.
    rewrite H0; tauto.


    rewrite H1.
    rewrite in_map_iff.
    split; intro HH; 
    destruct HH as [x HH];
    exists x;
    try rewrite filter_In in *;
    try rewrite H0, H in *;
    try rewrite <- H0 in *;
    tauto.
  Qed.

  Lemma extraction_id : 
    forall {A: Type} (la: list A) (ens: A -> Prop) (lb: list A)  
           (cond_prop: A -> Prop) (cond: A -> bool),
      (forall a, (cond_prop a <-> cond a = true)) -> 
      (SameElements ens la) ->
      ((forall (b : A), List.In b lb <-> ens b ∧ cond_prop b) <->
       (SetEq lb (List.filter cond la))).
  Proof.
    unfold SameElements.
    intros A la enq lb cond_prop cond H H0.
 
    pose proof (extraction la enq lb cond_prop cond (fun x => x) H H0).
    simpl in H1.

    Lemma map_id : 
      forall {A: Type} (seq: list A),
        (map (fun x => x) seq) = seq.
    Proof.
      intros A seq; induction seq; simpl; congruence.
    Qed.      

    rewrite map_id in H1.
    destruct H1 as [H1 H1'].

    split; intros HH;
    [ apply H1 | specialize (H1' HH) ].

    intros.
    specialize (HH b).
    rewrite HH.
    split; intros.
    exists b; intuition.
    destruct H2 as [a0 H2]; intuition; subst; tauto.

    unfold SetEq in HH.
    intros b; specialize (HH b).
    rewrite HH.
    
    rewrite filter_In, H, H0.
    intuition.
  Qed.

(*
  Lemma fold_seteq :
    forall {A: Type} (seq1 seq2: list A),
      SetEq seq1 seq2 <-> forall a, List.In a seq1 <-> List.In a seq2. 
    unfold SetEq; tauto.
  Qed.          
*)

  Ltac generalize_all :=
    repeat match goal with 
               [ H : _ |- _ ] => generalize H; clear H
           end.

  Ltac hone_observer' name :=
    hone' observer name using _;
    unfold refine; 
    intros; 
    [ instantiate (1 := eq);
      econstructor
    | 
    | unfold Query_For, Query_Where, 
      Query_In, Query_Return, qsHint, 
      In, qsSchemaHint;
      constructor;
      intros;
      constructor
    | ];
    repeat subst;
    [ | | | generalize_all | ];
    try solve [eauto].

  Ltac refine_eq_into_ret :=
    match goal with
      | [ H : _ _ _ ↝ _ |- ?eq _ _ ] => 
        generalize H; 
          clear H;
          apply (refine_eqA_into_ret _)

    end.    

  Lemma beq_process_true_iff : 
    forall { A: Type } (db_schema: Heading) (column: Attributes db_schema)
           { beq_A: Domain db_schema column -> Domain db_schema column -> bool },
    forall (beq_iff : forall a b, beq_A a b = true <-> a = b),
    forall value (p: Tuple db_schema),
      p!column = value <-> beq_A (p!column) value = true.
  Proof.
    intros ? ? ? ? beq_iff; split; apply beq_iff.
  Qed.  

  Definition beq_process_iff__state := beq_process_true_iff (A:=State) _ STATE beq_state_true_iff.

  Definition beq_process_iff__pid   := beq_process_true_iff (A:=nat) _ PID beq_nat_true_iff.

  (*
  Definition SimpleDB_enumerate (db: SimpleDB) (state: State) :=
    ret (List.map (fun (p: Process) => p!PID)
                  (List.filter (fun (p: Process) => beq_state state p!STATE)
                               db)).
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

    Check extraction.

    rewrite (extraction db _ _ _ (fun p => beq_state p!STATE state));
      eauto using beq_process_iff__state.

    refine_eq_into_ret;
      eexists.

    hone_observer' GET_CPU_TIME.

    intros db pid result computes set_db db_equiv.

    rewrite (extraction db _ _ _ (fun p => beq_nat p!PID pid));
      eauto using beq_process_iff__pid.

    refine_eq_into_ret;
      eexists.

    

    (*
    hone' observer ENUMERATE using SimpleDB_enumerate. 

    instantiate (1 := eq). 

    Focus 3.

    intros ro rn state equal; subst.
    unfold refine.
    intros v.

    intros.
    constructor.
    intros. 

    unfold SimpleDB_equivalence in *.
    constructor.

    unfold SimpleDB_enumerate in H.
    rewrite uh in H.
    subst.

    unfold In, Query_In, Query_Return, Query_Where, qsHint in *.

    intros; 
    rewrite in_map_iff;
    split; 
      intros H; 
      destruct H as [x H']; 
        exists x;  
        rewrite filter_In in *;
        intuition;
        [ rewrite H0         
        | rewrite <- beq_state_true_iff, beq_state_sym
        | rewrite <- H0
        | rewrite beq_state_sym, beq_state_true_iff ]; tauto.
     *)

    (* FIXME: the "Insert _into _" notation breaks the rename tactic *)

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
  
  (* TODO: Initialization? *)
  

  Lemma add_match : 
    forall (params: State),
    forall {B C: Type} 
           (f: State -> B)
           (g: B -> C),
      g (f (params)) = 
      g (State_rect (fun _ => B) (f Sleeping)
                    (f Running) params
        ).
  Proof.
    intro params; intros; destruct params; simpl; trivial.
  Qed.

  Add Parametric Morphism (A: Type) :
    (State_rect (fun _ => list A))
      with signature (@SetEq A ==> @SetEq A ==> pointwise_relation _ (@SetEq A))
        as rect_morphism.
  Proof.
    intros;
    unfold pointwise_relation, State_rect;
    intro state; destruct state; trivial.
  Qed.

  Open Scope type_scope.

  Definition TreeDB : Type := GenericTreeDB.t Process.
  Definition empty_tree_db : TreeDB := GenericTreeDB.empty Process.

  Definition NeatDB :=
    (TreeDB * TreeDB). 

  Definition AllSleeping seq :=
    List.filter (fun (x: Process) => beq_state x!STATE Sleeping) seq.

  Definition AllSleepingSet ensemble :=
    fun (p: Process) => ensemble p /\ p!STATE = Sleeping.

  Definition AllRunning seq :=
    List.filter (fun (x: Process) => beq_state x!STATE Running) seq.

  Definition AllRunningSet ensemble :=
    fun (p: Process) => ensemble p /\ p!STATE = Running.

  Definition KeyedOnPID (tree: TreeDB) :=
    forall (p: Process), 
      forall (a: nat), 
        GenericTreeDB.MapsTo a p tree ->
        a = p!PID.

  Definition NeatDB_equivalence old_rep (neat_db: NeatDB) :=
    let (sleeping, running) := neat_db in
    let set_db := GetRelation old_rep PROCESSES in
    SameElements (AllSleepingSet set_db) (GetValues sleeping) /\ 
    SameElements (AllRunningSet  set_db) (GetValues running ) /\
    KeyedOnPID sleeping /\ KeyedOnPID running.

  Lemma beqnat_dec2bool :
    forall n: nat,
      dec2bool (fun (p: Process) => eq_nat_dec n p!PID) =
      (fun (p: Process) => beq_nat n p!PID).
  Proof.
    unfold dec2bool; 
    intro n; 
    extensionality p.
    
    destruct (eq_nat_dec n (p!PID));
      symmetry;
      try rewrite beq_nat_true_iff;
      try rewrite beq_nat_false_iff;
      trivial.
  Qed.

  Definition Option2Box {A: Type} (xo: option A) :=
    match xo with
      | Some x => [x]
      | None   => []
    end.

  Print GenericTreeDB.
  Print TreeDB.

  Lemma filter_on_key :
    forall (tree: TreeDB) (equality: forall x y, {x = y} + {x <> y}), 
    forall (key: nat),
      KeyedOnPID tree -> 
      SetEq
        (List.filter
           (dec2bool (fun (p: Process) => equality key (p!PID)))
           (GetValues tree))
        (Option2Box 
           (GenericTreeDB.find key tree)).
  Proof.
    unfold KeyedOnPID.
    unfold SetEq, GetValues.
    intros; intuition.
    SearchAbout GenericTreeDB.find GenericTreeDB.MapsTo.

    Lemma or_false :
      forall (P: Prop), P \/ False <-> P.
    Proof.
      tauto.
    Qed.

    Lemma InOption2Box :
      forall {A: Type} (xo: option A) (x: A),
        List.In x (Option2Box xo) <-> xo = Some x. 
    Proof.
      intros A xo x; destruct xo; simpl; try rewrite or_false; intuition; congruence.
    Qed.          

    rewrite InOption2Box.
    rewrite filter_In in *.
    rewrite in_map_iff in *.
    destruct H0 as ([x0 (_snd, in_seq)], _fst).
    unfold dec2bool in *.

    rewrite <- find_mapsto_iff.
    destruct x0.
    subst; simpl in *.
    apply in_elements_mapsto in in_seq.

    specialize (H t k in_seq).

    destruct (equality key (t!PID)); try discriminate.
    subst; trivial.

    (****)

    
    rewrite InOption2Box in H0.
    rewrite filter_In in *.
    unfold dec2bool in *.
    rewrite <- find_mapsto_iff in H0.
    pose proof H0 as H2.
    rewrite elements_mapsto_iff in H0.
    apply InA_In_snd in H0.
    intuition.
    
    specialize (H x key H2).
    
    destruct (equality key (x!PID)); intuition.
  Qed.

  Add Parametric Morphism {A: Type} (x: A) :
    (List.In x)
      with signature (@SetEq A ==> iff)
        as in_morphism.
  Proof.
    intros s1 s2;
    unfold SetEq;
    intros;
    eauto.
  Qed.

  Definition SetUnion {A: Type} (x y: list A) := (x ++ y)%list.
  
  Lemma union_left : 
    forall {A: Type} (x: A) (seq1 seq2: list A),
      SetEq (SetUnion (x::seq1) seq2) (x :: (SetUnion seq1 seq2)).
  Proof.
    intros; unfold SetEq, SetUnion; intuition.
  Qed.
  
  Lemma union_right : 
    forall {A: Type} (x: A) (seq1 seq2: list A),
      SetEq (SetUnion seq1 (x::seq2)) (x :: (SetUnion seq1 seq2)).
  Proof.
    intros; unfold SetEq, SetUnion; intuition;
    repeat (rewrite in_app_iff in *; simpl in *);
    intuition.
  Qed.

  Lemma filter_union :
    forall {A: Type} (seq1 seq2: list A),
    forall (pred: A -> bool), 
      SetEq (List.filter pred (SetUnion seq1 seq2))
            (SetUnion (List.filter pred seq1) (List.filter pred seq2)).
  Proof.
    unfold SetEq, SetUnion;
    split;
    intros;
    rewrite filter_In, in_app_iff in *;
    rewrite ! filter_In in *;
    tauto.
  Qed.

  Lemma SetEq_append : 
    forall {A: Type} (seq1 seq2: list A) (x: A),
      SetEq seq1 seq2 -> SetEq (x :: seq1) (x :: seq2).
  Proof.
    intros A s1 s2 x s_eq; 
    unfold SetEq; 
    split; intro H;
    simpl in *;
    [rewrite s_eq in H | rewrite <- s_eq in H]; 
    intuition.
  Qed.  

  Add Parametric Morphism {A: Type} : (@SetUnion A) 
      with signature (@SetEq A ==> @SetEq A ==> @SetEq A)
        as union_morphism.
  Proof.
    unfold SetEq, SetUnion;
    intros;
    rewrite ! in_app_iff;
    intuition;
    repeat match goal with 
             | [ H: List.In ?x _, H': forall _, _ |- _ ] => try specialize (H' x)
           end;
    tauto.
  Qed.

  Lemma filter_comm :
    forall {A: Type} (pred1 pred2: A -> bool), 
    forall (seq: list A),
      List.filter pred1 (List.filter pred2 seq) =
      List.filter pred2 (List.filter pred1 seq).
  Proof.
    intros A pred1 pred2 seq; 
    induction seq as [ | hd tl];
    [ simpl 
    | destruct (pred1 hd) eqn:eq1; 
      destruct (pred2 hd) eqn:eq2; 
      repeat progress (simpl; 
                       try rewrite eq1; 
                       try rewrite eq2)
    ]; congruence.
  Qed.

  Lemma partition : 
    forall seq, 
      SetEq (SetUnion (AllRunning seq) (AllSleeping seq)) seq.
  Proof.
    intro seq; induction seq as [ | p seq']; simpl.
    reflexivity.
    unfold beq_state; destruct p!STATE.

    (* TODO: Why doesn't the eauto call work here *)
    rewrite union_right; eauto using SetEq_append.
    eauto using union_right, union_left, SetEq_append. 
  Qed.

  Lemma partition_set : 
    forall ens x,
      (fun x => AllRunningSet ens x \/ AllSleepingSet ens x) x <-> ens x.
  Proof.
    unfold AllRunningSet, AllSleepingSet; 
    intros ens x;
    destruct (x!STATE);
      tauto.
  Qed.

  Lemma SetUnion_Or : 
    forall {A: Type} 
           {ens1 ens2: A -> Prop}
           {seq1 seq2: list A},
      SameElements ens1 seq1 ->
      SameElements ens2 seq2 ->
      SameElements (fun x => ens1 x \/ ens2 x) (SetUnion seq1 seq2).
  Proof.
    unfold SameElements, SetUnion, In;
    intros A ens1 ens2 seq1 seq2 eq1 eq2 x;
    specialize (eq1 x);
    specialize (eq2 x);
    rewrite in_app_iff;
    tauto.
  Qed.      

  Lemma equiv_SameElements:
    forall {A: Type} {seq ens1 ens2},
      (forall (x: A), ens1 x <-> ens2 x) ->
      SameElements ens1 seq ->
      SameElements ens2 seq.
  Proof.
    intros A ? ? ? equiv;
    unfold SameElements;
    intros same_1 x; 
    specialize (equiv x); 
    specialize (same_1 x); 
    intuition.
  Qed.
  
  Lemma NeatScheduler :
    Sharpened ProcessSchedulerSpec.
  Proof.
    hone representation' using NeatDB_equivalence.
 
    hone_observer' ENUMERATE.
 
    intros db state result computes set_db db_equiv.

    destruct db as (sleeping, running);
      unfold NeatDB_equivalence in db_equiv;
      destruct db_equiv as (sleeping_correct, (running_correct, (sleeping_keys, running_keys))).

    pose proof (equiv_SameElements 
                  (partition_set (GetRelation set_db PROCESSES))
                  (SetUnion_Or running_correct sleeping_correct)).
    
    set (full_db := SetUnion (GetValues running) (GetValues sleeping)).

    unfold SameElements, In, AllRunningSet, AllSleepingSet in sleeping_correct, running_correct. 
    symmetry in sleeping_correct, running_correct.

    rewrite (extraction_id (full_db) _ _ _ (fun p => beq_state p!STATE Running)) in running_correct;
      eauto using beq_process_iff__state.

    rewrite (extraction_id full_db _ _ _ (fun p => beq_state p!STATE Sleeping)) in sleeping_correct;
      eauto using beq_process_iff__state.

    rewrite (extraction (full_db) _ _ _ (fun p => beq_state p!STATE state));
      eauto using beq_process_iff__state.

    rewrite (add_match state (fun l => map _ _) (fun x => SetEq result x)).
    (* eta rule *)
    
    rewrite <- sleeping_correct, <- running_correct.

    rewrite <- !map_list_map_fmap.

    refine_eq_into_ret.
 
    instantiate (1 :=fun (db: TreeDB * TreeDB) (params: State) => 
              let (sleeping, running) := db in _);
      reflexivity.

    hone_observer' GET_CPU_TIME.


    intros db pid result computes set_db db_equiv.

    destruct db as (sleeping, running);
      unfold NeatDB_equivalence in db_equiv;
      destruct db_equiv as (sleeping_correct, (running_correct, (sleeping_keys, running_keys))).

    pose proof (equiv_SameElements 
                  (partition_set (GetRelation set_db PROCESSES))
                  (SetUnion_Or running_correct sleeping_correct)).
    
    set (full_db := SetUnion (GetValues running) (GetValues sleeping)).

    unfold SameElements, In, AllRunningSet, AllSleepingSet in sleeping_correct, running_correct. 
    symmetry in sleeping_correct, running_correct.

    rewrite (extraction_id (full_db) _ _ _ (fun p => beq_state p!STATE Running)) in running_correct;
      eauto using beq_process_iff__state.

    rewrite (extraction_id full_db _ _ _ (fun p => beq_state p!STATE Sleeping)) in sleeping_correct;
      eauto using beq_process_iff__state.

    rewrite (extraction (full_db) _ _ _ (fun p => beq_nat p!PID pid));
      eauto using beq_process_iff__pid.

    unfold full_db.
    rewrite filter_union.

    rewrite filter_on_key.
    repeat rewrite filter_on_key; 
      trivial.
    
    apply (refine_eqA_into_ret _).

    instantiate (1 := fun db params => let (sleeping, running) := db in ret _);
      reflexivity.

    $$
  Admitted.
End ProcessSchedulerExample.

