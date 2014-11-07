Require Import FiatToFacade.Compiler.Prerequisites.
Require Import Facade.FacadeADTs.
Require Import List.

Unset Implicit Arguments.

(* Inversion lemmas *)
(* TODO: This should be moved to DFacade, thus getting rid of function pointers *)

Lemma runsto_pop :
  forall hd tl (vseq thead: StringMap.key) env (st st': State FacadeADT) ppop,
    vseq <> thead ->
    st [vseq >> ADT (List (hd :: tl))] ->
    Word2Spec env ppop  = Some (Axiomatic List_pop) ->
    RunsTo env (Call thead ppop (vseq :: nil)) st st' ->
    StringMap.Equal st' (StringMap.add thead (SCA _ hd) (StringMap.add vseq (ADT (List tl)) st)).
Proof.
  intros * vseq_thead vseq_init ppop_is_pop runs_to.

  inversion_clear' runs_to; simpl in *; autoinj;
  [ | congruence].

  rewrite ppop_is_pop in *; autoinj;
  unfold List_pop in *; clear ppop_is_pop; simpl in *;
  autodestruct; subst;
  rewrite StringMapFacts.find_mapsto_iff in * |- ;
  unfold sel in *.

  subst_find; simpl in *; autoinj. (* TODO Make autoinj call simpl in * first *)

  destruct output; [congruence|].
  simpl in *; autoinj.
Qed.

Lemma runsto_is_empty :
  forall seq (vseq tis_empty: StringMap.key) env (st st': State FacadeADT) pis_empty,
    vseq <> tis_empty ->
    st [vseq >> ADT (List seq)] ->
    Word2Spec env pis_empty  = Some (Axiomatic List_empty) ->
    RunsTo env (Call tis_empty pis_empty (vseq :: nil)) st st' ->
    exists ret, 
      ((ret = SCAZero /\ seq <> nil) \/ (ret = SCAOne /\ seq = nil)) /\
      StringMap.Equal st' (StringMap.add tis_empty ret st).
Proof.
  intros * vseq_tis_empty vseq_init pis_empty_is_is_empty runs_to.

  inversion_clear' runs_to; simpl in *; autoinj;
  [ | congruence].

  rewrite pis_empty_is_is_empty in *; autoinj;
  unfold List_pop in *; clear pis_empty_is_is_empty; simpl in *;
  autodestruct; subst;
  rewrite StringMapFacts.find_mapsto_iff in * |-;
                                                unfold sel in *;
  subst_find; simpl in *; autoinj. (* TODO Make autoinj call simpl in * first *)

  destruct output; [congruence|].
  simpl in *; autoinj; simpl in *.

  eexists; split; eauto.
  etransitivity; try eassumption.
  rewrite (add_noop vseq_init).
  reflexivity.
Qed.

Lemma runsto_copy :
  forall seq (vseq vcopy: StringMap.key) env (st st': State FacadeADT) pcopy,
    st [vseq >> ADT (List seq)] ->
    Word2Spec env pcopy  = Some (Axiomatic List_copy) ->
    RunsTo env (Call vcopy pcopy (vseq :: nil)) st st' ->
    StringMap.Equal st' (StringMap.add vcopy (ADT (List seq)) (StringMap.add vseq (ADT (List seq)) st)).
Proof.
  intros * vseq_seq pcopy_is_copy runs_to.

  inversion_clear' runs_to; simpl in *; autoinj;
  [ | congruence].

  rewrite pcopy_is_copy in *; autoinj;
  unfold List_copy in *; clear pcopy_is_copy; simpl in *;
  autodestruct; subst;
  rewrite StringMapFacts.find_mapsto_iff in * |- ;
  unfold sel in *.

  subst_find; simpl in *; autoinj. (* TODO Make autoinj call simpl in * first *)

  destruct output; [congruence|].
  simpl in *; autoinj.
Qed.

Lemma runsto_delete :
  forall seq (vseq vret: StringMap.key) env (st st': State FacadeADT) pdelete,
    st [vseq >> ADT (List seq)] ->
    Word2Spec env pdelete  = Some (Axiomatic List_delete) ->
    RunsTo env (Call vret pdelete (vseq :: nil)) st st' ->
    StringMap.Equal st' (StringMap.add vret SCAZero (StringMap.remove vseq st)).
Proof.
  intros * vseq_seq pdelete_is_delete runs_to.

  inversion_clear' runs_to; simpl in *; autoinj;
  [ | congruence].

  rewrite pdelete_is_delete in *; autoinj;
  unfold List_copy in *; clear pdelete_is_delete; simpl in *;
  autodestruct; subst;
  rewrite StringMapFacts.find_mapsto_iff in * |- ;
  unfold sel in *.

  subst_find; simpl in *; autoinj. (* TODO Make autoinj call simpl in * first *)

  destruct output; [congruence|].
  simpl in *; autoinj.
Qed.

Lemma runsto_cons :
  forall seq head (vseq vhead vdiscard: StringMap.key) env (st st': State FacadeADT) pcons,
    st [vseq >> ADT (List seq)] ->
    st [vhead >> SCA _ head] ->
    Word2Spec env pcons  = Some (Axiomatic List_push) ->
    RunsTo env (Call vdiscard pcons (vseq :: vhead :: nil)) st st' ->
    StringMap.Equal st' (StringMap.add vdiscard (SCA _ 0) (StringMap.add vseq (ADT (List (head :: seq))) st)).
Proof.
  intros * vseq_seq vhead_head pcons_is_cons runs_to.

  inversion_clear' runs_to; simpl in *; autoinj;
  [ | congruence].

  rewrite pcons_is_cons in *; autoinj;
  unfold List_push in *; clear pcons_is_cons; simpl in *;
  autodestruct; subst;
  rewrite StringMapFacts.find_mapsto_iff in * |- ;
  unfold sel in *.

  subst_find; simpl in *; autoinj. (* TODO Make autoinj call simpl in * first *)

  destruct output; [congruence|].
  destruct output; [congruence|].
  simpl in *; autoinj.

  subst_find; simpl in *; autoinj.
Qed.


Lemma runsto_new :
  forall env st1 st2 w vpointer vret,
    Word2Spec env w = Some (Axiomatic List_new) ->
    st1[vpointer >> SCA _ w] ->
    RunsTo env (Call vret (Var vpointer) nil) st1 st2 ->
    StringMap.Equal st2 ([vret >adt> List nil]::st1).
Proof.
  intros;
  inversion_facade;
  simpl in *;
  autoinj;
  auto_mapsto_unique;
  autoinj; eq_transitive; autoinj; simpl in *;
  match goal with
    | [ H: 0 = List.length _ |- _ ] => rewrite length_0 in H
  end; destruct_pairs; subst;
  [assumption|discriminate].
Qed.                       

Lemma runsto_delete' :
  forall seq (vseq vret: StringMap.key) env (st st': State FacadeADT) vpointer w,
    st [vseq >> ADT (List seq)] ->
    st [vpointer >> SCA _ w] ->
    Word2Spec env w = Some (Axiomatic List_delete) ->
    RunsTo env (Call vret vpointer (vseq :: nil)) st st' ->
    StringMap.Equal st' (StringMap.add vret SCAZero (StringMap.remove vseq st)).
Proof.
  intros;
  inversion_facade;
  simpl in *;
  autoinj;
  auto_mapsto_unique;
  autoinj; eq_transitive; autoinj; simpl in *;
  autodestruct; autoinj; subst;
  unfold sel in *;
  subst_find; simpl in *; autoinj;
  try discriminate;
  destruct output; [congruence|];
  destruct output; autoinj.
Qed.


Lemma runsto_copy_var :
  forall seq (vseq vcopy: StringMap.key) env (st st': State FacadeADT) pcopy vpointer,
    st[vpointer >> SCA _ pcopy] ->
    st[vseq >> ADT (List seq)] ->
    Word2Spec env pcopy  = Some (Axiomatic List_copy) ->
    RunsTo env (Call vcopy (Var vpointer) (vseq :: nil)) st st' ->
    StringMap.Equal st' ([vcopy >adt> List seq]::[vseq >adt> List seq]::st).
Proof.
  intros;
  inversion_facade;
  simpl in *;
  autoinj; rewrite <- StringMapFacts.find_mapsto_iff in *;  (* TODO: Extend auto_mapsto_unique *)
    auto_mapsto_unique; intros; autoinj; eq_transitive; autoinj; simpl in *.

  autodestruct; subst. simpl in *.
  destruct output; try discriminate.
  destruct output; try discriminate.
  autoinj.

  unfold sel in *.
  simpl in H16.
  
  subst_find; simpl in *. autoinj.
  discriminate.
Qed.

Lemma runsto_cons_var :
  forall seq head (vseq vhead vdiscard: StringMap.key) env (st st': State FacadeADT) pcons vpointer,
    st[vpointer >> SCA _ pcons] ->
    st [vseq >> ADT (List seq)] ->
    st [vhead >> SCA _ head] ->
    Word2Spec env pcons = Some (Axiomatic List_push) ->
    RunsTo env (Call vdiscard (Var vpointer) (vseq :: vhead :: nil)) st st' ->
    StringMap.Equal st' (StringMap.add vdiscard (SCA _ 0) (StringMap.add vseq (ADT (List (head :: seq))) st)).
Proof.
  intros;
  inversion_facade;
  simpl in *;
  autoinj; rewrite <- StringMapFacts.find_mapsto_iff in *;  (* TODO: Extend auto_mapsto_unique *)
    auto_mapsto_unique; intros; autoinj; eq_transitive; autoinj; simpl in *.

  autodestruct; subst. simpl in *.
  destruct output; try discriminate.
  destruct output; try discriminate.
  autoinj.

  unfold sel in *.
  simpl in *.
  
  repeat (subst_find; simpl in *; autoinj).
  discriminate.
Qed.
