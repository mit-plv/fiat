Require Import
        Coq.Lists.List
        Coq.Sorting.Permutation
        Fiat.Computation
        Fiat.ADT
        Fiat.ADTRefinement
        Fiat.ADTNotation
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.Common.ilist2
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Common.List.ListFacts
        Fiat.QueryStructure.Specification.Operations.Query
        Fiat.QueryStructure.Specification.Operations.Insert
        Fiat.QueryStructure.Specification.Operations.Empty
        Fiat.QueryStructure.Specification.Operations.Delete
        Fiat.QueryStructure.Specification.Operations.Update
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Implementation.Operations.General.QueryRefinements
        Fiat.QueryStructure.Implementation.Operations.General.InsertRefinements
        Fiat.QueryStructure.Implementation.Operations.General.DeleteRefinements
        Fiat.QueryStructure.Implementation.Operations.General.QueryStructureRefinements
        Fiat.QueryStructure.Automation.Common
        Fiat.QueryStructure.Automation.General.QueryAutomation
        Fiat.QueryStructure.Automation.General.InsertAutomation
        Fiat.QueryStructure.Automation.General.DeleteAutomation
        Fiat.Narcissus.Examples.Guard.DropFields.
Import ListNotations.

        
Lemma change_refine_form {X1 X2 Y Z} :
  forall (cx: Comp (X1 * X2)) (cy: X1 * X2 -> Comp Y) (f: Y -> Comp Z),
    refine
      (x <- cx;
       y <- cy x;
       f y)
      (x0 <- (x <- cx;
              y <- cy x;
              ret (y, snd x));
       f (fst x0)).
Proof.
  intros.
  unfold refine; intros.
  computes_to_inv; subst.
  eauto.
Qed.


Definition UnIndexedEnsembleListEquivalence'
           (ElementType : Type)
           (ensemble : IndexedEnsemble)
           (l : list ElementType) :=
  sig (fun (l': list IndexedElement) =>
         map indexedElement l' = l /\
         (forall x : IndexedElement,
            In IndexedElement ensemble x <-> List.In x l') /\
         NoDup (map elementIndex l')).


Definition AllFinite {qs_schema} (r: UnConstrQueryStructure qs_schema) :=
  forall idx, {l: list RawTuple & UnIndexedEnsembleListEquivalence' _ (GetUnConstrRelation r idx) l}.

Definition FiniteTables_AbsR'
    {qs_schema}
    (r_o : UnConstrQueryStructure qs_schema)
    (r_n : { r_n: UnConstrQueryStructure qs_schema & AllFinite r_n }) :=
  r_o = projT1 r_n.

Open Scope list.
Lemma QSEmptyFinite {qs_schema}:
  forall idx, FiniteEnsemble (GetUnConstrRelation (DropQSConstraints (QSEmptySpec qs_schema)) idx).
Proof.
  intros. red. exists []. red. exists [].
  split.
  - reflexivity.
  - split.
    * split; intros.
      + cbn in H. red in H. red in H.
        change (Vector.map schemaRaw (QSschemaSchemas qs_schema))
          with (qschemaSchemas qs_schema) in H. rewrite <- ith_imap2 in H.
        remember (ith2 _ _) in *.
        change (numQSschemaSchemas qs_schema)
          with (numRawQSschemaSchemas (QueryStructureSchemaRaw qs_schema)) in Heqy.
        change (fun x => ?f x) with f in Heqy.

        rewrite (Build_EmptyRelation_IsEmpty qs_schema idx) in Heqy.
        subst y. cbn in H. inversion H.
      + inversion H.
    * constructor.
Qed.

Lemma QSEmptyIsFinite {qs_schema}: AllFinite (DropQSConstraints (QSEmptySpec qs_schema)).
Proof.
  unfold AllFinite. intros. exists []. exists [].
  split.
  - reflexivity.
  - split.
    * split; intros.
      + cbn in H. red in H. red in H.
        change (Vector.map schemaRaw (QSschemaSchemas qs_schema))
          with (qschemaSchemas qs_schema) in H. rewrite <- ith_imap2 in H.
        remember (ith2 _ _) in *.
        change (numQSschemaSchemas qs_schema)
          with (numRawQSschemaSchemas (QueryStructureSchemaRaw qs_schema)) in Heqy.
        change (fun x => ?f x) with f in Heqy.

        rewrite (Build_EmptyRelation_IsEmpty qs_schema idx) in Heqy.
        subst y. cbn in H. inversion H.
      + inversion H.
    * constructor.
Qed.
Close Scope list.

Lemma FiniteTables_AbsR'_QSEmptySpec
      {qs_schema}
  :  FiniteTables_AbsR'
       (DropQSConstraints (QSEmptySpec qs_schema))
       (existT AllFinite (DropQSConstraints (QSEmptySpec qs_schema)) QSEmptyIsFinite).
Proof. reflexivity. Qed.

Definition IncrMaxFreshIdx {qs_schema idx} (r: sigT (@AllFinite qs_schema)) :=
  S (fold_right (fun elem acc => max (elementIndex elem) acc) 0 (proj1_sig (projT2 ((projT2 r) idx)))).

Lemma IncrMaxFreshIdx_Prop:
  forall {qs_schema idx} (r: sigT (@AllFinite qs_schema)),
    UnConstrFreshIdx (GetUnConstrRelation (projT1 r) idx)
                     (@IncrMaxFreshIdx _ idx r).
Proof.
  intros qsc idx r. pose (proj2_sig (projT2 ((projT2 r) idx))) as Hl.
  destruct Hl as [Hmap [Heqv Hdup]]. intro elem; intros Helem.
  apply Heqv in Helem. unfold lt.
  apply le_n_S; apply fold_right_max_is_max; apply Helem.
Qed.

Lemma IncrMaxFreshIdx_Refine:
  forall {qs_schema} {qidx: Fin.t (numRawQSschemaSchemas qs_schema)} (r: sigT (@AllFinite qs_schema)),
    refine
      {idx: nat | UnConstrFreshIdx (GetUnConstrRelation (projT1 r) qidx) idx}
      (ret (@IncrMaxFreshIdx _ qidx r)).
Proof.
  intros qsc qidx r. apply refine_pick. intros.
  apply Return_inv in H. subst. apply IncrMaxFreshIdx_Prop.
Qed.

Open Scope list.
Lemma insert_finite_helper:
  forall (qs_schema : RawQueryStructureSchema)
         (r_n: { r_n: UnConstrQueryStructure qs_schema & AllFinite r_n })
         qidx tup,
    UnConstrFreshIdx (GetUnConstrRelation (projT1 r_n) qidx) (elementIndex tup) ->
    AllFinite (UpdateUnConstrRelation (projT1 r_n) qidx
                 (EnsembleInsert tup (GetUnConstrRelation (projT1 r_n) qidx))).
Proof.
  red; intros qsc r_n idx tup Hfresh idx'. destruct (Fin.eqb idx idx') eqn:idxeq.
  - apply Fin.eqb_eq in idxeq. subst idx'.
    destruct r_n as [r Hfin]. destruct (Hfin idx) as [l1 Hl1].
    destruct Hl1 as [l2 [Hmap [Hin Hdup]]].
    exists ((indexedElement tup) :: l1). cbn.
    rewrite get_update_unconstr_eq. red. exists (tup :: l2).
    
    split. simpl. rewrite <- Hmap. reflexivity. split.
    split; intros H; unfold EnsembleInsert, In in *;
      destruct H; simpl;
        [ left; symmetry; assumption
        | right; apply (Hin x); apply H
        | left; symmetry; assumption
        | right; apply (Hin x); apply H].
    
    simpl. apply NoDup_cons. red in Hfresh. simpl in Hfresh.
    assert (Hlist: forall (x: nat) l,
               (forall x', List.In x' l -> lt x' x) ->
               ~List.In x l).
    {
      intros x l Hx'. intro Hx. apply (Hx' x) in Hx.
      apply lt_irrefl in Hx. inversion Hx.
    }
    apply Hlist. apply forall_In_map. intros elem Helem.
    apply Hfresh. apply (Hin elem).
    assumption. assumption.
    
  - assert (Hidxeq: idx <> idx').
    { intro. apply Fin.eqb_eq in H. congruence. }
    destruct r_n as [r Hfin]. destruct (Hfin idx') as [l1 Hl1].
    exists l1. cbn. rewrite get_update_unconstr_neq.
    assumption. assumption.
Qed.

Lemma FiniteTables_AbsR'_Insert :
  forall (qs_schema : RawQueryStructureSchema) r_n
         (idx : Fin.t (numRawQSschemaSchemas qs_schema)) tup
         (H: UnConstrFreshIdx (GetUnConstrRelation (projT1 r_n) idx) (elementIndex tup)),
    refine
      {r_n0 : { r_n: UnConstrQueryStructure qs_schema & AllFinite r_n } |
       FiniteTables_AbsR'
         (UpdateUnConstrRelation (projT1 r_n) idx (EnsembleInsert tup (GetUnConstrRelation (projT1 r_n) idx))) r_n0}
      (ret (existT AllFinite
              (UpdateUnConstrRelation (projT1 r_n) idx
                 (EnsembleInsert tup (GetUnConstrRelation (projT1 r_n) idx)))
              (insert_finite_helper _ r_n idx tup H))).
Proof.
  intros qsc r_n idx tup Hfreshn.
  unfold refine; intros r_n' Hr_n'. apply Return_inv in Hr_n'. subst r_n'.
  computes_to_econstructor. red; cbn. reflexivity.
Qed.


Lemma simpl_in_bind:
  forall (T U: Type) (x v : T) (y: U),
    In T (`(r', _) <- ret (x, y); ret r') v -> x = v.
Proof.
  intros. apply Bind_inv in H. destruct H. destruct H. apply Return_inv in H. rewrite <- H in H0. simpl in H0. apply Return_inv in H0. assumption. Qed.

Definition UnConstrQuery_In {ResultT}
           {qsSchema}
           (qs : UnConstrQueryStructure qsSchema)
           (R : Fin.t _)
           (bod : RawTuple -> Comp (list ResultT))
  := QueryResultComp (GetUnConstrRelation qs R) bod.

Notation "( x 'in' r '%' Ridx ) bod" :=
  (let qs_schema : QueryStructureSchema := _ in
   let r' : UnConstrQueryStructure qs_schema := r in
   let Ridx' := ibound (indexb (@Build_BoundedIndex _ _ (QSschemaNames qs_schema) Ridx%string _)) in
   @UnConstrQuery_In _ qs_schema r' Ridx'
            (fun x : @RawTuple (GetNRelSchemaHeading (qschemaSchemas qs_schema) Ridx') => bod)) (at level 0, x at level 200, r at level 0, bod at level 0).

Lemma permutation_length {A: Type}:
  forall (l1 l2 : list A),
    Permutation l1 l2 -> Datatypes.length l1 = Datatypes.length l2.
Proof.
  intros. induction H; simpl; congruence.
Qed.

Lemma fold_comp_list_in:
  forall (T: Type) (P: T -> bool) (ltup: list T) l inp,
    fold_right
      (fun b a : Comp (list ()) =>
         l <- b;
         l' <- a;
         ret (l ++ l')%list) (ret [])
      (map
         (fun t : T =>
            {l : list () |
             (P t -> ret [()] ↝ l) /\ (~ P t -> l = [])}) ltup) l ->
    List.In inp ltup ->
    P inp ->
    0 <? Datatypes.length l.
Proof.
  intros T P. induction ltup.
  - intros; auto.
  - intros l inp Hf Hin Hp. cbn in Hf.  destruct Hf as [x [Hx [y [Hy Happ]]]].
    unfold In in *. inversion Happ. destruct Hin as [Hin | Hin].
    * subst inp. inversion Hx. apply H0 in Hp. inversion Hp. auto.
    * pose proof (IHltup y inp Hy Hin Hp) as Hind. rewrite app_length.
      apply Nat.ltb_lt; apply Nat.lt_lt_add_l; apply Nat.ltb_lt; assumption.
Qed.

Lemma fold_comp_list_length:
  forall l l',
    fold_right
      (fun b a : Comp (list ()) =>
         l <- b;
         l' <- a;
         ret (l ++ l')%list) (ret [])
      l' l ->
    0 <? Datatypes.length l ->
    exists lin, List.In lin l' /\
                (exists lin', lin lin' /\ 0 <? Datatypes.length lin').
Proof.
  intros l l'. generalize dependent l. induction l'.
  - simpl. intros. inversion H. subst l. inversion H0.
  - simpl. intros. destruct H as [l1 [Hl1 Hl]]. red in Hl1. red in Hl.
    destruct Hl as [l2 [Hl2 Hl]]. red in Hl2. red in Hl. inversion Hl.
    destruct (0 <? Datatypes.length l2) eqn:Hlen2.
    * pose proof (IHl' l2 Hl2 Hlen2) as IH.
      destruct IH as [lin [Hlin1 Hlin2]]. exists lin. split.
      right; assumption. assumption.
    * apply Nat.ltb_ge in Hlen2. inversion Hlen2. rewrite <- H in H0.
      rewrite app_length in H0. rewrite H2 in H0. rewrite Nat.add_0_r in H0.
      exists a. split.
      left; reflexivity. exists l1. split. assumption. rewrite H2. apply H0.
Qed.
Close Scope list.

Lemma count_zero_iff:
  forall h (topkt: @Tuple h -> input) totup
    (r: UnConstrQueryStructure (PacketHistorySchema h))
    (P: input -> bool) count,
    (forall t, totup (topkt t) = t) ->
    (forall inp, P inp = P (topkt (totup inp))) ->
    computes_to (Count (For (UnConstrQuery_In r Fin.F1
                        (fun t =>
                          Where (P (topkt t))
                          Return ())))) count ->
    ((0 <? count) <-> (exists inp, In_History totup r inp /\ P inp)).
Proof.
  Transparent Query_For. Transparent Count. Transparent QueryResultComp.
  unfold Count, Query_For, Query_Where, Query_Return, UnConstrQuery_In.
  unfold QueryResultComp, FlattenCompList.flatten_CompList.
  intros h topkt totup r P count toinv Ptoinv Hcount.
  destruct Hcount as [l [Hcount Htmp]].
  unfold In in *. inversion Htmp. rename H into Hlen. clear Htmp.
  destruct Hcount as [l' [Htmp Hperm]]. apply Pick_inv in Hperm.
  unfold In in *. destruct Htmp as [ltup [Hrel Hfold]].
  apply Pick_inv in Hrel. unfold In in *.
  pose proof (permutation_length l' l Hperm) as Hpermlen.
  rewrite <- Hpermlen in *. clear Hperm. clear Hpermlen. clear l.
  split; intros H.
  - pose proof (fold_comp_list_length l' _ Hfold H) as Hlin0.
    destruct Hlin0 as [lin [Hlinm [lin' [Hll Hlinc]]]].
    apply in_map_iff in Hlinm. destruct Hlinm as [x [Hpx Hlx]].
    exists (topkt x). split.
    * red in Hrel. destruct Hrel as [l [Hmap [Heql Hdup]]].
      red. rewrite <- Hmap in Hlx.
      apply in_map_iff in Hlx.
      destruct Hlx as [y [Hy1 Hy2]]. destruct y as [yidx yelem].
      exists yidx. simpl in Hy1. subst x. apply Heql. rewrite toinv. apply Hy2.
    * subst lin. inversion Hll.
      destruct (P (topkt x)) eqn:Hpx. reflexivity.
      assert (Hle: lin' = []%list) by (apply H1; congruence). subst lin'.
      inversion Hlinc.

  - red in Hrel. destruct Hrel as [l [Hmap [Heql Hdup]]].
    destruct H as [inp [Hinp Hpinp]]. red in Hinp. destruct Hinp as [idx Hinp].
    apply Heql in Hinp.
    assert (Hinp': List.In (totup inp) ltup).
    { rewrite <- Hmap. apply in_map_iff.
      exists {| elementIndex := idx; indexedElement := (totup inp) |}.
      split. reflexivity. assumption. }
    pose (fun t => P (topkt t)) as P'. rewrite Ptoinv in Hpinp.
    apply (fold_comp_list_in _ P' ltup l' _ Hfold Hinp' Hpinp).
Qed.

Lemma list_helper:
  forall {T: Type} (l: list T) (f: T -> nat) (big: nat),
    lt (fold_right (fun e acc => max (f e) acc) 0 l) big ->
    ~ List.In big (map f l).
Proof.
  induction l.
  - auto.
  - unfold not; intros f big Hbig H. cbn in Hbig. cbn in H.
    pose proof
         (Nat.max_spec (f a)
                       (fold_right (fun (e : T) (acc : nat) =>
                                      Init.Nat.max (f e) acc) 0 l)) as Hmax.
    destruct Hmax as [[Hlt Hmax] | [Hlt Hmax]]; rewrite Hmax in Hbig;
      destruct H as [H | H].
    + subst big. pose proof (lt_trans _ _ _ Hlt Hbig).
      apply lt_irrefl in H. auto.
    + apply (IHl f big Hbig H).
    + subst big. apply lt_irrefl in Hbig. auto.
    + pose proof (le_lt_trans _ _ _ Hlt Hbig). apply (IHl f big H0 H).
Qed.

Lemma refine_pair: forall (T U: Type) (x: T) (y: U) (c: Comp T),
    refine c (ret x) ->
    refine
      (x' <- c;
         ret (x', y))
      (ret (x, y)).
Proof.
  intros. intro; intros. comp_inv. computes_to_econstructor.
  red in H. apply H. auto. auto. Qed.


Definition StatefulFilterSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : rep,
      Method "Filter" : rep * input -> rep * (option result)
    }.


Ltac prove_count_refine :=
  intros r inp;
  match goal with
  | [|- refine (?f1 _ _ _ _ _) (?f2 _ _ _ _ _)] => unfold f1, f2
  end;
  red; intros v H;
  repeat match goal with
  | [|- (If ?cond Then (ret _) Else _) ↝ _] =>
    destruct cond; [ assumption | ]; simpl
  | [H: (_ ↝ _) |- (with _ _, if historically _ then _ else _) ↝ _] =>
    inversion H as [c Hc]; destruct Hc as [Hcount Hres]; unfold In in *;
    pose 1 as Hcziff; clear Hcziff;
    unshelve epose proof (count_zero_iff _ _ _ _ _ c _ _ Hcount) as Hcziff;
    shelve_unifiable; cycle -1;
    [ computes_to_econstructor; computes_to_econstructor;
      [ instantiate (1:=(0 <? c)); red; destruct (0 <? c) eqn:Hzero; simpl;
        [ rewrite <- Hzero in Hcziff; apply Hcziff in Hzero;
          destruct Hzero as [pre [Hin Hcond]]; exists pre; split;
          [ apply Hin | apply Hcond ]
        | let H := fresh in
          intro H; rewrite <- Hzero in Hcziff; apply Hcziff in H; congruence ]
      | apply Hres ]
    | intros t; repeat (let i := fresh in destruct t as [i t]); reflexivity
    | reflexivity ]
  end.


Ltac drop_constraints_under_bind_insert :=
  unfold QSInsert;
  rewrite QSInsertSpec_UnConstr_refine; eauto; cycle 1;
    try (refine pick val true; [reflexivity | cbv; intros; exact I]);
    try (cbv -[refine]; intros; refine pick val true; try eauto);
    try (simplify with monad laws; higher_order_reflexivity).
  
Ltac drop_constraints_under_bind qs_schema bound_meth_tac :=
  hone representation using (@DropQSConstraints_AbsR qs_schema);
  repeat
    (match goal with
     | [H: constructorType _ _ |- _] =>
       apply Constructor_DropQSConstraints

     | [H: methodType _ _ _ |- _] =>
       simplify with monad laws; unfold Bind2;
       simplify with monad laws; cbn; etransitivity;
       [ eapply refine_bind;
         repeat
           (match goal with
            | [|- refine _ _] => reflexivity
            | [|- pointwise_relation _ refine _ _] =>
              intro a; etransitivity;
              [ apply change_refine_form
              | drop_constraints_under_bind_insert ]
            end)
       | etransitivity;
         [ eapply refine_bind;
           repeat
             (match goal with
              | [|- refine _ _] => bound_meth_tac
              | [|- pointwise_relation _ refine _ _] =>
                red; intros; higher_order_reflexivity
              end)
         | subst H; higher_order_reflexivity
         ]
       ]
     end).

Ltac hone_finite_under_bind_constructor :=
  match goal with
    [H: constructorType _ _ |- _] =>
    simplify with monad laws;
    refine pick val
      (existT _ (DropQSConstraints (QSEmptySpec _)) QSEmptyIsFinite);
    [ subst H; higher_order_reflexivity
    | apply FiniteTables_AbsR'_QSEmptySpec ]
  end.

Ltac hone_finite_under_bind_insert qs_schema idx :=
  match goal with
    [H': FiniteTables_AbsR' _ _ |- _] =>
    red; intros; red in H'; subst;
    rewrite (@IncrMaxFreshIdx_Refine qs_schema idx);
    simplify with monad laws; simpl;
    rewrite (@FiniteTables_AbsR'_Insert
               qs_schema _ idx
               ({| elementIndex := IncrMaxFreshIdx _;
                   indexedElement := icons2 _ inil2 |})
               (IncrMaxFreshIdx_Prop _));
    simplify with monad laws; higher_order_reflexivity
  end.

Ltac hone_finite_under_bind qs_schema idx :=
  hone representation using (@FiniteTables_AbsR' qs_schema);
  repeat
    (match goal with
     | [H: constructorType _ _ |- _] =>
       hone_finite_under_bind_constructor
         
     | [H: methodType _ _ _, H': FiniteTables_AbsR' _ _ |- _] =>
       simplify with monad laws; eapply refine_bind;
       repeat
         (match goal with
          | [|- refine _ _] =>
            red in H'; subst; higher_order_reflexivity
          | [|- pointwise_relation _ refine _ _] =>
            hone_finite_under_bind_insert qs_schema idx
          end)
   end).


(** Tactics for generating variants of filters **)

Ltac filter_gen gen :=
  red; intros h topkt totup r inp;
  let f := (eval unfold gen in @gen) in
  let f' := (eval cbv beta in (@f h _ In_History topkt totup r inp)) in
  apply f'.

Ltac filter_count filter :=
  red; intros h topkt totup r inp;
  pose (filter h topkt totup r inp) as f; unfold filter in f;
  repeat let f' := (eval unfold f in f) in
  match f' with
  | If ?cond Then (ret _) Else _ => destruct cond; [ apply f | ]; cbn in f
  | with ?r ?cont, if historically ?cond then ?iftru else ?iffal =>
    pose (c <- Count (For (t in r%"History")
                       Where (cond (topkt t))
                       Return ());
           If 0 <? c Then iftru Else iffal) as hist_count; apply hist_count
  end.