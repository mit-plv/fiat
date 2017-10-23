Require Import
        Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Lists.List.

Require Import
        Fiat.Common.SumType
        Fiat.Computation.ListComputations
        Fiat.QueryStructure.Automation.AutoDB
        Fiat.Examples.DnsServer.Packet.

Require Import
        Bedrock.Word
        Bedrock.Memory.


Import Vectors.VectorDef.VectorNotations.

Local Open Scope vector_scope.

Section DecomposeEnumField.

  (* Define new heading. *)

  Definition BreakdownHeading
             {n}
             (attr : Fin.t (S n))
             (sch : Vector.t Type (S n))
  : (Vector.t Type n).
    revert sch; pattern n, attr; apply Fin.rectS.
    exact (fun n' v => Vector.tl v).
    exact (fun n' attr' rec v => Vector.cons _ (Vector.hd v) _ (rec (Vector.tl v))).
  Defined.

  Definition icons2'
             {A} {B}
             {n}
             {l : Vector.t A (S n)}
             (b : B (l[@Fin.F1]))
             (il : ilist2 (B := B) (Vector.tl l))
    : ilist2 (B := B) l.
    revert b il; pattern n, l; apply Vector.caseS;
      simpl; intros; exact {| prim_fst := b; prim_snd := il |}.
  Defined.

  Definition icons2''
             {A} {B}
             {n}
             {l : Vector.t A (S n)}
             (b : B (Vector.hd l))
             (il : ilist2 (B := B) (Vector.tl l))
    : ilist2 (B := B) l.
    revert b il; pattern n, l; apply Vector.caseS;
      simpl; intros; exact {| prim_fst := b; prim_snd := il |}.
  Defined.

  (* Define injection into original heading. *)
  Fixpoint Tuple_BreakdownHeading_inj
           {n}
           (attrIdx : Fin.t (S n))
           (heading : Vector.t Type (S n))
           (el : heading[@attrIdx])
           (tup : ilist2 (B := @id Type) (BreakdownHeading attrIdx heading))
           {struct attrIdx}
    : ilist2 (B := @id Type) heading.
    revert heading el tup; pattern n, attrIdx; apply Fin.rectS.
    - exact (fun n' heading el tup => icons2' el tup).
    - refine (fun n' attr' rec heading el tup =>
                icons2'' (ilist2_hd tup) (rec _ _ (ilist2_tl tup))).
      generalize attr' el; clear.
      pattern (S n'), heading; apply Vector.caseS; simpl.
      exact (fun _ _ _ _ el => el).
  Defined.

  Fixpoint Tuple_DecomposeHeading_proj
           {n}
           (attrIdx : Fin.t (S n))
           (heading : Vector.t Type (S n))
           (tup : ilist2 (B := @id Type) heading)
           {struct attrIdx}
    : ilist2 (B := @id Type) (BreakdownHeading attrIdx heading).
    revert heading tup; pattern n, attrIdx; apply Fin.rectS.
    - exact (fun n' heading tup => ilist2_tl' tup).
    - refine (fun n' attr' rec heading tup => icons2'' _ _).
      exact (ilist2_hd' tup).
      exact (rec _ (ilist2_tl' tup)).
  Defined.

  Definition DecomposeSchema'
             (heading : RawSchema)
             (attr : Fin.t (NumAttr (rawSchemaHeading heading)))
    : RawSchema :=
    match attr in Fin.t n' return Vector.t _ n' -> RawSchema with
    | Fin.F1 _ =>
      fun v => {| rawSchemaHeading :=
                    {| AttrList := BreakdownHeading Fin.F1 v |};
                  attrConstraints := None;
                  tupleConstraints := None |}
    | Fin.FS _ attr' =>
      fun v => {| rawSchemaHeading :=
                    {| AttrList := BreakdownHeading (Fin.FS attr') v |};
                  attrConstraints := None;
                  tupleConstraints := None |}
    end (AttrList (rawSchemaHeading heading)).

  Fixpoint BuildVector {A}
           (a : A)
           m
    : Vector.t A m :=
    match m with
    | 0 => Vector.nil _
    | S m' => Vector.cons _ a _ (BuildVector a m')
    end.

  Lemma BuildVector_nth {A}
        (a : A)
        m
    : forall idx, (BuildVector a m)[@idx] = a.
  Proof.
    induction idx; simpl; first [reflexivity | eassumption].
  Defined.

  Definition DecomposeSchema
             m
             (heading : RawSchema)
             (attr : Fin.t (NumAttr (rawSchemaHeading heading)))
    : Vector.t RawSchema m :=
    BuildVector (DecomposeSchema' heading attr) m.

  Definition DecomposeRawQueryStructureSchema
             m
             (raw_qs_schema : RawQueryStructureSchema)
             (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
    : RawQueryStructureSchema :=
    {| qschemaSchemas :=
         DecomposeSchema m (Vector.nth (qschemaSchemas raw_qs_schema) schemaIdx)
                         attrIdx;
       qschemaConstraints := [ ] |}.

  Definition Tuple_DecomposeRawQueryStructure_proj
             {m : nat}
             {qs_schema : RawQueryStructureSchema}
             (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
             (tup : ilist2 (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)))
    :  ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas (DecomposeRawQueryStructureSchema m qs_schema schemaIdx attrIdx)) (a_proj_index (GetAttributeRaw tup attrIdx)))).
    unfold DecomposeRawQueryStructureSchema in *; simpl in *.
    unfold GetNRelSchema, DecomposeSchema in *;
      simpl in *.
    rewrite BuildVector_nth.
    match goal with
    | [ |- context[DecomposeSchema' ?nthv _] ]
      => remember nthv as y eqn:H
    end.
    clear H qs_schema schemaIdx.
    destruct y as [ [? ?] ? ?]; simpl in *.
    destruct attrIdx.
    eapply Tuple_DecomposeHeading_proj; eassumption.
    eapply Tuple_DecomposeHeading_proj; eassumption.
  Defined.

  Definition Tuple_DecomposeRawQueryStructure_inj
             {m : nat}
             {qs_schema : RawQueryStructureSchema}
             (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (el : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
             (idx : Fin.t m)
             (tup : ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas (DecomposeRawQueryStructureSchema m qs_schema schemaIdx attrIdx)) idx)))
    : ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)).
    unfold DecomposeRawQueryStructureSchema in *; simpl in *.
    unfold GetNRelSchema, DecomposeSchema in *;
      simpl in *.
    rewrite BuildVector_nth in tup.
    match goal with
    | [ |- context[rawSchemaHeading ?nthv] ]
      => remember nthv as y eqn:H
    end.
    clear H qs_schema schemaIdx.
    destruct y as [ [? ?] ? ?]; simpl in *.
    destruct attrIdx.
    eapply Tuple_BreakdownHeading_inj; eassumption.
    eapply Tuple_BreakdownHeading_inj; eassumption.
  Defined.

  Definition DecomposeRawQueryStructureSchema_AbsR
             {m : nat}
             {qs_schema : RawQueryStructureSchema}
             (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (a_proj : Vector.nth _ attrIdx -> Fin.t m)
             (el : _ -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
             (r_o : UnConstrQueryStructure qs_schema)
             (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema m qs_schema schemaIdx attrIdx))
    : Prop :=
    (forall Ridx, Same_set _ (GetUnConstrRelation r_o Ridx)
                           (GetUnConstrRelation (fst r_n) Ridx))
    /\ (forall Ridx tup,
           In _ (GetUnConstrRelation (snd r_n) Ridx) tup
           ->  In _ (GetUnConstrRelation (fst r_n) schemaIdx)
                  {| elementIndex := elementIndex tup;
                     indexedElement := Tuple_DecomposeRawQueryStructure_inj _ _ (el Ridx) _ (indexedElement tup) |})
    /\ (forall tup,
           In _ (GetUnConstrRelation (fst r_n) schemaIdx) tup
           -> In _ (GetUnConstrRelation (snd r_n) (a_proj (GetAttributeRaw (indexedElement tup) attrIdx)))
                 {| elementIndex := elementIndex tup;
                    indexedElement := Tuple_DecomposeRawQueryStructure_proj _ _ _ (indexedElement tup) |})
    /\ (forall Ridx Ridx' tup tup' ,
           In _ (GetUnConstrRelation (snd r_n) Ridx) tup
           -> In _ (GetUnConstrRelation (snd r_n) Ridx') tup'
           -> Ridx <> Ridx'
           -> elementIndex tup <> elementIndex tup')
    /\ (forall Ridx tup,
           In IndexedElement (GetUnConstrRelation (snd r_n) Ridx) tup
           -> a_proj (GetAttributeRaw
                        (Tuple_DecomposeRawQueryStructure_inj schemaIdx attrIdx (el Ridx) Ridx (indexedElement tup)) attrIdx) = Ridx)
    /\ (forall Ridx, FiniteEnsemble (GetUnConstrRelation (snd r_n) Ridx)).

  Definition DecomposeRawQueryStructureSchema_AbsR'
             {m : nat}
             {qs_schema : QueryStructureSchema}
             (schemaIdx' : BoundedIndex (QSschemaNames qs_schema))
             (schemaIdx := ibound (indexb schemaIdx'))
             {attrIdx' : BoundedIndex (HeadingNames (QSGetNRelSchemaHeading (qs_schema) schemaIdx'))}
             (attrIdx := ibound (indexb attrIdx'))
             (attrIdx_inj : Fin.t _ -> Fin.t _)
             (a_proj : Vector.nth _ (attrIdx_inj attrIdx) -> Fin.t m)
             (el : _ -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) _)
             (r_o : UnConstrQueryStructure qs_schema)
             (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema m qs_schema schemaIdx (attrIdx_inj attrIdx)))
    : Prop :=
    DecomposeRawQueryStructureSchema_AbsR (qs_schema := qs_schema)
                                          schemaIdx (attrIdx_inj attrIdx)
                                          a_proj el r_o r_n.

  Definition DecomposeRawQueryStructureSchema_empty_AbsR
             {m : nat}
             {qs_schema : QueryStructureSchema}
    : forall (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             a_proj
             el,
      DecomposeRawQueryStructureSchema_AbsR
        schemaIdx attrIdx a_proj el
        (DropQSConstraints (QSEmptySpec qs_schema))
        (DropQSConstraints (QSEmptySpec qs_schema),
         imap2 (fun ns : RawSchema => rawRel (RelationSchema:=ns))
               (Build_EmptyRelations
                  (qschemaSchemas (DecomposeRawQueryStructureSchema m qs_schema schemaIdx attrIdx)))).
  Proof.
    intros.
    repeat split; simpl; intros; intuition.
    - unfold GetUnConstrRelation in H.
      rewrite <- ith_imap2,
      EmptyRefinements.ith_Bounded_BuildEmptyRelations in H.
      simpl in H; unfold IndexedEnsemble_In in H; destruct_ex;
        inversion H.
    - unfold GetUnConstrRelation, DropQSConstraints, QSEmptySpec in H.
      rewrite <- ith_imap2 in H.
      simpl in H.
      rewrite EmptyRefinements.ith_Bounded_BuildEmptyRelations in H.
      simpl in H; unfold IndexedEnsemble_In in H; destruct_ex;
        inversion H.
    - unfold UnConstrFreshIdx in *; intros.
      unfold GetUnConstrRelation, DropQSConstraints, QSEmptySpec in H0.
      rewrite <- ith_imap2 in H0.
      simpl in H0.
      rewrite EmptyRefinements.ith_Bounded_BuildEmptyRelations in H0.
      destruct H0.
    - unfold UnConstrFreshIdx in *; intros.
      unfold GetUnConstrRelation, DropQSConstraints, QSEmptySpec in H.
      rewrite <- ith_imap2 in H.
      simpl in H.
      rewrite EmptyRefinements.ith_Bounded_BuildEmptyRelations in H.
      destruct H.
    - unfold FiniteEnsemble; eexists nil.
      unfold GetUnConstrRelation, DropQSConstraints, QSEmptySpec.
      rewrite <- ith_imap2.
      rewrite EmptyRefinements.ith_Bounded_BuildEmptyRelations.
      apply  UnIndexedEnsembleListEquivalence_Empty_set.
  Qed.

  Definition DecomposeRawQueryStructureSchema_Insert_AbsR_neq
             {m : nat}
             {qs_schema : QueryStructureSchema}
    : forall (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             a_proj
             el
             r_o
             r_n,
      DecomposeRawQueryStructureSchema_AbsR (qs_schema := qs_schema)
                                            (m := m)
                                            schemaIdx attrIdx a_proj el r_o r_n
      ->
      forall Ridx tup,
        Ridx <> schemaIdx
        -> DecomposeRawQueryStructureSchema_AbsR
             schemaIdx attrIdx a_proj el
             (UpdateUnConstrRelation r_o Ridx (EnsembleInsert tup (GetUnConstrRelation r_o Ridx)))
             (UpdateUnConstrRelation (fst r_n) Ridx (EnsembleInsert tup (GetUnConstrRelation (fst r_n) Ridx)), snd r_n).
  Proof.
    repeat split; simpl; intros.
    - destruct (fin_eq_dec Ridx Ridx0); subst;
        unfold GetUnConstrRelation, UpdateUnConstrRelation.
      + rewrite !ith_replace2_Index_eq.
        unfold Included; intros.
        inversion H1; subst; intuition.
        * econstructor; eauto.
        * econstructor 2; eapply (proj1 H Ridx0); apply H2.
      + rewrite !ith_replace2_Index_neq; eauto.
        unfold Included; intros; eapply (proj1 H Ridx0); apply H1.
    - destruct (fin_eq_dec Ridx Ridx0); subst;
        unfold GetUnConstrRelation, UpdateUnConstrRelation.
      + rewrite !ith_replace2_Index_eq.
        unfold Included; intros.
        inversion H1; subst; intuition.
        * econstructor; eauto.
        * econstructor 2; eapply (proj1 H Ridx0); apply H2.
      + rewrite !ith_replace2_Index_neq; eauto.
        unfold Included; intros; eapply (proj1 H Ridx0); apply H1.
    - unfold GetUnConstrRelation, UpdateUnConstrRelation.
      rewrite !ith_replace2_Index_neq; eauto.
      eapply (proj2 H); eauto.
    - unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
      rewrite !ith_replace2_Index_neq in H1; eauto.
      eapply (proj2 H); eauto.
    - unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
      eapply H; eauto.
    - unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
      eapply H; eauto.
    - unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
      eapply H; eauto.
  Qed.

  Lemma Tuple_DecomposeRawQueryStructure_inj_inverse
        {m : nat}
        {qs_schema : RawQueryStructureSchema}
    : forall (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             a_proj
             el
             tup,
      Tuple_DecomposeRawQueryStructure_inj (qs_schema := qs_schema)
                                           (m := m)
                                           schemaIdx attrIdx
                                           (el (a_proj (GetAttributeRaw tup attrIdx)))
                                           (a_proj (GetAttributeRaw tup attrIdx))
                                           (Tuple_DecomposeRawQueryStructure_proj schemaIdx attrIdx a_proj
                                                                                  tup) = tup.
  Proof.
  Admitted.

  Lemma ith_replace2_Index_eq':
    forall (A : Type) (B : A -> Type) (m : nat) (n n' : Fin.t m) (As : t A m) (il : ilist2 As) (new_b : B As[@n'])
           (H : n' = n),
      ith2 (replace_Index2 As il n' new_b) n = @eq_rect _ _ (fun n => B As[@n]) new_b _ H.
  Proof.
    intros.
    subst; unfold eq_rect; apply ith_replace2_Index_eq.
  Qed.

  Definition DecomposeRawQueryStructureSchema_Insert_AbsR_eq
             {m : nat}
             {qs_schema : QueryStructureSchema}
    : forall (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             a_proj
             el
             r_o
             r_n,
      DecomposeRawQueryStructureSchema_AbsR (qs_schema := qs_schema)
                                            (m := m)
                                            schemaIdx attrIdx a_proj el
                                            r_o r_n
      ->
      forall tup,
        UnConstrFreshIdx (GetUnConstrRelation (fst r_n) schemaIdx) (elementIndex tup)
        -> DecomposeRawQueryStructureSchema_AbsR
             schemaIdx attrIdx a_proj el
             (UpdateUnConstrRelation r_o schemaIdx (EnsembleInsert tup (GetUnConstrRelation r_o schemaIdx)))
             (UpdateUnConstrRelation (fst r_n) schemaIdx (EnsembleInsert tup (GetUnConstrRelation (fst r_n) schemaIdx)),
              UpdateUnConstrRelation (snd r_n)
                                     (a_proj (GetAttributeRaw (indexedElement tup) attrIdx))
                                     (EnsembleInsert {| elementIndex := elementIndex tup;
                                                        indexedElement :=
                                                          Tuple_DecomposeRawQueryStructure_proj _ _ a_proj
                                                                                                (indexedElement tup) |} (GetUnConstrRelation (snd r_n) (a_proj (GetAttributeRaw (indexedElement tup) attrIdx))))).
  Proof.
    repeat split; simpl; intros.
    - destruct (fin_eq_dec schemaIdx Ridx); subst;
        unfold GetUnConstrRelation, UpdateUnConstrRelation.
      + rewrite !ith_replace2_Index_eq.
        unfold Included; intros.
        inversion H1; subst; intuition.
        * econstructor; eauto.
        * econstructor 2; eapply (proj1 H Ridx); apply H2.
      + rewrite !ith_replace2_Index_neq; eauto.
        unfold Included; intros; eapply (proj1 H Ridx); apply H1.
    - destruct (fin_eq_dec schemaIdx Ridx); subst;
        unfold GetUnConstrRelation, UpdateUnConstrRelation.
      + rewrite !ith_replace2_Index_eq.
        unfold Included; intros.
        inversion H1; subst; intuition.
        * econstructor; eauto.
        * econstructor 2; eapply (proj1 H Ridx); apply H2.
      + rewrite !ith_replace2_Index_neq; eauto.
        unfold Included; intros; eapply (proj1 H Ridx); apply H1.
    - unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
      + rewrite !ith_replace2_Index_eq in *.
        simpl in H1.
        destruct (fin_eq_dec
                    Ridx
                    (a_proj (GetAttributeRaw (indexedElement tup) attrIdx))); subst.
        rewrite !ith_replace2_Index_eq in H1.
        destruct H1 as [? | ?] .
        * destruct tup; subst; injections; simpl.
          econstructor; f_equal; simpl.
          erewrite <- Tuple_DecomposeRawQueryStructure_inj_inverse.
          reflexivity.
        * pose proof (proj1 (proj2 H) (a_proj (GetAttributeRaw (indexedElement tup) attrIdx)) tup0).
          apply H2 in H1.
          econstructor 2; eauto.
        * rewrite !ith_replace2_Index_neq in H1 by eauto.
          pose proof (proj1 (proj2 H) Ridx tup0 H1); eauto.
          econstructor 2; eauto.
    - unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
      + rewrite !ith_replace2_Index_eq in H1.
        destruct H1 as [? | ?]; subst.
        * try rewrite !ith_replace2_Index_eq.
          econstructor; econstructor; f_equal.
        * apply (proj1 (proj2 (proj2 H)) tup0) in H1.
          simpl in *.
          destruct tup0; destruct tup; simpl in *.
          clear r_o H.
          destruct (fin_eq_dec (a_proj (GetAttributeRaw indexedElement0 attrIdx))
                               (a_proj (GetAttributeRaw indexedElement attrIdx))
                   ); subst;
            [ | rewrite !ith_replace2_Index_neq; eauto].
          erewrite ith_replace2_Index_eq' with (H := e).
          revert H1; clear.
          match goal with
            |- _ -> In _ _ ?G => generalize G; clear
          end.
          revert e.
          generalize ( a_proj (GetAttributeRaw indexedElement attrIdx)).
          match goal with
            |- context[EnsembleInsert ?t _] =>
            generalize t;
              generalize (a_proj (GetAttributeRaw indexedElement0 attrIdx))
          end.
          clear.
          destruct e; simpl; intros.
          unfold EnsembleInsert; intuition.
    - unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
      destruct (fin_eq_dec
                  Ridx
                  (a_proj (GetAttributeRaw (indexedElement tup) attrIdx)));
        destruct (fin_eq_dec
                    Ridx'
                    (a_proj (GetAttributeRaw (indexedElement tup) attrIdx))); subst.
      + congruence.
      + rewrite ith_replace2_Index_eq in H1.
        rewrite ith_replace2_Index_neq in H2 by eauto.
        destruct H1 as [? | ?]; subst; simpl.
        * apply (proj1 (proj2 H)) in H2; apply H0 in H2; simpl in *; omega.
        * apply H; eauto.
      + rewrite ith_replace2_Index_neq in H1 by eauto.
        rewrite ith_replace2_Index_eq in H2.
        destruct H2 as [? | ?]; subst; simpl.
        * apply (proj1 (proj2 H)) in H1; apply H0 in H1; simpl in *; omega.
        * apply H; eauto.
      + rewrite ith_replace2_Index_neq in H1 by eauto.
        rewrite ith_replace2_Index_neq in H2 by eauto.
        apply H; eauto.
    - unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
      destruct (fin_eq_dec
                  Ridx
                  (a_proj (GetAttributeRaw (indexedElement tup) attrIdx))).
      + subst.
        rewrite ith_replace2_Index_eq in H1.
        destruct H1 as [? | ?]; subst; simpl.
        * repeat f_equal.
          erewrite <- Tuple_DecomposeRawQueryStructure_inj_inverse;
            reflexivity.
        * apply H; eauto.
      + rewrite ith_replace2_Index_neq in H1 by eauto.
        apply H; eauto.
    - unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
      destruct (fin_eq_dec
                  Ridx
                  (a_proj (GetAttributeRaw (indexedElement tup) attrIdx))).
      + subst; rewrite ith_replace2_Index_eq.
        apply FiniteEnsemble_Insert; eauto.
        * unfold UnConstrFreshIdx in *; simpl in *; intros.
          eapply (proj1 (proj2 H)) in H1; simpl in H1.
          apply H0 in H1.
          simpl in H1; eauto.
        * apply H.
      + rewrite ith_replace2_Index_neq by eauto.
        apply H.
  Qed.

  Corollary DecomposeRawQueryStructureSchema_UpdateUnConstrRelationInsertC_eq
             {m : nat}
             {qs_schema : QueryStructureSchema}
             {ResultT}
    : forall (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             a_proj
             el
             r_o
             r_n
             (k : UnConstrQueryStructure qs_schema -> Comp ResultT)
             (k' : _ -> Comp ResultT),
      DecomposeRawQueryStructureSchema_AbsR (qs_schema := qs_schema)
                                            (m := m)
                                            schemaIdx attrIdx a_proj el
                                            r_o r_n
      ->
      forall freshIdx tup,
        UnConstrFreshIdx (GetUnConstrRelation (fst r_n) schemaIdx) freshIdx
        -> (forall r_o' r_n',
               DecomposeRawQueryStructureSchema_AbsR
                 schemaIdx attrIdx a_proj el r_o' r_n'
               -> refine (k r_o') (k' r_n'))
        ->
        refine (r_o' <- UpdateUnConstrRelationInsertC r_o schemaIdx {| elementIndex := freshIdx; indexedElement := tup |};
                  k r_o')
               (r_n' <- UpdateUnConstrRelationInsertC (fst r_n) schemaIdx {| elementIndex := freshIdx; indexedElement := tup |};
                  r_n'' <- UpdateUnConstrRelationInsertC (snd r_n)
                        (a_proj (GetAttributeRaw tup attrIdx))
                        {| elementIndex := freshIdx;
                           indexedElement :=
                             Tuple_DecomposeRawQueryStructure_proj _ _ a_proj tup |} ;
                  k' (r_n', r_n'')).
  Proof.
    Local Transparent UpdateUnConstrRelationInsertC.
    unfold UpdateUnConstrRelationInsertC; intros.
    repeat rewrite refineEquiv_bind_unit.
    rewrite H1.
    reflexivity.
    simpl; eapply DecomposeRawQueryStructureSchema_Insert_AbsR_eq; eauto.
  Qed.

  Corollary DecomposeRawQueryStructureSchema_UpdateUnConstrRelationInsertC_neq
            {m : nat}
            {qs_schema : QueryStructureSchema}
            {ResultT}
    : forall (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             a_proj
             el
             r_o
             r_n
             (k : UnConstrQueryStructure qs_schema -> Comp ResultT)
             (k' : _ -> Comp ResultT),
      DecomposeRawQueryStructureSchema_AbsR (qs_schema := qs_schema)
                                            (m := m)
                                            schemaIdx attrIdx a_proj el
                                            r_o r_n
      ->
      forall Ridx freshIdx tup,
        Ridx <> schemaIdx
        -> UnConstrFreshIdx (GetUnConstrRelation (fst r_n) Ridx) freshIdx
        -> (forall r_o' r_n',
               DecomposeRawQueryStructureSchema_AbsR
                 schemaIdx attrIdx a_proj el r_o' r_n'
               -> refine (k r_o') (k' r_n'))
        ->
        refine (r_o' <- UpdateUnConstrRelationInsertC r_o Ridx {| elementIndex := freshIdx; indexedElement := tup |};
                  k r_o')
               (r_n' <- UpdateUnConstrRelationInsertC (fst r_n) Ridx {| elementIndex := freshIdx; indexedElement := tup |};
                  k' (r_n', snd r_n)).
  Proof.
    unfold UpdateUnConstrRelationInsertC; intros.
    repeat rewrite refineEquiv_bind_unit.
    rewrite H2.
    reflexivity.
    simpl; eapply DecomposeRawQueryStructureSchema_Insert_AbsR_neq; eauto.
  Qed.

  Lemma UnConstrFreshIdx_Same_Set_Equiv {ElementType} :
    forall (ensemble ensemble' : @IndexedEnsemble ElementType),
      Same_set _ ensemble ensemble'
      -> forall bound,
        UnConstrFreshIdx ensemble bound
        <-> UnConstrFreshIdx ensemble' bound.
  Proof.
    unfold Same_set, UnConstrFreshIdx; intros.
    intuition.
    - eapply H; eapply H1; eauto.
    - eapply H; eapply H0; eauto.
  Qed.

  Lemma refine_UnConstrFreshIdx_Same_Set_Equiv {ElementType} :
    forall (ensemble ensemble' : @IndexedEnsemble ElementType),
      Same_set _ ensemble ensemble'
      -> refine {idx : nat | UnConstrFreshIdx ensemble idx}
                {idx : nat | UnConstrFreshIdx ensemble' idx}.
  Proof.
    intros.
    unfold refine; intros; computes_to_inv; computes_to_econstructor.
    rewrite UnConstrFreshIdx_Same_Set_Equiv; eauto.
  Qed.

  Corollary refine_UnConstrFreshIdx_DecomposeRawQueryStructureSchema_AbsR_Equiv
            {m : nat}
            {qs_schema : RawQueryStructureSchema}
            (schemaIdx : Fin.t _)
            (attrIdx : Fin.t _)
            a_proj
            el
            (r_o : UnConstrQueryStructure qs_schema)
            (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema m qs_schema schemaIdx attrIdx))
    : DecomposeRawQueryStructureSchema_AbsR schemaIdx attrIdx a_proj el r_o r_n
      ->
      refine {idx : nat | UnConstrFreshIdx (GetUnConstrRelation r_o schemaIdx) idx}
             {idx : nat | UnConstrFreshIdx (GetUnConstrRelation (fst r_n) schemaIdx) idx}.
  Proof.
    unfold refine; intros; computes_to_inv; computes_to_econstructor.
    unfold UnConstrFreshIdx in *; intros.
    eapply H0.
    apply H; eauto.
  Qed.

  Fixpoint Iterate_Equiv_QueryResultComp
           m
           (heading : RawHeading)
           (headings : Fin.t m -> RawHeading)
           (Ensembles : forall (idx : Fin.t m),
               @IndexedEnsemble (@RawTuple (headings idx)))
           (inj_Tuple : forall (idx : Fin.t m),
               @RawTuple (headings idx)
               -> @RawTuple heading)
           {struct m}
    : Comp (list (@RawTuple heading)) :=
    match m return
          forall (headings : Fin.t m -> RawHeading),
            (forall (idx : Fin.t m),
                @IndexedEnsemble (@RawTuple (headings idx)))
            -> (forall (idx : Fin.t m),
                   @RawTuple (headings idx)
                   -> @RawTuple heading)
            -> Comp (list _)
    with
    | 0 => fun _ _ _ => (ret List.nil)
    | S m =>
      fun headings Ensembles inj_Tuple =>
        res <- QueryResultComp (Ensembles Fin.F1)
            (fun tup => ret [inj_Tuple Fin.F1 tup])%list;
          res' <- Iterate_Equiv_QueryResultComp heading
               (fun idx => headings (Fin.FS idx))
               (fun idx => Ensembles (Fin.FS idx))
               (fun idx tup => (inj_Tuple (Fin.FS idx) tup))
          ;
          ret (List.app res res')
    end headings Ensembles inj_Tuple.

  Local Transparent QueryResultComp.

  Lemma flatten_CompList_ret:
    forall (A B : Type) (f : A -> B) (l : list A),
      refine (ret (map f l))
             (FlattenCompList.flatten_CompList (map (fun a => ret [(f a)]) l))%list.
  Proof.
    induction l; simpl.
    - reflexivity.
    - setoid_rewrite <- IHl.
      repeat setoid_rewrite refineEquiv_bind_unit.
      simpl; reflexivity.
  Qed.

  Lemma refine_UnIndexedEnsembleListEquivalence_Iterate_Equiv_QueryResultComp
        m
        (heading : RawHeading)
        (headings : Fin.t m -> RawHeading)
        (Ensembles : forall (idx : Fin.t m),
            @IndexedEnsemble (@RawTuple (headings idx)))
        (inj_Tuple : forall (idx : Fin.t m),
            @RawTuple (headings idx)
            -> @RawTuple heading)

        (distinctIndexes : forall idx idx' tup tup',
            idx <> idx'
            -> Ensembles idx tup
            -> Ensembles idx' tup'
            -> elementIndex tup <> elementIndex tup')
    : refine
        {queriedList : list RawTuple |
         UnIndexedEnsembleListEquivalence
           (fun tup => exists idx tup',
                tup = {| elementIndex := elementIndex tup';
                         indexedElement := inj_Tuple idx (indexedElement tup') |}
                /\ In _ (Ensembles idx) tup')
           queriedList}
        (Iterate_Equiv_QueryResultComp heading headings Ensembles inj_Tuple).
  Proof.
    revert heading headings Ensembles inj_Tuple distinctIndexes.
    induction m; simpl; intros; intros ? ?.
    - computes_to_inv; subst; computes_to_econstructor.
      unfold UnIndexedEnsembleListEquivalence; eexists nil; simpl;
        intuition eauto.
      unfold In in H; destruct_ex; intuition subst.
      inversion x0.
      constructor.
    - unfold QueryResultComp in H.
      computes_to_inv; subst.
      eapply IHm in H'; computes_to_inv; clear IHm.
      apply flatten_CompList_ret in H'0; computes_to_inv; subst.
      computes_to_econstructor. unfold UnIndexedEnsembleListEquivalence in *;
                                  destruct_ex; intuition; subst.
      rewrite map_map.
      replace (fun x1 : IndexedElement => inj_Tuple Fin.F1 (indexedElement x1))
      with (fun x1 : IndexedElement => indexedElement {| elementIndex := elementIndex x1;
                                                         indexedElement := inj_Tuple Fin.F1 (indexedElement x1) |}) by
          (apply functional_extensionality; reflexivity).
      rewrite <- map_map.
      eexists (_ ++ _)%list.
      rewrite map_app; intuition eauto.
      + unfold In in *; destruct_ex; intuition subst.
        revert headings Ensembles inj_Tuple distinctIndexes x0 x H0 H4 H2 H5 x3 H3.
        pattern m, x2.
        eapply Fin.caseS; clear m x2; intros.
        * simpl in *; apply H0 in H3; apply in_or_app; left.
          eapply in_map with
          (f := (fun x1 : IndexedElement =>
                   {| elementIndex := elementIndex x1;
                      indexedElement := inj_Tuple Fin.F1 (indexedElement x1) |})) in H3.
          apply H3.
        * apply in_or_app; right.
          eapply H2; eexists _,_; intuition eauto.
      + apply in_app_or in H; unfold In in *; destruct_ex; intuition subst.
        * apply in_map_iff in H1; destruct_ex; intuition subst.
          eexists _, _; intuition eauto.
          eapply H0; eauto.
        * eapply H2 in H1.
          destruct_ex; intuition subst.
          eexists _, _; intuition eauto.
      + rewrite map_app.
        eapply NoDup_app_in_iff; intuition.
        revert H4; clear; induction x0; simpl; intros; econstructor;
          inversion H4; subst; eauto.
        intro; apply H1; revert H; clear; induction x0; simpl; intuition auto.
        rewrite map_map in H1.
        apply in_map_iff in H; apply in_map_iff in H1.
        destruct_ex; intuition; subst.
        eapply H2 in H6; eapply H0 in H7.
        destruct H6 as [? [? [? ?] ] ]; simpl in *; subst;
          simpl in *.
        eapply (distinctIndexes Fin.F1 (Fin.FS x1)); eauto.
        intros; discriminate.
      + intros; eapply distinctIndexes; eauto.
        intro; apply H0.
        apply Fin.FS_inj; eauto.
  Qed.

  Fixpoint Iterate_Equiv_QueryResultComp_body
           m
           {ResultT}
           (heading : RawHeading)
           (headings : Fin.t m -> RawHeading)
           (Ensembles : forall (idx : Fin.t m),
               @IndexedEnsemble (@RawTuple (headings idx)))
           (inj_Tuple : forall (idx : Fin.t m),
               @RawTuple (headings idx)
               -> @RawTuple heading)
           (body : @RawTuple heading -> Comp (list ResultT))
           {struct m}
    : Comp (list ResultT) :=
    match m return
          forall (headings : Fin.t m -> RawHeading),
            (forall (idx : Fin.t m),
                @IndexedEnsemble (@RawTuple (headings idx)))
            -> (forall (idx : Fin.t m),
                   @RawTuple (headings idx)
                   -> @RawTuple heading)
            -> Comp (list ResultT)
    with
    | 0 => fun _ _ _ => (ret List.nil)
    | S m =>
      fun headings Ensembles inj_Tuple =>
        res <- QueryResultComp (Ensembles Fin.F1)
            (fun tup => body (inj_Tuple Fin.F1 tup));
          res' <- Iterate_Equiv_QueryResultComp_body heading
               (fun idx => headings (Fin.FS idx))
               (fun idx => Ensembles (Fin.FS idx))
               (fun idx tup => (inj_Tuple (Fin.FS idx) tup))
               body
          ;
          ret (List.app res res')
    end headings Ensembles inj_Tuple.

  Lemma refine_Iterate_Equiv_QueryResultComp_body
        m
        {ResultT : Type}
        (heading : RawHeading)
        (headings : Fin.t m -> RawHeading)
        (Ensembles : forall (idx : Fin.t m),
            @IndexedEnsemble (@RawTuple (headings idx)))
        (inj_Tuple : forall (idx : Fin.t m),
            @RawTuple (headings idx)
            -> @RawTuple heading)
        (body : @RawTuple heading -> Comp (list ResultT))
    : refineEquiv
        (results <- Iterate_Equiv_QueryResultComp heading headings Ensembles inj_Tuple;
           FlattenCompList.flatten_CompList (map body results))
        (Iterate_Equiv_QueryResultComp_body heading headings Ensembles inj_Tuple body).
  Proof.
    split.
    - induction m; simpl.
      + simplify with monad laws.
        simpl; reflexivity.
      + simplify with monad laws.
        setoid_rewrite <- IHm.
        repeat setoid_rewrite refineEquiv_bind_bind.
        f_equiv; intro.
        rewrite refineEquiv_swap_bind.
        rewrite (refineEquiv_swap_bind
                   (FlattenCompList.flatten_CompList (map (fun tup : RawTuple => body (inj_Tuple Fin.F1 tup)) a))).
        f_equiv; intro.
        induction a; simpl; simplify with monad laws.
        * setoid_rewrite refineEquiv_bind_unit.
          simpl; setoid_rewrite refineEquiv_unit_bind.
          reflexivity.
        * repeat setoid_rewrite refineEquiv_bind_bind.
          simpl.
          rewrite refineEquiv_swap_bind.
          f_equiv; intro.
          rewrite <- refineEquiv_bind_bind, IHa.
          simplify with monad laws.
          setoid_rewrite refineEquiv_bind_unit.
          setoid_rewrite <- List.app_assoc.
          reflexivity.
    - induction m; simpl.
      + setoid_rewrite refineEquiv_bind_unit.
        simpl; reflexivity.
      + repeat setoid_rewrite refineEquiv_bind_bind.
        setoid_rewrite IHm.
        repeat setoid_rewrite refineEquiv_bind_bind.
        f_equiv; intro.
        rewrite refineEquiv_swap_bind.
        setoid_rewrite (refineEquiv_swap_bind
                          _
                          (Iterate_Equiv_QueryResultComp heading (fun idx : Fin.t m => headings (Fin.FS idx))
                                                         (fun idx : Fin.t m => Ensembles (Fin.FS idx))
                                                         (fun (idx : Fin.t m) (tup : RawTuple) => inj_Tuple (Fin.FS idx) tup))).
        setoid_rewrite refineEquiv_bind_unit.
        f_equiv; intro.
        revert a0.
        induction a; simpl; intros; simplify with monad laws.
        * setoid_rewrite refineEquiv_bind_unit.
          reflexivity.
        * repeat setoid_rewrite refineEquiv_bind_bind.
          repeat setoid_rewrite refineEquiv_bind_unit.
          setoid_rewrite map_app.
          simpl.
          rewrite <- (refineEquiv_swap_bind (body (inj_Tuple Fin.F1 a))).
          f_equiv; intro.
          setoid_rewrite map_app in IHa.
          setoid_rewrite <- refineEquiv_bind_bind; rewrite <- IHa.
          repeat setoid_rewrite refineEquiv_bind_bind.
          setoid_rewrite refineEquiv_bind_unit.
          setoid_rewrite <- List.app_assoc.
          f_equiv; intro.
  Qed.

  Lemma refine_UnIndexedEnsembleListEquivalence {A}
    : forall s s',
      (forall l, UnIndexedEnsembleListEquivalence s' l
                 -> UnIndexedEnsembleListEquivalence s l)
      -> refine {queriedList : list A | UnIndexedEnsembleListEquivalence s queriedList}
                {queriedList : list A | UnIndexedEnsembleListEquivalence s' queriedList}.
  Proof.
    intros ? ?; computes_to_inv; computes_to_econstructor.
    computes_to_inv.
    eauto.
  Qed.

  Lemma UnIndexedEnsembleListEquivalence_app {A} :
    forall (P Q : IndexedEnsemble) (l l' : list A),
      Disjoint _ (fun idx => exists tup,
                      In _ P {| elementIndex := idx;
                                indexedElement := tup |})
               (fun idx => exists tup,
                    In _ Q {| elementIndex := idx;
                              indexedElement := tup |})
      -> UnIndexedEnsembleListEquivalence P l
      -> UnIndexedEnsembleListEquivalence Q l'
      -> UnIndexedEnsembleListEquivalence (Union _ P Q) (l ++ l').
  Proof.
    unfold UnIndexedEnsembleListEquivalence; intros.
    destruct_ex; intuition.
    eexists (x0 ++ x)%list; intuition; eauto.
    - rewrite map_app; congruence.
    - apply in_or_app.
      setoid_rewrite <- H1; setoid_rewrite <- H3;
        destruct H4; intuition.
    - apply in_app_or in H4.
      setoid_rewrite <- H1 in H4; setoid_rewrite <- H3 in H4.
      intuition.
    - rewrite map_app; apply NoDup_app_in_iff; intuition.
      apply in_map_iff in H4; apply in_map_iff in H7;
        destruct_ex; intuition; subst.
      apply H1 in H10; apply H3 in H9.
      inversion H; subst.
      eapply (H0 (elementIndex x2)).
      destruct x3; destruct x2; subst; simpl in *.
      econstructor; unfold In.
      eexists; eauto.
      rewrite H4; eexists; eauto.
  Qed.

  Lemma refine_UnConstrQuery_In_DecomposeRawQueryStructureSchema_AbsR
        {m : nat}
        {qs_schema : RawQueryStructureSchema}
        {ResultT : Type}
        (schemaIdx : Fin.t _)
        (body : @RawTuple _ -> Comp (list ResultT))
        (attrIdx : Fin.t _)
        a_proj
        el
        (r_o : UnConstrQueryStructure qs_schema)
        (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema m qs_schema schemaIdx attrIdx))
    : DecomposeRawQueryStructureSchema_AbsR schemaIdx attrIdx a_proj el r_o r_n
      ->
      refine (UnConstrQuery_In r_o schemaIdx body) (UnConstrQuery_In (fst r_n) schemaIdx body).
  Proof.
    intros.
    unfold UnConstrQuery_In, QueryResultComp; f_equiv.
    rewrite refine_UnIndexedEnsembleListEquivalence.
    reflexivity.
    intros.
    eapply UnIndexedEnsembleListEquivalence_Same_set; eauto.
    destruct H.
    unfold Same_set in *; intuition eauto.
    apply H.
    apply H.
  Qed.

  Lemma refine_Iterate_Equiv_QueryResultComp
        {m : nat}
        {qs_schema : RawQueryStructureSchema}
        {ResultT : Type}
        (schemaIdx : Fin.t _)
        (body : @RawTuple _ -> Comp (list ResultT))
        (attrIdx : Fin.t _)
        a_proj
        el
        (r_o : UnConstrQueryStructure qs_schema)
        (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema m qs_schema schemaIdx attrIdx))
    : DecomposeRawQueryStructureSchema_AbsR schemaIdx attrIdx a_proj el r_o r_n
      ->
      refine (UnConstrQuery_In r_o schemaIdx body)
             (Iterate_Equiv_QueryResultComp_body
                _ _
                (GetUnConstrRelation (snd r_n))
                (fun idx => Tuple_DecomposeRawQueryStructure_inj _ _ (el idx) idx) body).
  Proof.
    intros.
    erewrite refine_UnConstrQuery_In_DecomposeRawQueryStructureSchema_AbsR by eassumption.
    rewrite <- refine_Iterate_Equiv_QueryResultComp_body.
    unfold UnConstrQuery_In, QueryResultComp; f_equiv.
    rewrite refine_UnIndexedEnsembleListEquivalence.
    - unfold DecomposeRawQueryStructureSchema; simpl.
      intros; rewrite <- refine_UnIndexedEnsembleListEquivalence_Iterate_Equiv_QueryResultComp.
      + reflexivity.
      + intros; destruct H as [? [? [? [? ?] ] ] ].
        intro; pose proof (H5 _ _ _ _ H1 H2 H0); simpl in *; eauto.
    - unfold UnIndexedEnsembleListEquivalence; simpl; intros.
      destruct_ex; intuition; subst.
      eexists x; intuition eauto.
      apply H in H1.
      apply H0.
      eexists _, _; split; eauto.
      simpl; destruct x0; simpl; f_equal.
      symmetry; apply Tuple_DecomposeRawQueryStructure_inj_inverse.
      unfold In in *; apply H0 in H1; destruct_ex; intuition; subst.
      apply (proj1 (proj2 H)) in H4; eassumption.
  Qed.

  Lemma refine_Iterate_Equiv_QueryResultComp_body_Where_False
        m
        {ResultT : Type}
        (heading : RawHeading)
        (headings : Fin.t m -> RawHeading)
        (Ensembles : forall (idx : Fin.t m),
            @IndexedEnsemble (@RawTuple (headings idx)))
        (inj_Tuple : forall (idx : Fin.t m),
            @RawTuple (headings idx)
            -> @RawTuple heading)
        (FiniteEnsembles : forall idx, FiniteEnsemble (Ensembles idx))
        (body : @RawTuple heading -> Comp (list ResultT))
        P
    :
      (forall idx tup, In _ (Ensembles idx) tup -> ~ P (inj_Tuple idx (indexedElement tup)))
      -> refine
        (Iterate_Equiv_QueryResultComp_body heading headings Ensembles inj_Tuple
                                            (fun tup : RawTuple => Where (P tup)
                                                                         (body tup) ))
                                            (ret nil).
  Proof.
    induction m; simpl; intros.
    - reflexivity.
    - rewrite refine_QueryResultComp_body_Where_False; eauto.
      simplify with monad laws.
      apply IHm; eauto.
  Qed.

  Lemma refine_flatten_CompList_func' :
    forall (A B : Type) (l : list A) (f f' : A -> Comp (list B)),
      (forall v, List.In v l -> refine (f v) (f' v))
      -> refine (FlattenCompList.flatten_CompList (map f l)) (FlattenCompList.flatten_CompList (map f' l)).
  Proof.
    induction l; simpl; intros.
    - reflexivity.
    - rewrite H by eauto.
      f_equiv; intro.
      rewrite IHl by eauto.
      reflexivity.
  Qed.

  Lemma refine_Iterate_Equiv_QueryResultComp_body_Where_And_eq
        m
        {ResultT : Type}
        (heading : RawHeading)
    : forall (headings : Fin.t m -> RawHeading)
        (Ensembles : forall (idx : Fin.t m),
            @IndexedEnsemble (@RawTuple (headings idx)))
        (inj_Tuple : forall (idx : Fin.t m),
            @RawTuple (headings idx)
            -> @RawTuple heading)
        (FiniteEnsembles : forall idx, FiniteEnsemble (Ensembles idx))
        (body : @RawTuple heading -> Comp (list ResultT))
        idx
        P Q,
      (forall idx',
          idx <> idx'
          -> forall tup,
            In _ (Ensembles idx') tup
            -> ~ (P (inj_Tuple _ (indexedElement tup))))
      -> (forall tup,
             In _ (Ensembles idx) tup
             -> P (inj_Tuple _ (indexedElement tup)))
      -> refine
           (Iterate_Equiv_QueryResultComp_body
              heading headings Ensembles inj_Tuple
              (fun tup => Where (P tup /\ Q tup)
                                (body tup)))
           (QueryResultComp (Ensembles idx)
                            (fun tup => Where (Q (inj_Tuple _ tup))
                                              (body (inj_Tuple idx tup)))).
  Proof.
      induction m; simpl; intros.
      - intros; inversion idx.
      - destruct (fin_eq_dec idx Fin.F1).
        + etransitivity.
          * apply refine_under_bind_both; intros.
            apply refine_under_bind; intros.
            eapply refine_flatten_CompList_func'.
            intros; rewrite (refine_Query_Where_Cond (Q := Q (inj_Tuple _ v))).
            finish honing.
            intros; computes_to_inv; unfold UnIndexedEnsembleListEquivalence in H1;
              destruct_ex; intuition; subst.
            apply in_map_iff in H2; destruct_ex; intuition; subst.
            apply H1 in H6; apply H0 in H6; intuition.
            rewrite e.
            rewrite refine_Iterate_Equiv_QueryResultComp_body_Where_False.
            simplify with monad laws;
              rewrite app_nil_r; finish honing.
            intuition eauto.
            unfold not; intros; eapply H; intuition eauto.
            rewrite e in H4; discriminate.
          * simplify with monad laws.
            unfold UnConstrQuery_In, QueryResultComp.
            rewrite e.
            reflexivity.
        + rewrite refine_QueryResultComp_body_Where_False.
          * simplify with monad laws.
            revert IHm headings Ensembles inj_Tuple FiniteEnsembles P H H0 n; pattern m, idx.
            apply Fin.caseS; simpl; intros.
            congruence.
            apply (IHm (fun n => headings (Fin.FS n))
                            (fun n => Ensembles (Fin.FS n))
                            (fun n tup => inj_Tuple (Fin.FS n) tup));
              intros; eauto.
            intro.
            eapply (H (Fin.FS idx')); eauto.
            intro; apply H1; apply Fin.FS_inj; eauto.
          * unfold not; intros.
            eapply H; intuition eauto.
          * apply FiniteEnsembles.
  Qed.

  Lemma refine_QueryIn_Where
        {m : nat}
        {qs_schema : RawQueryStructureSchema}
        (schemaIdx : Fin.t _)
        (attrIdx : Fin.t _)
        a_proj
        el
        (r_o : UnConstrQueryStructure qs_schema)
        (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema m qs_schema schemaIdx attrIdx))
        (r_o_r_n_AbsR : DecomposeRawQueryStructureSchema_AbsR schemaIdx attrIdx a_proj el r_o r_n)
        {ResultT : Type}
        (body : @RawTuple _ -> Comp (list ResultT))
        idx
        Q
    : refine (UnConstrQuery_In r_o schemaIdx
                               (fun tup => Where (a_proj (GetAttributeRaw tup attrIdx) = a_proj idx
                                                  /\ Q tup)
                                                 (body tup)))
             (UnConstrQuery_In (snd r_n) (a_proj idx) (fun tup =>
                                                         Where (Q (Tuple_DecomposeRawQueryStructure_inj _ _ (el (a_proj idx)) _ tup))
                                                               (body
                                                               (Tuple_DecomposeRawQueryStructure_inj _ _ (el (a_proj idx)) _ tup)))).
  Proof.
    rewrite (@refine_Iterate_Equiv_QueryResultComp m); eauto.
    apply refine_Iterate_Equiv_QueryResultComp_body_Where_And_eq with
    (idx := a_proj idx); eauto.
    - intros; apply r_o_r_n_AbsR.
    - intros; apply r_o_r_n_AbsR in H0; rewrite H0; congruence.
    - intros; apply r_o_r_n_AbsR; eauto.
  Qed.

    Corollary refine_QueryIn_Where_True
        {m : nat}
        {qs_schema : RawQueryStructureSchema}
        (schemaIdx : Fin.t _)
        (attrIdx : Fin.t _)
        a_proj
        el
        (r_o : UnConstrQueryStructure qs_schema)
        (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema m qs_schema schemaIdx attrIdx))
        (r_o_r_n_AbsR : DecomposeRawQueryStructureSchema_AbsR schemaIdx attrIdx a_proj el r_o r_n)
        {ResultT : Type}
        (body : @RawTuple _ -> Comp (list ResultT))
        idx
    : refine (UnConstrQuery_In r_o schemaIdx
                               (fun tup => Where (a_proj (GetAttributeRaw tup attrIdx) = a_proj idx)
                                                 (body tup)))
             (UnConstrQuery_In (snd r_n) (a_proj idx) (fun tup =>
                                                         body
                                                           (Tuple_DecomposeRawQueryStructure_inj _ _ (el (a_proj idx)) _ tup))).
  Proof.
    etransitivity.
    apply refine_UnConstrQuery_In; intro.
    apply refine_Query_Where_Cond with
    (Q := (a_proj (GetAttributeRaw a attrIdx) = a_proj idx) /\ True);
      intuition.
    setoid_rewrite refine_QueryIn_Where; eauto.
    apply refine_UnConstrQuery_In; intro.
    apply refine_Query_Where_True_Cond; eauto.
  Qed.

  Arguments DecomposeRawQueryStructureSchema : simpl never.
  Arguments DecomposeRawQueryStructureSchema_AbsR : simpl never.
  Arguments inj_SumType : simpl never.
  Arguments inj_SumType : simpl never.
  Arguments SumType_proj : simpl never.
  Arguments SumType_index : simpl never.
  Arguments Vector.nth _ _ _ !_ / .

End DecomposeEnumField.
