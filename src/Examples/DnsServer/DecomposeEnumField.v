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
    remember (qschemaSchemas qs_schema)[@schemaIdx] eqn:H;
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
    remember (qschemaSchemas qs_schema)[@schemaIdx] eqn:H;
      clear H qs_schema schemaIdx.
    destruct y as [ [? ?] ? ?]; simpl in *.
    destruct attrIdx.
    eapply Tuple_BreakdownHeading_inj; eassumption.
    eapply Tuple_BreakdownHeading_inj; eassumption.
  Defined.

  (*Fixpoint Tuple_DecomposeRawQueryStructure_Tuple_inj
             {n m : nat}
             (headings : _ )
             (idx : Fin.t m)
             (tup : ilist2 (B := @id Type)
          (AttrList
             (rawSchemaHeading
                (Vector.map
                   (fun
                      rawheading : t Type n =>
                    {|
                    rawSchemaHeading := {|
                                        NumAttr := _;
                                        AttrList := rawheading |};
                    attrConstraints := None;
                    tupleConstraints := None |})
                   headings)[@idx])))
             {struct idx}
      : ilist2 (B := @id Type) headings[@idx].
  Proof.
    destruct idx; simpl in *;
      revert tup; try revert idx;
        pattern n0, headings; apply Vector.caseS.
    - simpl; intros; exact tup.
    - simpl; intros.
      apply Tuple_DecomposeRawQueryStructure_Tuple_inj.
      apply tup.
  Defined.

  Definition Tuple_DecomposeRawQueryStructure_inj'
             {m : nat}
             {qs_schema : RawQueryStructureSchema}
             (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (el : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
             (idx : Fin.t m)
             (tup : ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas (DecomposeRawQueryStructureSchema m qs_schema schemaIdx attrIdx)) idx)))
    : ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)).

    eapply Tuple_DecomposeHeading_inj; eauto.
  Defined.

    Fixpoint Tuple_DecomposeRawQueryStructure_Tuple_proj
             {n m : nat}
             (headings : _ )
             (idx : Fin.t m)
             (tup : ilist2 (B := @id Type) headings[@idx])
             {struct idx}
             :
ilist2 (B := @id Type)
          (AttrList
             (rawSchemaHeading
                (Vector.map
                   (fun
                      rawheading : t Type n =>
                    {|
                    rawSchemaHeading := {|
                                        NumAttr := _;
                                        AttrList := rawheading |};
                    attrConstraints := None;
                    tupleConstraints := None |})
                   headings)[@idx]))
          .
  Proof.
    destruct idx; simpl in *;
      revert tup; try revert idx;
        pattern n0, headings; apply Vector.caseS.
    - simpl; intros; exact tup.
    - simpl; intros.
      apply Tuple_DecomposeRawQueryStructure_Tuple_proj.
      apply tup.
  Defined.

  Definition Tuple_DecomposeRawQueryStructure_proj'
             {m : nat}
             {qs_schema : RawQueryStructureSchema}
             (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (a : Vector.t Type m)
             (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
             (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
             (tup : ilist2 (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)))
             (Tuple_proj :
                ilist2 (B := @id Type)
                       (DecomposeHeading attrIdx
                                         (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) a)[@a_proj_index (GetAttributeRaw tup attrIdx)]
                -> ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a)) (a_proj_index (GetAttributeRaw tup attrIdx))))
              := Tuple_DecomposeRawQueryStructure_Tuple_proj _ (a_proj_index _))
    : ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a)) (a_proj_index (GetAttributeRaw tup attrIdx)))).
    eapply Tuple_proj; eapply Tuple_DecomposeHeading_proj; eauto.
  Defined. *)

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
           IndexedEnsemble_In (GetUnConstrRelation (snd r_n) Ridx) tup
           ->  IndexedEnsemble_In (GetUnConstrRelation (fst r_n) schemaIdx)
                                  (Tuple_DecomposeRawQueryStructure_inj _ _ (el Ridx) _ tup))
    /\ (forall tup,
           IndexedEnsemble_In (GetUnConstrRelation (fst r_n) schemaIdx) tup
           -> IndexedEnsemble_In (GetUnConstrRelation (snd r_n) (a_proj (GetAttributeRaw tup attrIdx))) (Tuple_DecomposeRawQueryStructure_proj _ _ _ tup)).

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
Qed.

Lemma Tuple_DecomposeRawQueryStructure_inj_inverse
      {m : nat}
      {qs_schema : QueryStructureSchema}
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
      DecomposeRawQueryStructureSchema_AbsR
        schemaIdx attrIdx a_proj el
        (UpdateUnConstrRelation r_o schemaIdx (EnsembleInsert tup (GetUnConstrRelation r_o schemaIdx)))
        (UpdateUnConstrRelation (fst r_n) schemaIdx (EnsembleInsert tup (GetUnConstrRelation (fst r_n) schemaIdx)),
         UpdateUnConstrRelation (snd r_n)
                                (a_proj (GetAttributeRaw (indexedElement tup) attrIdx))
                                (EnsembleInsert {| elementIndex := elementIndex tup;
                                                   indexedElement :=
                                                     Tuple_DecomposeRawQueryStructure_proj _ _ a_proj
                                                       (indexedElement tup) |} (GetUnConstrRelation (snd r_n) (a_proj (GetAttributeRaw (indexedElement tup) attrIdx))))).
  repeat split; simpl; intros.
  - destruct (fin_eq_dec schemaIdx Ridx); subst;
      unfold GetUnConstrRelation, UpdateUnConstrRelation.
    + rewrite !ith_replace2_Index_eq.
      unfold Included; intros.
      inversion H0; subst; intuition.
      * econstructor; eauto.
      * econstructor 2; eapply (proj1 H Ridx); apply H1.
    + rewrite !ith_replace2_Index_neq; eauto.
      unfold Included; intros; eapply (proj1 H Ridx); apply H0.
  - destruct (fin_eq_dec schemaIdx Ridx); subst;
      unfold GetUnConstrRelation, UpdateUnConstrRelation.
    + rewrite !ith_replace2_Index_eq.
      unfold Included; intros.
      inversion H0; subst; intuition.
      * econstructor; eauto.
      * econstructor 2; eapply (proj1 H Ridx); apply H1.
    + rewrite !ith_replace2_Index_neq; eauto.
      unfold Included; intros; eapply (proj1 H Ridx); apply H0.
  - unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
    + rewrite !ith_replace2_Index_eq in *.
      simpl in H0.
      destruct (fin_eq_dec
                  Ridx
                  (a_proj (GetAttributeRaw (indexedElement tup) attrIdx))); subst.
      rewrite !ith_replace2_Index_eq in H0.
      destruct H0 as [? [? | ?] ].
      * destruct tup; injections; econstructor; econstructor.
        f_equal; simpl.
        apply Tuple_DecomposeRawQueryStructure_inj_inverse.
      * destruct (proj1 (proj2 H) (a_proj (GetAttributeRaw (indexedElement tup) attrIdx)) tup0).
        econstructor; eauto.
        econstructor; econstructor 2; eauto.
      * rewrite !ith_replace2_Index_neq in H0 by eauto.
        destruct (proj1 (proj2 H) Ridx tup0 H0); eauto.
        econstructor; econstructor 2; eauto.
  - unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
    + rewrite !ith_replace2_Index_eq in H0.
      destruct H0 as [? [? | ?] ]; subst.
      * try rewrite !ith_replace2_Index_eq.
        econstructor; econstructor; f_equal.
      * destruct (proj2 (proj2 H) tup0) as [G H'].
        econstructor; eauto.
        simpl in *.
        econstructor; simpl.
        destruct tup; simpl in *.
        clear r_o H H0.
        unfold In.
        destruct (fin_eq_dec (a_proj (GetAttributeRaw tup0 attrIdx))
                             (a_proj (GetAttributeRaw indexedElement attrIdx))
                 ); subst;
          [ | rewrite !ith_replace2_Index_neq; eauto].
Admitted.

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
    -> forall Ridx,
    refine {idx : nat | UnConstrFreshIdx (GetUnConstrRelation r_o Ridx) idx}
           {idx : nat | forall Ridx', (UnConstrFreshIdx (GetUnConstrRelation (snd r_n) Ridx') idx)}.
Proof.
Admitted.

Fixpoint Iterate_Equiv_QueryResultComp
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
             res' <- Iterate_Equiv_QueryResultComp heading
                  (fun idx => headings (Fin.FS idx))
                  (fun idx => Ensembles (Fin.FS idx))
                  (fun idx tup => (inj_Tuple (Fin.FS idx) tup))
                  body
             ;
             ret (List.app res res')
          end headings Ensembles inj_Tuple.

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
  {ResultT}
  (body : @RawTuple _ -> Comp (list ResultT))
  idx
  : refine (UnConstrQuery_In r_o schemaIdx
                             (fun tup => Where (GetAttributeRaw tup attrIdx = idx)
                                               (body tup)))
           (UnConstrQuery_In (snd r_n) (a_proj idx) (fun tup => body
                                                (Tuple_DecomposeRawQueryStructure_inj _ _ (el (a_proj idx)) _ tup))).
Admitted.

(*Lemma refine_Iterate_Equiv_QueryResultComp
  {m : nat}
  {qs_schema : RawQueryStructureSchema}
  {ResultT}
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
           (Iterate_Equiv_QueryResultComp
              _ _
              (GetUnConstrRelation (snd r_n))
              (fun idx => Tuple_DecomposeRawQueryStructure_inj _ _ (el idx) idx) body).
Admitted. *)

Arguments DecomposeRawQueryStructureSchema : simpl never.
Arguments DecomposeRawQueryStructureSchema_AbsR : simpl never.
Arguments inj_SumType : simpl never.
Arguments inj_SumType : simpl never.
Arguments SumType_proj : simpl never.
Arguments SumType_index : simpl never.
Arguments Vector.nth _ _ _ !_ / .

End DecomposeEnumField.
