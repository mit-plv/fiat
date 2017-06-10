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

  (* Could use above to prove dependent inversion lemma, but *)
  (* this is more of a sanity check than anything. *)
  (* Lemma proj_SumType_inj_inverse {n}
    : forall (v : Vector.t Type n)
             (tag : Fin.t n)
             (el : Vector.nth v tag),
      SumType_proj v (inj_SumType v tag el) = el. *)

  (* Goal: Convert from QueryStructure with a heading with a SumType *)
  (* attribute to one that has multiple tables. *)
  (* Is this a worthwhile refinement? We could just do this at data structure *)
  (* selection time. OTOH, nice high-level refinement step that makes sense to *)
  (* end-users and has applications in both DNS examples.  *)

  Definition AddRawQueryStructureSchema
             {m}
             (raw_qs_schema : RawQueryStructureSchema)
             (new_schemas : Vector.t RawSchema m)
  : RawQueryStructureSchema :=
    {| qschemaSchemas := Vector.append (qschemaSchemas raw_qs_schema) new_schemas;
       qschemaConstraints := [ ] |}.

  Fixpoint LiftTuple_AddRawQueryStructureSchema
           {n m : nat}
           (old_schemas : Vector.t RawSchema n)
           (new_schemas : Vector.t RawSchema m)
           Ridx
           (tup : @RawTuple (GetNRelSchemaHeading old_schemas Ridx))
           {struct old_schemas}
    : @RawTuple
        (GetNRelSchemaHeading (Vector.append old_schemas new_schemas)
                              (Fin.L m Ridx)).
    refine (match old_schemas in Vector.t _ n return
                  forall (Ridx : Fin.t n),
                    @RawTuple (GetNRelSchemaHeading old_schemas Ridx)
                    -> @RawTuple
                         (GetNRelSchemaHeading (Vector.append old_schemas new_schemas)
                                               (Fin.L m Ridx)) with
            | Vector.nil => fun Ridx tup => Fin.case0 (fun _ => _) Ridx
            | Vector.cons _ _ _ => fun Ridx tup => _
            end Ridx tup).
    revert t tup0; pattern n0, Ridx0; apply Fin.caseS; simpl.
    - intros; exact tup0.
    - intros; exact (LiftTuple_AddRawQueryStructureSchema _ _ _ _ _ tup0).
  Defined.

  Definition AddRawQueryStructureSchema_AbsR
             {m : nat}
             {qs_schema : RawQueryStructureSchema}
             (new_schemas : Vector.t RawSchema m)
             (r_o : UnConstrQueryStructure qs_schema)
             (r_n : UnConstrQueryStructure (AddRawQueryStructureSchema qs_schema new_schemas))
    : Prop :=
    (forall Ridx tup,
        IndexedEnsemble_In (GetUnConstrRelation r_o Ridx) tup
        <-> IndexedEnsemble_In (GetUnConstrRelation r_n (Fin.L m Ridx)) (LiftTuple_AddRawQueryStructureSchema _ _ Ridx tup)).

  (* Define new schema *)

  Fixpoint DecomposeHeading
           {n m}
           (attr : Fin.t n)
           (sch : Vector.t Type n)
           (a : Vector.t Type m)
           {struct attr}
    : Vector.t (Vector.t Type n) m :=
    match attr in Fin.t n return Vector.t _ n ->  Vector.t (Vector.t _ n) m with
    | Fin.F1 _ =>
      fun sch =>
        Vector.map (fun t => Vector.cons _ t _ (Vector.tl sch)) a
    | Fin.FS _ attr' =>
      fun sch =>
        Vector.map (fun t => Vector.cons _ (Vector.hd sch) _ t)
                   (DecomposeHeading attr' (Vector.tl sch) a)
    end sch.

  Fixpoint Tuple_mapHeading
           {m q} {A' B' C}
           (idx : Fin.t m)
           (a : Vector.t C m)
           (f : _ -> _ q)
           (tup : ilist2 (A := A') (B := B') (Vector.map f a)[@idx])
           {struct idx}
    : ilist2 (B := B') (f a[@idx]).
    refine (match idx in Fin.t m return
                  forall (a : Vector.t C m)
                         (f : _ -> _ q)
                         (tup : ilist2 (B := B') (Vector.map f a)[@idx]),
                    ilist2 (B := B') (f a[@idx]) with
            | Fin.F1 _ => _
            | Fin.FS _ idx' => _
            end a f tup); clear a tup; intro; try revert idx';
      pattern n, a; apply Vector.caseS.
    - intros; exact tup.
    - simpl; intros; eapply Tuple_mapHeading; eauto.
  Defined.

  Fixpoint Tuple_mapHeading_inv
           {m q} {A' B' C}
           (idx : Fin.t m)
           (a : Vector.t C m)
           (f : _ -> _ q)
           (tup : ilist2 (B := B') (f a[@idx]))
           {struct idx}
    : ilist2 (A := A') (B := B') (Vector.map f a)[@idx].
    refine (match idx in Fin.t m return
                  forall (a : Vector.t C m)
                         (f : _ -> _ q)
                         (tup : ilist2 (B := B') (f a[@idx])),
                    ilist2 (B := B') (Vector.map f a)[@idx] with
            | Fin.F1 _ => _
            | Fin.FS _ idx' => _
            end a f tup); clear a tup; intro; try revert idx';
      pattern n, a; apply Vector.caseS.
    - intros; exact tup.
    - simpl; intros; eapply Tuple_mapHeading_inv; eauto.
  Defined.

  Fixpoint Tuple_DecomposeHeading_inj
           {n m}
           (attrIdx : Fin.t n)
           (heading : Vector.t Type n)
           (a : Vector.t Type m)
           (a_inj : forall idx, Vector.nth a idx -> Vector.nth heading attrIdx)
           (idx : Fin.t m)
           (tup : ilist2 (B := @id Type) (Vector.nth (DecomposeHeading attrIdx heading a) idx))
           {struct attrIdx}
    : ilist2 (B := @id Type) heading.
    refine
      (match attrIdx in Fin.t n return
             forall (heading : Vector.t Type n)
                    (a : Vector.t Type m)
                    (a_inj : forall idx, Vector.nth a idx -> Vector.nth heading attrIdx)
                    (idx : Fin.t m)
                    (tup : ilist2 (B := @id Type) (Vector.nth (DecomposeHeading attrIdx heading a) idx)),
               ilist2 (B := @id Type) heading with
       | Fin.F1 _ => fun heading' => _
       | Fin.FS _ attr' => fun heading' => _
       end heading a a_inj idx tup).
    - clear; pattern n0, heading'; eapply Vector.caseS.
      simpl; intros.
      exact (icons2 (B := @id Type)
                    (a_inj idx (ilist2_hd (Tuple_mapHeading idx a _ tup)))
                    (ilist2_tl (Tuple_mapHeading idx a _ tup))).
    - revert attr'; pattern n0, heading'; eapply Vector.caseS.
      simpl; intros.
      exact (icons2
               (ilist2_hd (Tuple_mapHeading _ _ _ tup0))
               (Tuple_DecomposeHeading_inj
                  _ _ attr' t _ a_inj0 _
                  (ilist2_tl (Tuple_mapHeading _ _ _ tup0)))).
  Defined.

  Fixpoint Tuple_DecomposeHeading_proj
           {n m}
           (attrIdx : Fin.t n)
           (heading : Vector.t Type n)
           (a : Vector.t Type m)
           (a_proj_index : Vector.nth heading attrIdx -> Fin.t m)
           (a_proj : forall (attr : Vector.nth heading attrIdx),
               a[@a_proj_index attr])
           (tup : ilist2 (B := @id Type) heading)
           {struct attrIdx}
    : ilist2 (B := @id Type) (Vector.nth (DecomposeHeading attrIdx heading a) (a_proj_index (ith2 tup attrIdx))).
    refine
      (match attrIdx in Fin.t n return
             forall
               (heading : Vector.t Type n)
               (a : Vector.t Type m)
               (a_proj_index : Vector.nth heading attrIdx -> Fin.t m)
               (a_proj : forall (attr : Vector.nth heading attrIdx),
                   a[@a_proj_index attr])
               (tup : ilist2 (B := @id Type) heading),
               ilist2 (B := @id Type) (Vector.nth (DecomposeHeading attrIdx heading a) (a_proj_index (ith2 tup attrIdx))) with
       | Fin.F1 _ => fun heading' => _
       | Fin.FS _ attr' => fun heading' => _
       end heading a a_proj_index a_proj tup).
    - clear; pattern n0, heading'; eapply Vector.caseS.
      simpl; intros.
      exact (Tuple_mapHeading_inv
               _ a _ (icons2 (B := @id Type) (a_proj (ilist2_hd tup)) (ilist2_tl tup))).
    - revert attr'; pattern n0, heading'; eapply Vector.caseS.
      simpl; intros.
      refine (Tuple_mapHeading_inv
                _ _ _
                (icons2 (B := @id Type)
                        (ilist2_hd tup0)
                        (Tuple_DecomposeHeading_proj _ _ _ _ _ _ a_proj0 (ilist2_tl tup0)))).
  Defined.

  (* Could fuse this with Decompose Heading, but efficiency shouldn't matter too much. *)
  Definition DecomposeSchema
             {m}
             (heading : RawSchema)
             (attr : Fin.t _)
             (a : Vector.t Type m)
    : Vector.t RawSchema m :=
    Vector.map
      (fun rawheading =>
         {| rawSchemaHeading := Build_RawHeading rawheading;
            attrConstraints := None;
            tupleConstraints := None |})
      (DecomposeHeading attr (AttrList (rawSchemaHeading heading)) a).

  Definition DecomposeRawQueryStructureSchema
             {m}
             (raw_qs_schema : RawQueryStructureSchema)
             (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (a : Vector.t Type m)
    : RawQueryStructureSchema :=
    {| qschemaSchemas :=
         DecomposeSchema (Vector.nth (qschemaSchemas raw_qs_schema) schemaIdx)
                         attrIdx a;
       qschemaConstraints := [ ] |}.

  Definition Tuple_DecomposeRawQueryStructure_proj
             {m : nat}
             {qs_schema : RawQueryStructureSchema}
             (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (a : Vector.t Type m)
             (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
             (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
             (tup : ilist2 (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)))
    :  ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a)) (a_proj_index (GetAttributeRaw tup attrIdx)))).
    unfold DecomposeRawQueryStructureSchema in *; simpl in *.
    unfold GetNRelSchema, DecomposeSchema in *;
      simpl in *.
    erewrite VectorSpec.nth_map by eauto; simpl.
    eapply Tuple_DecomposeHeading_proj; eauto.
  Defined.

  Definition Tuple_DecomposeRawQueryStructure_inj
             {m : nat}
             {qs_schema : RawQueryStructureSchema}
             (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (a : Vector.t Type m)
             (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
             (idx : Fin.t m)
             (tup : ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a)) idx)))
    : ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)).
    unfold DecomposeRawQueryStructureSchema in *; simpl in *.
    unfold GetNRelSchema, DecomposeSchema in *;
      simpl in *.
    erewrite VectorSpec.nth_map in tup by eauto; simpl.
    simpl in tup.
    eapply Tuple_DecomposeHeading_inj; eauto.
  Defined.

  Fixpoint Tuple_DecomposeRawQueryStructure_Tuple_inj
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
             (a : Vector.t Type m)
             (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
             (idx : Fin.t m)
             (tup : ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a)) idx)))
             (Tuple_inj :
                ilist2 (B := @id Type) (AttrList (GetNRelSchemaHeading (qschemaSchemas (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a)) idx))
                ->
                ilist2 (B := @id Type)
                       (DecomposeHeading attrIdx
                                         (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) a)[@idx] := Tuple_DecomposeRawQueryStructure_Tuple_inj _ idx)
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
  Defined.

  Definition DecomposeRawQueryStructureSchema_AbsR
             {m : nat}
             {qs_schema : RawQueryStructureSchema}
             (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (a : Vector.t Type m)
             (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
             (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
             (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
             (r_o : UnConstrQueryStructure qs_schema)
             (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
    : Prop :=
    (forall Ridx, Same_set _ (GetUnConstrRelation r_o Ridx)
                           (GetUnConstrRelation (fst r_n) Ridx))
    /\ (forall Ridx tup,
           In _ (GetUnConstrRelation (snd r_n) Ridx) tup
           ->  In _ (GetUnConstrRelation (fst r_n) schemaIdx)
                  {| elementIndex := elementIndex tup;
                     indexedElement := Tuple_DecomposeRawQueryStructure_inj' _ _ a a_inj _ (indexedElement tup) |})
    /\ (forall tup,
           In _ (GetUnConstrRelation (fst r_n) schemaIdx) tup
           -> In _ (GetUnConstrRelation (snd r_n) (a_proj_index (GetAttributeRaw (indexedElement tup) attrIdx)))
                 {| elementIndex := elementIndex tup;
                    indexedElement := Tuple_DecomposeRawQueryStructure_proj' _ _ a _ a_proj (indexedElement tup) |})
    /\ (forall Ridx Ridx' tup tup' ,
           In _ (GetUnConstrRelation (snd r_n) Ridx) tup
           -> In _ (GetUnConstrRelation (snd r_n) Ridx') tup'
           -> Ridx <> Ridx'
           -> elementIndex tup <> elementIndex tup')
    /\ (forall Ridx tup,
           In IndexedElement (GetUnConstrRelation (snd r_n) Ridx) tup
           -> a_proj_index (GetAttributeRaw
                              (Tuple_DecomposeRawQueryStructure_inj' _ _ a a_inj _ (indexedElement tup)) attrIdx) = Ridx)
    /\ (forall Ridx, FiniteEnsemble (GetUnConstrRelation (snd r_n) Ridx)).

  Definition DecomposeRawQueryStructureSchema_AbsR'
             {m : nat}
             {qs_schema : QueryStructureSchema}
             ( schemaIdx' : BoundedIndex (QSschemaNames qs_schema))
             (schemaIdx := ibound (indexb schemaIdx'))
             {attrIdx' : BoundedIndex (HeadingNames (QSGetNRelSchemaHeading (qs_schema) schemaIdx'))}
             (attrIdx := ibound (indexb attrIdx'))
             (attrIdx_inj : Fin.t _ -> Fin.t _)
             (EnumTypes : Vector.t Type m)
             (f' : Vector.nth (AttrList _) (attrIdx_inj attrIdx) -> SumType EnumTypes)
             (f'' : SumType EnumTypes -> Vector.nth (AttrList _) (attrIdx_inj attrIdx))
             (a_proj_index : Vector.nth (AttrList _) (attrIdx_inj attrIdx) -> Fin.t m :=
                fun attr => SumType_index EnumTypes (f' attr))
             (a_proj : forall (attr : Vector.nth _ (attrIdx_inj attrIdx)), EnumTypes[@a_proj_index attr] :=
                fun attr => SumType_proj EnumTypes (f' attr))
             (a_inj : forall idx, Vector.nth EnumTypes idx -> Vector.nth (AttrList _) (attrIdx_inj attrIdx) :=
                fun idx attr => f'' (inj_SumType EnumTypes idx attr))
             (r_o : UnConstrQueryStructure qs_schema)
             (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx (attrIdx_inj attrIdx) EnumTypes))
    : Prop :=
    DecomposeRawQueryStructureSchema_AbsR (qs_schema := qs_schema)
                                          schemaIdx (attrIdx_inj attrIdx)
                                          EnumTypes a_proj_index a_proj a_inj r_o r_n.

  Definition DecomposeRawQueryStructureSchema_empty_AbsR
             {m : nat}
             {qs_schema : QueryStructureSchema}
    : forall (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (a : Vector.t Type m)
             (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
             (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
             (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx),
      DecomposeRawQueryStructureSchema_AbsR
        schemaIdx attrIdx a a_proj_index a_proj a_inj
        (DropQSConstraints (QSEmptySpec qs_schema))
        (DropQSConstraints (QSEmptySpec qs_schema),
         imap2 (fun ns : RawSchema => rawRel (RelationSchema:=ns))
               (Build_EmptyRelations
                  (qschemaSchemas (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a)))).
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
             (a : Vector.t Type m)
             (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
             (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
             (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
             r_o
             r_n,
      DecomposeRawQueryStructureSchema_AbsR
        schemaIdx attrIdx a a_proj_index a_proj a_inj r_o r_n
      ->
      forall Ridx tup,
        Ridx <> schemaIdx
        -> DecomposeRawQueryStructureSchema_AbsR
             schemaIdx attrIdx a a_proj_index a_proj a_inj
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
             (a : Vector.t Type m)
             (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
             (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
             (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
             tup,
      Tuple_DecomposeRawQueryStructure_inj' schemaIdx attrIdx a a_inj
                                            (a_proj_index (GetAttributeRaw tup attrIdx))
                                            (Tuple_DecomposeRawQueryStructure_proj' schemaIdx attrIdx a a_proj_index a_proj
                                                                                    tup) = tup.
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
             (a : Vector.t Type m)
             (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
             (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
             (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
             r_o
             r_n,
      DecomposeRawQueryStructureSchema_AbsR
        schemaIdx attrIdx a a_proj_index a_proj a_inj
        r_o r_n
      ->
      forall tup
             (freshIdx : UnConstrFreshIdx (GetUnConstrRelation (fst r_n) schemaIdx) (elementIndex tup)),
        DecomposeRawQueryStructureSchema_AbsR
          schemaIdx attrIdx a a_proj_index a_proj a_inj
          (UpdateUnConstrRelation r_o schemaIdx (EnsembleInsert tup (GetUnConstrRelation r_o schemaIdx)))
          (UpdateUnConstrRelation (fst r_n) schemaIdx (EnsembleInsert tup (GetUnConstrRelation (fst r_n) schemaIdx)),
           UpdateUnConstrRelation (snd r_n)
                                  (a_proj_index (GetAttributeRaw (indexedElement tup) attrIdx))
                                  (EnsembleInsert {| elementIndex := elementIndex tup;
                                                     indexedElement :=
                                                       Tuple_DecomposeRawQueryStructure_proj'
                                                         _ _ _ _ a_proj
                                                         (indexedElement tup) |} (GetUnConstrRelation (snd r_n) (a_proj_index (GetAttributeRaw (indexedElement tup) attrIdx))))).
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
                    (a_proj_index (GetAttributeRaw (indexedElement tup) attrIdx))); subst.
        rewrite !ith_replace2_Index_eq in H0.
        destruct H0 as [? | ?]; subst.
        * destruct tup; subst; injections; simpl.
          econstructor; f_equal; simpl.
          erewrite <- Tuple_DecomposeRawQueryStructure_inj_inverse.
          reflexivity.
        * pose proof (proj1 (proj2 H) (a_proj_index (GetAttributeRaw (indexedElement tup) attrIdx)) tup0).
          apply H1 in H0.
          econstructor 2; eauto.
        * rewrite !ith_replace2_Index_neq in H0 by eauto.
          pose proof (proj1 (proj2 H) Ridx tup0 H0); eauto.
          econstructor 2; eauto.
    - unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
      + rewrite !ith_replace2_Index_eq in H0.
        destruct H0 as [? | ?]; subst.
        * try rewrite !ith_replace2_Index_eq.
          econstructor; econstructor; f_equal.
        * apply (proj1 (proj2 (proj2 H)) tup0) in H0.
          simpl in *.
          destruct tup0; destruct tup; simpl in *.
          clear r_o H.
          destruct (fin_eq_dec (a_proj_index (GetAttributeRaw indexedElement attrIdx))
                               (a_proj_index (GetAttributeRaw indexedElement0 attrIdx))
                   ); subst;
            [ | rewrite !ith_replace2_Index_neq; eauto].
          symmetry in e;
            erewrite ith_replace2_Index_eq' with (H := e).
          revert H0; clear.
          match goal with
            |- context[In _ _ ?G] => generalize G; clear
          end.
          revert e.
          match goal with
            |- context[EnsembleInsert ?t _] =>
            generalize t
          end.
          clear.
          destruct e; simpl; intros.
          unfold EnsembleInsert; intuition.
    - unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
      destruct (fin_eq_dec
                  Ridx
                  (a_proj_index (GetAttributeRaw (indexedElement tup) attrIdx)));
        destruct (fin_eq_dec
                    Ridx'
                    (a_proj_index (GetAttributeRaw (indexedElement tup) attrIdx))); subst.
      + congruence.
      + rewrite ith_replace2_Index_eq in H0.
        rewrite ith_replace2_Index_neq in H1 by eauto.
        destruct H0 as [? | ?]; subst; simpl.
        * apply (proj1 (proj2 H)) in H1; apply freshIdx in H1; simpl in *; try omega.
        * apply H; eauto.
      + rewrite ith_replace2_Index_neq in H0 by eauto.
        rewrite ith_replace2_Index_eq in H1.
        destruct H1 as [? | ?]; subst; simpl.
        * apply (proj1 (proj2 H)) in H0; apply freshIdx in H0; simpl in *; omega.
        * apply H; eauto.
      + rewrite ith_replace2_Index_neq in H0 by eauto.
        rewrite ith_replace2_Index_neq in H1 by eauto.
        apply H; eauto.
    - unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
      destruct (fin_eq_dec
                  Ridx
                  (a_proj_index (GetAttributeRaw (indexedElement tup) attrIdx))).
      + subst.
        rewrite ith_replace2_Index_eq in H0.
        destruct H0 as [? | ?]; subst; simpl.
        * repeat f_equal.
          erewrite <- Tuple_DecomposeRawQueryStructure_inj_inverse;
            reflexivity.
        * apply H; eauto.
      + rewrite ith_replace2_Index_neq in H0 by eauto.
        apply H; eauto.
    - unfold GetUnConstrRelation, UpdateUnConstrRelation in *.
      destruct (fin_eq_dec
                  Ridx
                  (a_proj_index (GetAttributeRaw (indexedElement tup) attrIdx))).
      + subst; rewrite ith_replace2_Index_eq.
        apply FiniteEnsemble_Insert; eauto.
        * unfold UnConstrFreshIdx in *; simpl in *; intros.
          eapply (proj1 (proj2 H)) in H0; simpl in H0.
          apply freshIdx in H0.
          simpl in H0; eauto.
        * apply H.
      + rewrite ith_replace2_Index_neq by eauto.
        apply H.
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
            (a : Vector.t Type m)
            (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
            (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
            (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
            (r_o : UnConstrQueryStructure qs_schema)
            (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
    : DecomposeRawQueryStructureSchema_AbsR schemaIdx attrIdx a a_proj_index a_proj a_inj r_o r_n
      -> refine {idx : nat | UnConstrFreshIdx (GetUnConstrRelation r_o schemaIdx) idx}
                {idx : nat | forall Ridx', UnConstrFreshIdx (GetUnConstrRelation (snd r_n) Ridx') idx}.
  Proof.
    intros; etransitivity.
    - apply refine_UnConstrFreshIdx_Same_Set_Equiv.
      apply (proj1 H).
    - eapply refineEquiv_pick_pick; unfold UnConstrFreshIdx; split; intros.
      apply (proj1 (proj2 (proj2 H))) in H1.
      apply H0 in H1; apply H1.
      apply (proj1 (proj2 H)) in H1.
      apply H0 in H1.
      apply H1.
  Qed.

  Corollary refineEquiv_UnConstrFreshIdx_DecomposeRawQueryStructureSchema_AbsR_Equiv'
            {m : nat}
            {qs_schema : RawQueryStructureSchema}
            (schemaIdx : Fin.t _)
            (attrIdx : Fin.t _)
            (a : Vector.t Type m)
            (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
            (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
            (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
            (r_o : UnConstrQueryStructure qs_schema)
            (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
    : DecomposeRawQueryStructureSchema_AbsR schemaIdx attrIdx a a_proj_index a_proj a_inj r_o r_n
      -> forall Ridx,
        refineEquiv {idx : nat | UnConstrFreshIdx (GetUnConstrRelation r_o Ridx) idx}
               {idx : nat | UnConstrFreshIdx (GetUnConstrRelation (fst r_n) Ridx) idx}.
  Proof.
    intros; split; rewrite refine_UnConstrFreshIdx_Same_Set_Equiv;
      try reflexivity.
    apply (proj1 H).
    unfold Same_set; split; apply (proj1 H).
  Qed.

  Corollary refine_UnConstrFreshIdx_DecomposeRawQueryStructureSchema_AbsR_Equiv'
            {m : nat}
            {qs_schema : RawQueryStructureSchema}
            (schemaIdx : Fin.t _)
            (attrIdx : Fin.t _)
            (a : Vector.t Type m)
            (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
            (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
            (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
            (r_o : UnConstrQueryStructure qs_schema)
            (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
    : DecomposeRawQueryStructureSchema_AbsR schemaIdx attrIdx a a_proj_index a_proj a_inj r_o r_n
      -> forall Ridx idx',
        computes_to {idx : nat | UnConstrFreshIdx (GetUnConstrRelation r_o Ridx) idx} idx'
        -> UnConstrFreshIdx (GetUnConstrRelation (fst r_n) Ridx) idx'.
  Proof.
    intros.
    computes_to_inv.
    rewrite <- UnConstrFreshIdx_Same_Set_Equiv; eauto.
    apply (proj1 H Ridx).
  Qed.

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

  Corollary DecomposeRawQueryStructureSchema_UpdateUnConstrRelationInsertC_eq
            {m : nat}
            {qs_schema : QueryStructureSchema}
            {ResultT}
    : forall (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (a : Vector.t Type m)
             (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
             (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
             (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
             r_o
             r_n
             (k : UnConstrQueryStructure qs_schema -> Comp ResultT)
             (k' : _ -> Comp ResultT),
      DecomposeRawQueryStructureSchema_AbsR
        schemaIdx attrIdx a a_proj_index a_proj a_inj
        r_o r_n
      -> forall freshIdx tup,
        computes_to {idx | UnConstrFreshIdx (GetUnConstrRelation r_o schemaIdx) idx} freshIdx
        -> (forall r_o' r_n',
               DecomposeRawQueryStructureSchema_AbsR
                 schemaIdx attrIdx a a_proj_index a_proj a_inj
                 r_o' r_n'
               -> refine (k r_o') (k' r_n'))
        ->
        refine (r_o' <- UpdateUnConstrRelationInsertC r_o schemaIdx {| elementIndex := freshIdx; indexedElement := tup |};
                  k r_o')
               (r_n' <- UpdateUnConstrRelationInsertC (fst r_n) schemaIdx {| elementIndex := freshIdx; indexedElement := tup |};
                  r_n'' <- UpdateUnConstrRelationInsertC (snd r_n)
                        (a_proj_index (GetAttributeRaw tup attrIdx))
                        {| elementIndex := freshIdx;
                           indexedElement :=
                             Tuple_DecomposeRawQueryStructure_proj'
                               _ _ _ _ a_proj
                               tup |};
                  k' (r_n', r_n'')).
  Proof.
    Local Transparent UpdateUnConstrRelationInsertC.
    unfold UpdateUnConstrRelationInsertC; intros.
    repeat rewrite refineEquiv_bind_unit.
    rewrite H1.
    reflexivity.
    simpl.
    eapply (DecomposeRawQueryStructureSchema_Insert_AbsR_eq H); eauto.
    eapply refine_UnConstrFreshIdx_DecomposeRawQueryStructureSchema_AbsR_Equiv'; eauto.
  Qed.

  Corollary DecomposeRawQueryStructureSchema_UpdateUnConstrRelationInsertC_neq
            {m : nat}
            {qs_schema : QueryStructureSchema}
            {ResultT}
    : forall (schemaIdx : Fin.t _)
             (attrIdx : Fin.t _)
             (a : Vector.t Type m)
             (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
             (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
             (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
             r_o
             r_n
             (k : UnConstrQueryStructure qs_schema -> Comp ResultT)
             (k' : _ -> Comp ResultT),
      DecomposeRawQueryStructureSchema_AbsR
        schemaIdx attrIdx a a_proj_index a_proj a_inj
        r_o r_n
      -> forall Ridx freshIdx tup,
        Ridx <> schemaIdx
        -> (forall r_o' r_n',
               DecomposeRawQueryStructureSchema_AbsR
                 schemaIdx attrIdx a a_proj_index a_proj a_inj
                 r_o' r_n'
               -> refine (k r_o') (k' r_n'))
        ->
        refine (r_o' <- UpdateUnConstrRelationInsertC r_o Ridx {| elementIndex := freshIdx; indexedElement := tup |};
                  k r_o')
               (r_n' <- UpdateUnConstrRelationInsertC (fst r_n) Ridx {| elementIndex := freshIdx; indexedElement := tup |};
                  k' (r_n', snd r_n)).
  Proof.
    unfold UpdateUnConstrRelationInsertC; intros.
    repeat rewrite refineEquiv_bind_unit.
    rewrite H1.
    reflexivity.
    simpl; eapply (DecomposeRawQueryStructureSchema_Insert_AbsR_neq H); eauto.
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

  Definition Iterate_Equiv_For_UnConstrQuery_In_body
           {m : nat}
           {qs_schema : RawQueryStructureSchema}
           {ResultT}
           (schemaIdx : Fin.t _)
           (body : @RawTuple _ -> Comp (list ResultT))
           (attrIdx : Fin.t _)
           (a : Vector.t Type m)
           (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
           (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
           (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
           (r_n : UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
    : Comp (list ResultT) :=
    (fix Iterate_Equiv_For_UnConstrQuery_In_body' (m : nat) :=
    match m return (Fin.t m -> Comp (list ResultT)) -> _
    with
    | 0 => fun results => ret nil
    | S n'' => fun results =>
        res <- results Fin.F1;
        res' <- Iterate_Equiv_For_UnConstrQuery_In_body' n'' (fun idx => results (Fin.FS idx));
        ret (List.app res res')
    end) _ (fun idx => For (UnConstrQuery_In r_n idx
                                             (fun tup => body (Tuple_DecomposeRawQueryStructure_inj' _ _ a a_inj idx tup)))).

  Definition Iterate_Equiv_Count_For_UnConstrQuery_In_body
           {m : nat}
           {qs_schema : RawQueryStructureSchema}
           {ResultT}
           (schemaIdx : Fin.t _)
           (body : @RawTuple _ -> Comp (list ResultT))
           (attrIdx : Fin.t _)
           (a : Vector.t Type m)
           (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
           (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
           (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
           (r_n : UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
    : Comp nat :=
    (fix Iterate_Equiv_For_UnConstrQuery_In_body' (m : nat) :=
    match m return (Fin.t m -> Comp nat) -> _
    with
    | 0 => fun results => ret 0
    | S n'' => fun results =>
        res <- results Fin.F1;
        res' <- Iterate_Equiv_For_UnConstrQuery_In_body' n'' (fun idx => results (Fin.FS idx));
        ret (res + res')
    end) _ (fun idx => Count (For (UnConstrQuery_In r_n idx
                                             (fun tup => body (Tuple_DecomposeRawQueryStructure_inj' _ _ a a_inj idx tup))))).

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
        {ResultT}
        (schemaIdx : Fin.t _)
        (body : @RawTuple _ -> Comp (list ResultT))
        (attrIdx : Fin.t _)
        (a : Vector.t Type m)
        (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
        (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
        (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
        (r_o : UnConstrQueryStructure qs_schema)
        (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
    : DecomposeRawQueryStructureSchema_AbsR schemaIdx attrIdx a a_proj_index a_proj a_inj r_o r_n
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
        {ResultT}
        (schemaIdx : Fin.t _)
        (body : @RawTuple _ -> Comp (list ResultT))
        (attrIdx : Fin.t _)
        (a : Vector.t Type m)
        (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
        (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
        (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
        (r_o : UnConstrQueryStructure qs_schema)
        (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
    : DecomposeRawQueryStructureSchema_AbsR schemaIdx attrIdx a a_proj_index a_proj a_inj r_o r_n
      ->
      refine (UnConstrQuery_In r_o schemaIdx body)
             (Iterate_Equiv_QueryResultComp_body
                _ _
                (GetUnConstrRelation (snd r_n))
                (Tuple_DecomposeRawQueryStructure_inj' _ _ a a_inj) body).
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
      symmetry; eapply Tuple_DecomposeRawQueryStructure_inj_inverse.
      unfold In in *; apply H0 in H1; destruct_ex; intuition; subst.
      apply (proj1 (proj2 H)) in H4; eassumption.
  Qed.

    Lemma refine_Iterate_For_UnConstrQuery_In_QueryResultComp
        {m : nat}
        {qs_schema : RawQueryStructureSchema}
        {ResultT}
        (schemaIdx : Fin.t _)
        (body : @RawTuple _ -> Comp (list ResultT))
        (attrIdx : Fin.t _)
        (a : Vector.t Type m)
        (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
        (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
        (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
        (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
    : refine (For (Iterate_Equiv_QueryResultComp_body
                _ _
                (GetUnConstrRelation (snd r_n))
                (Tuple_DecomposeRawQueryStructure_inj' _ _ a a_inj) body))
             (Iterate_Equiv_For_UnConstrQuery_In_body
                schemaIdx body attrIdx a a_proj_index a_proj a_inj (snd r_n)).
  Proof.
    intros.
    unfold Iterate_Equiv_For_UnConstrQuery_In_body.
    destruct r_n as [ r_n' r_n].
    unfold UnConstrQuery_In.
    simpl.
    generalize (GetUnConstrRelation r_n).
    unfold DecomposeRawQueryStructureSchema; simpl.
    generalize ((Tuple_DecomposeRawQueryStructure_inj' schemaIdx attrIdx a a_inj)).
    simpl; clear.
    generalize (DecomposeSchema (qschemaSchemas qs_schema)[@schemaIdx] attrIdx a); clear.
    induction m; simpl; intros.
    - rewrite refine_For_List; reflexivity.
    - revert i i0 IHm.
      pattern m, t; apply Vector.caseS; simpl; clear t; intros.
      setoid_rewrite <- (IHm t (fun idx => i (Fin.FS idx)) (fun idx => i0 (Fin.FS idx))).
      Local Transparent Query_For.
      unfold Query_For.
      autorewrite with monad laws.
      clear; intros ? ?; computes_to_inv; subst.
      repeat computes_to_econstructor; eauto using Permutation_app.
      Local Opaque Query_For.
  Qed.

  Corollary refine_Iterate_For_UnConstrQuery_In
          {m : nat}
        {qs_schema : RawQueryStructureSchema}
        {ResultT}
        (schemaIdx : Fin.t _)
        (body : @RawTuple _ -> Comp (list ResultT))
        (attrIdx : Fin.t _)
        (a : Vector.t Type m)
        (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
        (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
        (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
        (r_o : UnConstrQueryStructure qs_schema)
        (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
    : DecomposeRawQueryStructureSchema_AbsR schemaIdx attrIdx a a_proj_index a_proj a_inj r_o r_n
      ->
      refine (For (UnConstrQuery_In r_o schemaIdx body))
             (Iterate_Equiv_For_UnConstrQuery_In_body
                schemaIdx body attrIdx a a_proj_index a_proj a_inj (snd r_n)).
  Proof.
    intros; rewrite <- refine_Iterate_For_UnConstrQuery_In_QueryResultComp.
    rewrite (refine_Iterate_Equiv_QueryResultComp _ H); reflexivity.
  Qed.

  Lemma refine_Iterate_Count_For_UnConstrQuery_In_QueryResultComp
        {m : nat}
        {qs_schema : RawQueryStructureSchema}
        {ResultT}
        (schemaIdx : Fin.t _)
        (body : @RawTuple _ -> Comp (list ResultT))
        (attrIdx : Fin.t _)
        (a : Vector.t Type m)
        (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
        (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
        (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
        (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
    : refine (Count (For (Iterate_Equiv_QueryResultComp_body
                _ _
                (GetUnConstrRelation (snd r_n))
                (Tuple_DecomposeRawQueryStructure_inj' _ _ a a_inj) body)))
             (Iterate_Equiv_Count_For_UnConstrQuery_In_body
                schemaIdx body attrIdx a a_proj_index a_proj a_inj (snd r_n)).
  Proof.
    intros.
    unfold Iterate_Equiv_Count_For_UnConstrQuery_In_body.
    destruct r_n as [ r_n' r_n].
    unfold UnConstrQuery_In.
    simpl.
    generalize (GetUnConstrRelation r_n).
    unfold DecomposeRawQueryStructureSchema; simpl.
    generalize ((Tuple_DecomposeRawQueryStructure_inj' schemaIdx attrIdx a a_inj)).
    simpl; clear.
    generalize (DecomposeSchema (qschemaSchemas qs_schema)[@schemaIdx] attrIdx a); clear.
    induction m; simpl; intros.
    - rewrite refine_For_List; rewrite refine_Count; simplify with monad laws; reflexivity.
    - revert i i0 IHm.
      pattern m, t; apply Vector.caseS; simpl; clear t; intros.
      setoid_rewrite <- (IHm t (fun idx => i (Fin.FS idx)) (fun idx => i0 (Fin.FS idx))).
      Local Transparent Query_For.
      Local Transparent Count.
      unfold Query_For.
      unfold Count.
      autorewrite with monad laws.
      clear; intros ? ?; computes_to_inv; subst.
      repeat computes_to_econstructor; eauto using Permutation_app.
      rewrite app_length.
      erewrite (Permutation_length H''''), Permutation_length; eauto using Permutation_app.
      Local Opaque Query_For.
      Local Opaque Count.
  Qed.

  Corollary refine_Iterate_Count_For_UnConstrQuery_In
          {m : nat}
        {qs_schema : RawQueryStructureSchema}
        {ResultT}
        (schemaIdx : Fin.t _)
        (body : @RawTuple _ -> Comp (list ResultT))
        (attrIdx : Fin.t _)
        (a : Vector.t Type m)
        (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
        (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
        (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
        (r_o : UnConstrQueryStructure qs_schema)
        (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
    : DecomposeRawQueryStructureSchema_AbsR schemaIdx attrIdx a a_proj_index a_proj a_inj r_o r_n
      ->
      refine (Count (For (UnConstrQuery_In r_o schemaIdx body)))
             (Iterate_Equiv_Count_For_UnConstrQuery_In_body
                schemaIdx body attrIdx a a_proj_index a_proj a_inj (snd r_n)).
  Proof.
    intros; rewrite (refine_Iterate_Equiv_QueryResultComp _ H),
            refine_Iterate_Count_For_UnConstrQuery_In_QueryResultComp;
    reflexivity.
  Qed.

  Lemma refine_Query_Where_Cond :
    forall (ResultT : Type) (P Q : Prop)
           (body : Comp (list ResultT)),
      (P <-> Q)
      -> refine (Query_Where P body)
                (Query_Where Q body).
  Proof.
    unfold pointwise_relation, Query_Where; intros.
    intros ? ?; intuition; computes_to_inv; computes_to_econstructor.
    intuition; intros.
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

  Lemma refine_Query_Where_True_Cond :
    forall (ResultT : Type) (P : Prop )
           (body : Comp (list ResultT)),
      P
      -> refine (Query_Where P body) body.
  Proof.
    intros.
    etransitivity; intro.
    apply refine_Query_Where_Cond with (Q := True).
    intuition; intros.
    intros; computes_to_econstructor; intuition.
  Qed.

  Lemma refine_Query_Where_False_Cond :
    forall (ResultT : Type) (P : Prop )
           (body : Comp (list ResultT)),
      ~ P
      -> refine (Query_Where P body) (ret nil).
  Proof.
    intros.
    etransitivity; intro.
    apply refine_Query_Where_Cond with (Q := False).
    intuition; intros.
    intros; computes_to_econstructor; intuition;
      computes_to_inv; eauto.
  Qed.

  Lemma flatten_CompList_nil':
    forall (A B : Type)(seq : list A),
      refine (FlattenCompList.flatten_CompList (map (fun _ => ret nil) seq)) (ret (@nil B)).
  Proof.
    induction seq; simpl; unfold refine; intros; computes_to_inv; subst; eauto.
  Qed.

  Lemma refine_QueryResultComp_body_Where_False
        {ResultT : Type}
        {heading}
        (body : @RawTuple heading -> Comp (list ResultT))
        P R
    :
      (forall tup, In _ R tup -> ~ P (indexedElement tup))
      -> FiniteEnsemble R
      -> refine (QueryResultComp R (fun tup => Where (P tup) (body tup)))
                (ret nil).
  Proof.
    intros; unfold QueryResultComp.
    destruct H0.
    refine pick val _; eauto.
    simplify with monad laws.
    rewrite refine_flatten_CompList_func' with (f' := fun _ => ret nil).
    apply flatten_CompList_nil'.
    intros; computes_to_econstructor; computes_to_inv; subst;
      intuition.
    unfold UnIndexedEnsembleListEquivalence in H0; destruct_ex;
      intuition; subst.
    apply in_map_iff in H1; destruct_ex; intuition; subst.
    apply H in H2; intuition.
    apply H0; eauto.
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
        {ResultT}
        (schemaIdx : Fin.t _)
        (body : @RawTuple _ -> Comp (list ResultT))
        (attrIdx : Fin.t _)
        (a : Vector.t Type m)
        (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
        (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
        (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
        (r_o : UnConstrQueryStructure qs_schema)
        (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
        idx
        Q
    : DecomposeRawQueryStructureSchema_AbsR schemaIdx attrIdx a a_proj_index a_proj a_inj r_o r_n
      ->
      refine (UnConstrQuery_In r_o schemaIdx
                               (fun tup => Where (a_proj_index (GetAttributeRaw tup attrIdx) =  idx
                                                  /\ Q tup)
                                                 (body tup)))
             (UnConstrQuery_In (snd r_n) idx (fun tup =>
                                                Where (Q (Tuple_DecomposeRawQueryStructure_inj' _ _ _ a_inj _ tup))
                                                      (body
                                                         (Tuple_DecomposeRawQueryStructure_inj' _ _ _ a_inj _ tup)))).
  Proof.
    intros; rewrite (@refine_Iterate_Equiv_QueryResultComp m); eauto.
    apply refine_Iterate_Equiv_QueryResultComp_body_Where_And_eq  with
    (idx := idx); eauto.
    - intros; apply H.
    - intros; apply H in H1; rewrite H1; congruence.
    - intros; apply H; eauto.
  Qed.

  Corollary refine_QueryIn_Where_True
            {m : nat}
            {qs_schema : RawQueryStructureSchema}
            {ResultT}
            (schemaIdx : Fin.t _)
            (body : @RawTuple _ -> Comp (list ResultT))
            (attrIdx : Fin.t _)
            (a : Vector.t Type m)
            (a_proj_index : Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx -> Fin.t m)
            (a_proj : forall (attr : Vector.nth _ attrIdx), a[@a_proj_index attr])
            (a_inj : forall idx, Vector.nth a idx -> Vector.nth (AttrList (GetNRelSchemaHeading (qschemaSchemas qs_schema) schemaIdx)) attrIdx)
            (r_o : UnConstrQueryStructure qs_schema)
            (r_n : UnConstrQueryStructure qs_schema * UnConstrQueryStructure (DecomposeRawQueryStructureSchema qs_schema schemaIdx attrIdx a))
            idx
    : DecomposeRawQueryStructureSchema_AbsR schemaIdx attrIdx a a_proj_index a_proj a_inj r_o r_n
      -> refine (UnConstrQuery_In r_o schemaIdx
                                  (fun tup => Where (a_proj_index (GetAttributeRaw tup attrIdx) = idx)
                                                    (body tup)))
                (UnConstrQuery_In (snd r_n) idx (fun tup =>
                                                   body
                                                     (Tuple_DecomposeRawQueryStructure_inj' _ _ _ a_inj _ tup))).
  Proof.
    etransitivity.
    apply refine_UnConstrQuery_In; intro.
    apply refine_Query_Where_Cond with
    (Q := (a_proj_index (GetAttributeRaw a0 attrIdx) = idx) /\ True);
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

  Definition EnumIDs := ["A"; "NS"; "CNAME"; "SOA" ].
  Definition EnumID := Fin.t 4.
  Definition EnumTypes := [nat : Type; string : Type; nat : Type; list nat : Type].
  Definition EnumType := SumType EnumTypes.

  Definition EESchema :=
    Query Structure Schema
          [ relation "foo" has
                     schema <"A" :: nat, "BID" :: EnumID, "B" :: EnumType>
            (*where (fun t => ibound (indexb t!"BID") = SumType_index _ t!"B" ) and (fun t t' => True) *);
              relation "bar" has
                       schema <"C" :: nat, "D" :: list string>
          ]
          enforcing [ ].

  Definition EESpec : ADT _ :=
    Def ADT {
          rep := QueryStructure EESchema,

                 Def Constructor "Init" : rep := empty,,

                                                      Def Method1 "AddData" (this : rep) (t : _) : rep * bool :=
            Insert t into this!"foo",

            Def Method1 "Process" (this : rep) (p : EnumID) : rep * list _ :=
              results <- For (r in this!"foo")
                      Where ( (SumType_index _ r!"B") = p)
                      Return r;
          ret (this, results)}.

  Definition EEImpl : FullySharpened EESpec.
    unfold EESpec.
    start sharpening ADT.
    start_honing_QueryStructure'.
    let AbsR' := constr:(@DecomposeRawQueryStructureSchema_AbsR' _ EESchema ``"foo" ``"B"
                                                                 id EnumTypes id id) in  hone representation using AbsR'.
    {
      simplify with monad laws.
      apply refine_pick_val.
      apply DecomposeRawQueryStructureSchema_empty_AbsR.
    }
    { (* Insert *)
      simpl in *; simplify with monad laws; cbv beta; simpl.
      rewrite (refine_UnConstrFreshIdx_DecomposeRawQueryStructureSchema_AbsR_Equiv H0).
      unfold H; eapply refine_under_bind; intros.
      apply refine_under_bind_both; intros.
      apply refine_pick_val.
      eapply (DecomposeRawQueryStructureSchema_Insert_AbsR_eq H0).
      eapply refine_UnConstrFreshIdx_DecomposeRawQueryStructureSchema_AbsR_Equiv in H1;
        eauto.
      eapply refine_UnConstrFreshIdx_DecomposeRawQueryStructureSchema_AbsR_Equiv';
        eauto.
      finish honing.
    }
    { (* Query *)
      simpl in *; simplify with monad laws; cbv beta; simpl.
      rewrite refine_For; simplify with monad laws.
      rewrite (refine_QueryIn_Where_True _ H0).
      simpl.
      (* More refinements here. *)
  Abort.
End DecomposeEnumField.

Ltac simplify_GetAttributeRaw_inj :=
  match goal with
    |- context [UnConstrQuery_In ?r_n ?Ridx (fun tup =>  Query_Where (@?P tup) _)] =>
    rewrite (fun ResultT =>
               @refine_UnConstrQuery_In_Query_Where_Cond _ r_n Ridx ResultT P);
    [ | intros; simpl;
        match goal with
          |- context [GetAttribute (Tuple_DecomposeRawQueryStructure_inj'
                                      (qs_schema := ?qs_schema)
                                      ?schemaIdx ?attrIdx ?a ?a_inj ?tag ?tup) ?attrIdx'] =>
          let eq := eval compute in (fin_eq_dec attrIdx (ibound (indexb attrIdx'))) in
              match eq with
              | left ?e =>
                let H := fresh in
                assert (GetAttribute (Tuple_DecomposeRawQueryStructure_inj'
                                        (qs_schema := qs_schema)
                                        schemaIdx attrIdx a a_inj tag tup) attrIdx'
                        = a_inj tag (GetAttributeRaw tup (ibound (indexb attrIdx')))) as H by reflexivity;
                simpl in H; rewrite H; clear H; finish honing
              |right ?e =>
               let H := fresh in
               assert (GetAttribute (Tuple_DecomposeRawQueryStructure_inj'
                                       (qs_schema := qs_schema)
                                       schemaIdx attrIdx a a_inj tag tup) attrIdx'
                       = GetAttributeRaw tup (ibound (indexb attrIdx'))) as H by reflexivity;
               simpl in H; rewrite H; clear H; finish honing
              end
        | |- context [GetAttributeRaw (Tuple_DecomposeRawQueryStructure_inj'
                                      (qs_schema := ?qs_schema)
                                      ?schemaIdx ?attrIdx ?a ?a_inj ?tag ?tup) ?attrIdx'] =>
          let eq := eval compute in (fin_eq_dec attrIdx attrIdx') in
              match eq with
              | left ?e =>
                let H := fresh in
                assert (GetAttributeRaw (Tuple_DecomposeRawQueryStructure_inj'
                                        (qs_schema := qs_schema)
                                        schemaIdx attrIdx a a_inj tag tup) attrIdx'
                        = a_inj tag (GetAttributeRaw tup  attrIdx')) as H by reflexivity;
                simpl in H; rewrite H; clear H; finish honing
              |right ?e =>
               let H := fresh in
               assert (GetAttributeRaw (Tuple_DecomposeRawQueryStructure_inj'
                                       (qs_schema := qs_schema)
                                       schemaIdx attrIdx a a_inj tag tup) attrIdx'
                       = GetAttributeRaw tup attrIdx') as H by reflexivity;
               simpl in H; rewrite H; clear H; finish honing
              end
        end]
  end.
