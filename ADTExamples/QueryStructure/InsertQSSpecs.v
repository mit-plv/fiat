Require Import List String Ensembles
        ADTNotation Program QueryStructureSchema QueryStructure.

(* Definitions for updating query structures. *)

Definition QSInsertSpec
           {QSSchema}
           (qs : QueryStructure QSSchema)
           (idx : string)
           (tup : Tuple (schemaHeading (GetNamedSchema _ idx)))
           (qs' : QueryStructure QSSchema)
: Prop :=
  (* All of the relations with a different index are untouched
     by insert. *)
  (forall idx',
     idx <> idx' ->
     GetRelation qs idx' = GetRelation qs' idx') /\
  (* If [tup] is consistent with the schema constraints and the
     cross-relation constraints, it is included in the relation
     indexed by [idx] after insert; that relation is unspecified if
     [tup] does not satisfy either set of constraints. *)
  schemaConstraints (GetNamedSchema QSSchema idx) tup
  -> (forall idx',
        qschemaConstraints QSSchema idx idx' tup (GetRelation  qs idx'))
  -> (forall idx' tup',
        idx' <> idx ->
        qschemaConstraints QSSchema idx' idx tup' (tup :: (GetRelation qs idx)))
  -> List.In idx (map relName (qschemaSchemas QSSchema))
  -> GetRelation qs' idx = tup :: GetRelation qs idx.

Notation "'Insert' b 'into' idx " :=
  (QSInsertSpec qsHint idx%string b)
    (at level 80) : QuerySpec_scope.

(* Facts about insert. We'll probably need to extract these to their
    own file at some point. *)

Section InsertRefinements.

  (* Definition Insert_Valid_obligation_0 *)
  (*            (qsSchema : QueryStructureSchema) *)
  (*            (idx idx' : string) *)
  (*            (tup : Tuple (schemaHeading (GetNamedSchema qsSchema idx))) *)
  (*            (idx_eq : idx = idx') *)
  (* : Tuple (schemaHeading (GetNamedSchema qsSchema idx')). *)
  (* Proof. *)
  (*   rewrite <- idx_eq. *)
  (*   eassumption. *)
  (* Defined. *)

  (* Arguments Insert_Valid_obligation_0 _ _ _ _ _ / _ . *)

  Lemma NamedSchema_eq_neq
  : forall idx idx' a,
      idx <> idx'
      -> NamedSchema_eq a idx = true
      -> NamedSchema_eq a idx' = false.
  Proof.
    unfold NamedSchema_eq; destruct a; simpl.
    repeat find_if_inside; congruence.
  Qed.

  Lemma NamedSchema_eq_eq :
    forall idx a,
      relName a = idx
      -> NamedSchema_eq a idx = true.
  Proof.
    intros; unfold NamedSchema_eq; destruct a; subst; simpl.
    caseEq (string_dec relName relName); eauto.
  Qed.

  Hint Resolve AC_eq_nth_In AC_eq_nth_NIn NamedSchema_eq_neq
       NamedSchema_eq_eq crossConstr.

  Program Definition Insert_Valid
             (qsSchema : QueryStructureSchema)
             (qs : QueryStructure qsSchema)
             (idx : string)
             (tup : Tuple (schemaHeading (GetNamedSchema qsSchema idx)))
             (schConstr : schemaConstraints (GetNamedSchema qsSchema idx) tup)
             (qsConstr : forall idx',
                           qschemaConstraints qsSchema idx idx' tup (GetRelation qs idx'))
             (qsConstr' : forall idx' tup',
                            idx' <> idx ->
                            qschemaConstraints qsSchema idx' idx tup' (tup :: (GetRelation qs idx)))
  : QueryStructure qsSchema :=
    {| rels :=
         replace_index NamedSchema_eq (rels qs) idx _
                       {| rel := (tup :: (GetRelation qs idx))|}
    |}.
  Next Obligation.
    simpl in *; intuition; subst; eauto.
    eapply ((ith NamedSchema_eq (rels qs) idx _ _));
      eassumption.
  Qed.
  Next Obligation.
    destruct (idx' == idx); subst; simpl in *; intuition.
    - destruct (findIndex_In_dec NamedSchema_eq idx (qschemaSchemas qsSchema)) as [NIn_a | [a [In_a a_eq] ] ].
      + rewrite replace_index_NIn in *; auto.
      + erewrite ith_replace' in *; simpl; eauto.
    - destruct (findIndex_In_dec NamedSchema_eq idx (qschemaSchemas qsSchema)) as [NIn_a | [a [In_a a_eq] ] ].
      + rewrite replace_index_NIn in *; auto.
      + destruct (idx0 == idx); subst; simpl in *; intuition.
        * erewrite ith_replace' in H0; eauto; simpl in *.
          rewrite ith_replace; eauto.
          intuition; subst; eauto.
        * rewrite ith_replace in *; eauto.
  Qed.

  Definition DecideableSB (P : Prop) := {P} + {~P}.

  Definition SchemaConstraints_dec qsSchema idx tup :=
    DecideableSB (schemaConstraints (GetNamedSchema qsSchema idx) tup).

  Definition QSSchemaConstraints_dec qsSchema qs idx tup :=
    DecideableSB
      (forall idx',
         qschemaConstraints qsSchema idx idx' tup (GetRelation qs idx')).

  Definition QSSchemaConstraints_dec' qsSchema qs idx tup :=
    DecideableSB
      (forall idx' tup',
         idx' <> idx ->
         qschemaConstraints qsSchema idx' idx tup' (tup :: (GetRelation qs idx))).

  Definition Any (T : Type) := Pick (fun _ : T => True).

  Lemma QSInsertSpec_refine :
    forall qsSchema qs idx tup default,
      refine
        {x | QSInsertSpec qs idx tup x}%comp
        (schConstr <- Any (SchemaConstraints_dec qsSchema idx tup);
         qsConstr <- Any (QSSchemaConstraints_dec qs idx tup);
         qsConstr' <- Any (QSSchemaConstraints_dec' qs idx tup);
         match schConstr, qsConstr, qsConstr' with
           | left schConstr, left qsConstr, left qsConstr' =>
             ret (Insert_Valid qs tup schConstr qsConstr qsConstr')
           | _, _, _ => default
         end).
  Proof.
    unfold Any; intros qsSchema qs idx tup default v Comp_v.
    repeat (apply_in_hyp computes_to_inv; destruct_ex; intuition).
    destruct x; destruct x0; destruct x1;
    econstructor; unfold QSInsertSpec; simpl; subst; intuition.
    unfold Insert_Valid, GetRelation; simpl.
    destruct (proj1 (@in_map_iff _ _ relName _ _) H5) as [a' [a'_eq In_a' ] ].
    erewrite ith_replace'; simpl; eauto.
  Qed.

End InsertRefinements.
