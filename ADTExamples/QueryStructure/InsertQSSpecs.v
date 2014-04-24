Require Import List String Ensembles
        ADTNotation Program QueryStructureSchema QueryStructure.

(* Definitions for updating query structures. *)

Definition QSInsertSpec
           (qs : QueryStructureHint)
           (idx : _)
           (tup : Tuple (schemaHeading (QSGetNRelSchema _ idx)))
           (qs' : UnConstrQueryStructure qsSchemaHint)
: Prop :=
  (* All of the relations with a different index are untouched
     by insert. *)
  (forall idx',
     idx <> idx' ->
     GetUnConstrRelation qsHint idx' = GetUnConstrRelation qs' idx') /\
  (* If [tup] is consistent with the schema constraints and the
     cross-relation constraints, it is included in the relation
     indexed by [idx] after insert; that relation is unspecified if
     [tup] does not satisfy either set of constraints. *)
  schemaConstraints (QSGetNRelSchema qsSchemaHint idx) tup
  -> (forall idx',
        BuildQueryStructureConstraints
          qsSchemaHint idx idx' tup (GetUnConstrRelation qsHint idx'))
  -> (forall idx' tup',
        idx' <> idx ->
        BuildQueryStructureConstraints
          qsSchemaHint idx' idx tup' (tup :: (GetUnConstrRelation qsHint idx)))
  -> List.In (bindex idx) (map relName (qschemaSchemas qsSchemaHint))
  -> GetUnConstrRelation qs' idx = tup :: GetUnConstrRelation qsHint idx.

Notation "'Insert' b 'into' idx " :=
  (Bind (Pick (QSInsertSpec _ idx b))
        (fun r' => Pick (fun r => r' = DropQSConstraints r)))
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

  (*Program Definition Insert_Valid
             (qsSchema : QueryStructureSchema)
             (qs : QueryStructure qsSchema)
             (idx : _)
             (tup : Tuple (QSGetNRelSchemaHeading qsSchema idx))
             (schConstr : schemaConstraints (QSGetNRelSchema qsSchema idx) tup)
             (qsConstr : forall idx',
                           BuildQueryStructureConstraints qsSchema idx idx' tup (GetRelation qs idx'))
             (qsConstr' : forall idx',
                            idx' <> idx ->
                            forall tup',
                            BuildQueryStructureConstraints qsSchema idx' idx tup' (tup :: (GetRelation qs idx)))
  : QueryStructure qsSchema :=
    {| rels :=
         replace_BoundedIndex _ (rels qs) idx
                       {| rel := (tup :: (GetRelation qs idx))|}
    |}.
  Next Obligation.
    simpl in *; intuition; subst; eauto.
    eapply ((ith_Bounded _ (rels qs) idx ));
      eassumption.
  Qed.
  Next Obligation.
    destruct ((bindex idx') == (bindex idx)); subst; simpl in *; intuition.
    - destruct (findIndex_In_dec NamedSchema_eq (bindex idx) (qschemaSchemas qsSchema)) as [NIn_a | [a [In_a a_eq] ] ].
      + rewrite replace_indexBounded_NIn in *; auto.
      + erewrite ith_default_replace' in *; simpl; eauto.
    - destruct (findIndex_In_dec NamedSchema_eq idx (qschemaSchemas qsSchema)) as [NIn_a | [a [In_a a_eq] ] ].
      + rewrite replace_index_NIn in *; auto.
      + destruct (idx0 == idx); subst; simpl in *; intuition.
        * erewrite ith_default_replace' in H0; eauto; simpl in *.
          rewrite ith_default_replace; eauto.
          intuition; subst; eauto.
        * rewrite ith_default_replace in *; eauto.
  Qed. *)

  Definition DecideableSB (P : Prop) := {P} + {~P}.

  Definition SchemaConstraints_dec qsSchema idx tup :=
    DecideableSB (schemaConstraints (QSGetNRelSchema qsSchema idx) tup).

  Definition QSSchemaConstraints_dec qsSchema qs idx tup :=
    DecideableSB
      (forall idx',
         BuildQueryStructureConstraints qsSchema idx idx' tup (GetRelation qs idx')).

  Definition QSSchemaConstraints_dec' qsSchema qs idx tup :=
    DecideableSB
      (forall idx',
         idx' <> idx ->
         forall tup',
                BuildQueryStructureConstraints qsSchema idx' idx tup' (tup :: (GetRelation qs idx))).

  (*Lemma QSInsertSpec_refine :
    forall qsSchema qs idx tup default,
      refine
        (Pick (QSInsertSpec {| qsHint := qs |} idx tup))
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

  Lemma refine_Any_DecideableSB_True
  : refine (Any (DecideableSB True)) (ret (left I)).
  Proof.
    repeat constructor.
  Qed.

  (* Infrastructure for Inserting into QueryStructures built using
     BuildQueryStructure*)

  Program Fixpoint DecideableSB_Comp (A : Type)
          (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
          (Bound : list A)
          (P : Ensemble A)
          (ValidBound : forall a, ~ List.In a Bound -> P a)
          {struct Bound}
  : Comp (DecideableSB (forall a : A, P a)) :=
    match Bound as Bound'
          return (forall a, ~ List.In a Bound' -> P a)
                 -> _ with
      | nil => fun ValidBound' => ret (left (fun a => ValidBound' a (id)))
      | cons a Bound' => fun ValidBound' =>
                           (Bind (Any (DecideableSB (P a)))
                                 (fun Pa =>
                                    if Pa
                                    then
                                      (DecideableSB_Comp A_eq_dec Bound' P)
                                        (fun a0 => if A_eq_dec a a0 then _ else _)
                                    else ret (right (fun H' => _ (H' _)))))
    end ValidBound.
  Next Obligation.
    apply ValidBound'; intuition.
  Defined.

  Definition ValidBound_DecideableSB_Comp
             qsSchema
             (qs : forall idx : string,
                     list
                       (Tuple
                          (QSGetNRelSchemaHeading qsSchema idx)))
             idx
             (tup : Tuple (QSGetNRelSchemaHeading qsSchema idx))
  : forall a : string,
      ~ List.In a (map relName (qschemaSchemas qsSchema)) ->
      (fun idx' : string =>
         BuildQueryStructureConstraints qsSchema
           idx idx' tup (qs idx')) a.
  Proof.
    destruct qsSchema as [namedSchemas constraints]; simpl in *.
    simpl in *; induction constraints;
    unfold BuildQueryStructureConstraints;  simpl; auto; intros.
    destruct a; destruct x; simpl in *.
    unfold BuildQueryStructureConstraints',
    BuildQueryStructureConstraints_cons,
    BuildQueryStructureConstraints_cons_obligation_1 in *;
      simpl in *.
    destruct (string_dec s idx); try (apply IHconstraints; eauto; fail).
    destruct (string_dec s0 a0); try (apply IHconstraints; eauto; fail).
    destruct e; destruct e0.
    unfold eq_sym, eq_rect; simpl.
    destruct (in_dec string_dec s (map relName namedSchemas)); auto.
    destruct (in_dec string_dec s0 (map relName namedSchemas)); tauto.
  Qed.

  Definition ValidBound_DecideableSB_Comp'
             qsSchema
             (qs : forall idx : string,
                     list
                       (Tuple
                          (QSGetNRelSchemaHeading qsSchema idx)))
             idx
             (tup : Tuple (QSGetNRelSchemaHeading qsSchema idx))
  : forall a : string,
      ~ List.In a (map relName (qschemaSchemas qsSchema)) ->
      a <> idx ->
      forall
        tup' : Tuple (QSGetNRelSchemaHeading qsSchema a),
        BuildQueryStructureConstraints qsSchema
                                       a idx tup' (tup :: qs idx).
  Proof.
    destruct qsSchema as [namedSchemas constraints]; simpl in *.
    simpl in *; induction constraints;
    unfold BuildQueryStructureConstraints;  simpl; auto; intros.
    destruct a; destruct x; simpl in *.
    unfold BuildQueryStructureConstraints,
    BuildQueryStructureConstraints_cons,
    BuildQueryStructureConstraints_cons_obligation_1 in *;
      simpl in *.
    destruct (string_dec s a0); try (apply IHconstraints; eauto; fail).
    destruct (string_dec s0 idx); try (apply IHconstraints; eauto; fail).
    destruct e; destruct e0.
    unfold eq_sym, eq_rect; simpl.
    destruct (in_dec string_dec s (map relName namedSchemas)); auto.
    destruct (in_dec string_dec s0 (map relName namedSchemas)); tauto.
  Qed.

  Definition Iterate_Constraints_dec
             qsSchema
             (qs : QueryStructure qsSchema)
             idx
             (tup : Tuple (QSGetNRelSchemaHeading qsSchema idx))
    := DecideableSB_Comp
         string_dec
         (map relName (qschemaSchemas qsSchema))
         (fun idx' =>
            BuildQueryStructureConstraints
              qsSchema idx idx' tup (GetRelation qs idx'))
         (ValidBound_DecideableSB_Comp qsSchema _
                                       idx tup ).

  Set Printing All.

  Lemma DecideableSB_Comp_refine :
  forall qsSchema
         (qs : QueryStructure qsSchema)
         idx
         (tup : Tuple (QSGetNRelSchemaHeading qsSchema idx)),
      refine
      (Any (QSSchemaConstraints_dec qs idx tup))
      (Iterate_Constraints_dec qs idx tup).
  Proof.
    intros.
    repeat econstructor.
  Qed.

  Definition Iterate_Constraints_dec'
             qsSchema
             (qs : QueryStructure qsSchema)
             idx
             (tup : Tuple (QSGetNRelSchemaHeading qsSchema idx))
    := DecideableSB_Comp
         string_dec
         (map relName (qschemaSchemas qsSchema))
         (fun idx' =>
            idx' <> idx ->
            forall tup' : Tuple (QSGetNRelSchemaHeading qsSchema idx'),
            BuildQueryStructureConstraints
              qsSchema idx' idx tup' (tup :: (GetRelation qs idx)))
         (ValidBound_DecideableSB_Comp' qsSchema _ tup ).

  Lemma DecideableSB_Comp'_refine :
  forall qsSchema
         (qs : QueryStructure qsSchema)
         idx
         (tup : Tuple (QSGetNRelSchemaHeading qsSchema idx)),
      refine
      (Any (QSSchemaConstraints_dec' qs idx tup))
      (Iterate_Constraints_dec' qs idx tup).
  Proof.
    intros.
    repeat econstructor.
  Qed.

  Lemma QSInsertSpec_BuildQuerySpec_refine :
    forall qsSchema
           (qs : QueryStructure qsSchema)
           idx tup default,
      refine
        (Pick (QSInsertSpec {| qsHint := qs |} idx tup))
        (schConstr <- Any (SchemaConstraints_dec _ idx tup);
         qsConstr <- (Iterate_Constraints_dec qs idx tup);
         qsConstr' <- (Iterate_Constraints_dec' qs idx tup);
         match schConstr, qsConstr, qsConstr' with
           | left schConstr, left qsConstr, left qsConstr' =>
             ret (Insert_Valid qs tup schConstr qsConstr qsConstr')
           | _, _, _ => default
         end).
  Proof.
    intros.
    rewrite QSInsertSpec_refine.
    setoid_rewrite DecideableSB_Comp'_refine;
      setoid_rewrite DecideableSB_Comp_refine.
    reflexivity.
  Qed.

  (* Old Solution
  Program Fixpoint DecideableSB_finite (A : Type)
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
        (Bound : list A)
        (P : Ensemble A)
        (ValidBound : forall a, ~ List.In a Bound -> P a)
        (Bound_dec : ilist (fun a => DecideableSB (P a)) Bound)
        {struct Bound}
  : DecideableSB (forall a : A, P a) :=
    match Bound as Bound'
          return
          (forall a, ~ List.In a Bound' -> P a)
          -> ilist (fun a => DecideableSB (P a)) Bound'
          -> DecideableSB (forall a : A, P a) with
      | nil => fun ValidBound Bound_dec => left _
      | cons a Bound' =>
        fun ValidBound Bound_dec =>
          match (ilist_hd Bound_dec) with
            | left P_a =>
              (fun H' => _)
                (DecideableSB_finite A_eq_dec P _ (ilist_tail Bound_dec))
            | right P_a => right _
          end
    end ValidBound Bound_dec.
  Next Obligation.
    destruct (A_eq_dec a a0); subst; eauto.
    apply ValidBound0; simpl; tauto.
  Defined.

  Program Fixpoint DecideableSB_finiteComp (A : Type)
          (Bound : list A)
          (P : Ensemble A)
  : Comp (ilist (fun a => DecideableSB (P a)) Bound) :=
    match Bound with
      | nil => ret (inil _)
      | cons a Bound' =>
        (Pa <- Any (DecideableSB (P a));
          PBound' <- DecideableSB_finiteComp Bound' P;
          ret (icons _ Pa PBound'))%comp
    end.

Definition DecideableSB_Comp (A : Type)
          (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
          (Bound : list A)
          (P : Ensemble A)
          (ValidBound : forall a, ~ List.In a Bound -> P a)
  : Comp (DecideableSB (forall a : A, P a)) :=
    (x <- DecideableSB_finiteComp Bound P;
    ret (DecideableSB_finite A_eq_dec P ValidBound x))%comp. *)
*)
End InsertRefinements.

Create HintDb refine_keyconstraints discriminated.
(*Hint Rewrite refine_Any_DecideableSB_True : refine_keyconstraints.*)
