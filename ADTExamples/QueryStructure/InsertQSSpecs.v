Require Import List String Ensembles Arith
        ADTNotation Program QueryStructureSchema QueryStructure.

(* Definitions for updating query structures. *)

(* 'Inserting' a Tuple [tup] into a relation [R] represented
    as an ensemble produces a new ensemble that holds for any
    Tuple [tup'] equal to [tup] or which is already in [R]. *)
Definition RelationInsert
           {Heading}
           (tup : @Tuple Heading)
           (R : Ensemble _)
           (tup' : @Tuple Heading) :=
  tup' = tup \/ R tup'.

Definition SatisfiesSchemaConstraints
           {qsSchema} Ridx tup tup' :=
    schemaConstraints (QSGetNRelSchema qsSchema Ridx) tup tup'.

Definition SatisfiesCrossRelationConstraints
           {qsSchema} Ridx Ridx' tup R :=
  BuildQueryStructureConstraints qsSchema Ridx Ridx' tup R.

Definition QSInsertSpec
           (qs : QueryStructureHint)
           (Ridx : _)
           (tup : @Tuple (schemaHeading (QSGetNRelSchema _ Ridx)))
           (qs' : QueryStructure qsSchemaHint)
: Prop :=
  (* All of the relations with a different index are untouched
     by insert. *)
  (forall Ridx',
     Ridx <> Ridx' ->
     GetRelation qsHint Ridx' = GetRelation qs' Ridx') /\
  (* If [tup] is consistent with the schema constraints, *)
  (SatisfiesSchemaConstraints Ridx tup tup)
  -> (forall tup', GetRelation qsHint Ridx tup' ->
                SatisfiesSchemaConstraints Ridx tup tup')
  -> (forall tup', GetRelation qsHint Ridx tup' ->
    SatisfiesSchemaConstraints Ridx tup' tup)
  (* and [tup] is consistent with the other tables per the cross-relation
     constraints, *)
  -> (forall Ridx', SatisfiesCrossRelationConstraints Ridx Ridx' tup (GetRelation qsHint Ridx'))
  (* and each tuple in the other tables is consistent with the
     table produced by inserting [tup] into the relation indexed by [Ridx], *)
  -> (forall Ridx',
        Ridx' <> Ridx ->
        forall tup',
        (GetRelation qsHint Ridx') tup'
        -> SatisfiesCrossRelationConstraints
             Ridx' Ridx tup'
             (RelationInsert tup (GetRelation qsHint Ridx)))
  (* [tup] is included in the relation indexed by [Ridx] after insert.
   The behavior of insertion is unspecified otherwise. *)
  -> (forall t, GetRelation qs' Ridx t <->
               (RelationInsert tup (GetRelation qsHint Ridx) t)).

Notation "'Insert' b 'into' Ridx " :=
  (Pick (QSInsertSpec _ Ridx b))
    (at level 80) : QuerySpec_scope.

(* Facts about insert. We'll probably need to extract these to their
    own file at some point. *)

Section InsertRefinements.

  (* Definition Insert_Valid_obligation_0 *)
  (*            (qsSchema : QueryStructureSchema) *)
  (*            (Ridx Ridx' : string) *)
  (*            (tup : Tuple (schemaHeading (GetNamedSchema qsSchema Ridx))) *)
  (*            (Ridx_eq : Ridx = Ridx') *)
  (* : Tuple (schemaHeading (GetNamedSchema qsSchema Ridx')). *)
  (* Proof. *)
  (*   rewrite <- Ridx_eq. *)
  (*   eassumption. *)
  (* Defined. *)

  (* Arguments Insert_Valid_obligation_0 _ _ _ _ _ / _ . *)

  Lemma NamedSchema_eq_neq
  : forall Ridx Ridx' a,
      Ridx <> Ridx'
      -> NamedSchema_eq a Ridx = true
      -> NamedSchema_eq a Ridx' = false.
  Proof.
    unfold NamedSchema_eq; destruct a; simpl.
    repeat find_if_inside; congruence.
  Qed.

  Lemma NamedSchema_eq_eq :
    forall Ridx a,
      relName a = Ridx
      -> NamedSchema_eq a Ridx = true.
  Proof.
    intros; unfold NamedSchema_eq; destruct a; subst; simpl.
    caseEq (string_dec relName relName); eauto.
  Qed.

  Hint Resolve AC_eq_nth_In AC_eq_nth_NIn NamedSchema_eq_neq
       NamedSchema_eq_eq crossConstr.
  Hint Unfold SatisfiesCrossRelationConstraints
       SatisfiesSchemaConstraints.

  Definition UpdateRelation
             (qsSchema : QueryStructureSchema)
             (rels : ilist (fun ns => Relation (relSchema ns))
                           (qschemaSchemas qsSchema))
             (Ridx : _)
             newRel :
    ilist (fun ns => Relation (relSchema ns))
          (qschemaSchemas qsSchema) :=
    replace_BoundedIndex relName rels Ridx newRel.

  Program
    Definition Insert_Valid
    (qsSchema : QueryStructureSchema)
    (qs : QueryStructure qsSchema)
    (Ridx : _)
    (tup : @Tuple (QSGetNRelSchemaHeading qsSchema Ridx))
    (schConstr : forall tup',
                   GetRelation qs Ridx tup' ->
                   SatisfiesSchemaConstraints Ridx tup tup')
    (schConstr' : forall tup',
                   GetRelation qs Ridx tup' ->
                   SatisfiesSchemaConstraints Ridx tup' tup)
    (schConstr_self :
       schemaConstraints (QSGetNRelSchema qsSchema Ridx) tup tup)
    (qsConstr : forall Ridx',
                  SatisfiesCrossRelationConstraints Ridx Ridx' tup (GetRelation qs Ridx'))
    (qsConstr' : forall Ridx',
                   Ridx' <> Ridx ->
                   forall tup',
                     GetRelation qs Ridx' tup'
                     -> SatisfiesCrossRelationConstraints
                     Ridx' Ridx tup'
                     (RelationInsert tup (GetRelation qs Ridx)))
  : QueryStructure qsSchema :=
    {| rels :=
         UpdateRelation _ (rels qs) Ridx {| rel := RelationInsert tup (GetRelation qs Ridx)|}
    |}.
  Next Obligation.
    unfold SatisfiesSchemaConstraints in *.
    unfold RelationInsert in *; simpl in *; intuition; subst; eauto.
    eapply ((ith_Bounded _ (rels qs) Ridx )); eassumption.
  Defined.
  Next Obligation.
    unfold SatisfiesCrossRelationConstraints, UpdateRelation in *;
    destruct (BoundedString_eq_dec Ridx idx'); subst.
    - rewrite ith_replace_BoundIndex_eq; simpl.
      rewrite ith_replace_BoundIndex_neq in H0; eauto using string_dec.
    - rewrite ith_replace_BoundIndex_neq in *; eauto using string_dec.
      destruct (BoundedString_eq_dec Ridx idx); subst.
      rewrite ith_replace_BoundIndex_eq in H0; simpl in *; eauto.
      unfold RelationInsert in H0; intuition; subst; eauto.
      rewrite ith_replace_BoundIndex_neq in H0; eauto using string_dec.
  Qed.

  (*Definition DecideableSB (P : Prop) := {P} + {~P}.

  Definition SchemaConstraints_dec qsSchema Ridx tup :=
    DecideableSB (schemaConstraints (QSGetNRelSchema qsSchema Ridx) tup).

  Definition QSSchemaConstraints_dec qsSchema qs Ridx tup :=
    DecideableSB
      (forall Ridx',
         BuildQueryStructureConstraints qsSchema Ridx Ridx' tup (GetRelation qs Ridx')).

  Definition QSSchemaConstraints_dec' qsSchema qs Ridx tup :=
    DecideableSB
      (forall Ridx',
         Ridx' <> Ridx ->
         forall tup',
                BuildQueryStructureConstraints qsSchema Ridx' Ridx tup'
                                               (RelationInsert tup (GetRelation qs Ridx))). *)

  Definition decides (b : bool) (P : Prop) := if b then P else ~ P.

  Lemma app_assoc
        (A : Type)
        (l m n : list A)
  : l ++ m ++ n = (l ++ m) ++ n.
  Proof.
    induction l; simpl; auto.
    rewrite IHl; reflexivity.
  Defined.

  Lemma app_cons {A : Set}:
    forall (a : A) As As',
      As ++ (a :: As') = (As ++ [a]) ++ As'.
  Proof.
    intros; rewrite <- app_assoc; reflexivity.
  Defined.

  Definition Ensemble_BoundedIndex_app_cons {A : Set}
    (a : A)
    (As As' : list A)
    (P : Ensemble (BoundedIndex (As ++ a :: As')))
  : Ensemble (BoundedIndex ((As ++ [a]) ++ As')).
    rewrite app_cons in P; exact P.
  Defined.

  Definition BoundedIndex_app_cons {A : Set}
    (a : A)
    (As As' : list A)
    (a' : BoundedIndex (As ++ a :: As'))
  : BoundedIndex ((As ++ [a]) ++ As').
    rewrite app_cons in a'; exact a'.
  Defined.

  Lemma ibound_BoundedIndex_app_cons {A : Set}
    (a : A)
    (As As' : list A)
    (a' : BoundedIndex (As ++ a :: As'))
  : ibound a' = ibound (BoundedIndex_app_cons a As As' a').
  Proof.
    unfold BoundedIndex_app_cons, eq_rec, eq_rect; simpl.
    destruct (app_cons a As As'); reflexivity.
  Qed.

  Program Fixpoint Iterate_Ensemble_BoundedIndex'
          {A : Set}
          (Visited Remaining : list A)
          (P : Ensemble (BoundedIndex (Visited ++ Remaining))) : Prop :=
    match Remaining with
        | [] => True
        | a :: Remaining' =>
          P {| bindex := a;
               indexb := {| ibound := List.length Visited;
                            boundi := _ |} |}
          /\ Iterate_Ensemble_BoundedIndex' (Visited ++ (a :: nil)) Remaining' _
    end.
  Next Obligation.
    clear P; induction Visited; simpl; auto.
  Defined.
  Next Obligation.
    exact (Ensemble_BoundedIndex_app_cons _ _ _ P).
  Defined.

  Lemma Ensemble_BoundedIndex_app_equiv {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
        (a : A) (As As' : list A)
        (P : Ensemble (BoundedIndex (As ++ a :: As')))
  : forall idx idx' n nth nth',
      P {| bindex := idx; indexb := {| ibound := n; boundi := nth |}|} <->
      Ensemble_BoundedIndex_app_cons a As As' P
                                     {| bindex := idx'; indexb := {| ibound := n; boundi := nth' |}|}.
  Proof.
    split; unfold Ensemble_BoundedIndex_app_cons, BoundedIndex_app_cons, app_cons; simpl;
    unfold eq_rec, eq_rect, eq_ind, eq_rect; destruct (app_assoc As [a] As'); auto;
    generalize (indexb_ibound_eq
            {| bindex := idx'; indexb := {| ibound := n; boundi := nth' |}|}
            {| bindex := idx; indexb := {| ibound := n; boundi := nth |}|}
            eq_refl); simpl; intros; subst;
    erewrite (eq_proofs_unicity_Opt_A A_eq_dec _); eauto.
  Qed.

  Lemma BoundedIndex_app_cons_nth_eq {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall
      (As As' : list A)
      a a' a'' n nth nth',
      {| bindex := a; indexb := {| ibound := n; boundi := nth |}|} =
      BoundedIndex_app_cons a' As As' {| bindex := a''; indexb := {| ibound := n; boundi := nth' |}|}.
  Proof.
    intros.
    unfold BoundedIndex_app_cons, eq_rec, eq_rect; simpl.
    destruct (app_cons a' As As').
    generalize (indexb_ibound_eq
            {| bindex := a''; indexb := {| ibound := n; boundi := nth' |}|}
            {| bindex := a; indexb := {| ibound := n; boundi := nth |}|}
               eq_refl); simpl; intros; subst.
    erewrite (eq_proofs_unicity_Opt_A A_eq_dec nth'); reflexivity.
  Qed.

  Lemma Ensemble_BoundedIndex_nth_eq {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall
      (As : list A)
      (P : Ensemble (BoundedIndex As))
      a a' n nth nth',
      P {| bindex := a; indexb := {| ibound := n; boundi := nth |}|} ->
      P {| bindex := a'; indexb := {| ibound := n; boundi := nth' |}|}.
  Proof.
    intros;
    generalize (indexb_ibound_eq
            {| bindex := a'; indexb := {| ibound := n; boundi := nth' |}|}
            {| bindex := a; indexb := {| ibound := n; boundi := nth |}|}
               eq_refl); simpl; intros; subst.
    erewrite (eq_proofs_unicity_Opt_A A_eq_dec nth'); eassumption.
  Qed.

  Lemma nth_error_app {A : Set} :
    forall (a : A) (As As' : list A) n,
      nth_error As n = Some a ->
      nth_error (As ++ As') n = Some a.
  Proof.
    induction As; destruct n; simpl; intros; try discriminate; auto.
  Defined.

  Lemma Ensemble_nth_error_app
        {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall a As As' nth'
      (P : Ensemble (BoundedIndex (As ++ (a :: As')))),
      P {| bindex := a;
           indexb := {| ibound := Datatypes.length As;
                        boundi := nth' |} |}
      -> (forall (a' : A) (n : nat) (nth : nth_error As n = Some a'),
      P {| bindex := a';
           indexb := {|
                      ibound := n;
                      boundi := nth_error_app As (a :: As') n nth |} |})
      -> forall (a' : A) (n : nat) (nth : nth_error (As ++ [a]) n = Some a'),
           Ensemble_BoundedIndex_app_cons a As As' P
                                          {| bindex := a';
                                             indexb := {| ibound := n;
                                                          boundi := nth_error_app (As ++ [a]) As' n nth |} |}.
  Proof.
    intros.
    destruct (eq_nat_dec (List.length As) n ); subst.
    - rewrite (BoundedIndex_app_cons_nth_eq
                 A_eq_dec As As' _ (List.length As)
                 (nth_error_app (As ++ [a]) As'
                                (Datatypes.length As) nth)
                 nth').
      erewrite <- BoundedIndex_app_cons_nth_eq; eauto.
      eapply Ensemble_BoundedIndex_app_equiv; eauto.
    - assert (nth_error As n = Some a') by
          (revert n nth n0; clear; induction As; destruct n; simpl; intros;
           try congruence;
           [destruct n; discriminate
           | eauto]).
      generalize (H0 _ _ H1); intros.
      erewrite (BoundedIndex_app_cons_nth_eq
                 A_eq_dec As As' _ n
                 (nth_error_app (As ++ [a]) As'
                                n nth)).
      erewrite <- BoundedIndex_app_cons_nth_eq; eauto.
      eapply Ensemble_BoundedIndex_app_equiv; eauto.
      Grab Existential Variables.
      rewrite <- app_assoc; simpl; apply nth_error_app; eassumption.
      apply nth_error_app; eassumption.
      apply nth_error_app; eassumption.
  Qed.

  Lemma Iterate_Ensemble_equiv' {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P : Ensemble (BoundedIndex (Visited ++ Remaining))),
      (forall a n (nth : nth_error Visited n = Some a),
         P {| bindex := a;
              indexb := {| ibound := n;
                           boundi := nth_error_app _ _ _ nth |} |})
      -> (Iterate_Ensemble_BoundedIndex' Visited Remaining P ->
         forall idx, P idx).
    intros; destruct idx as [idx [n nth_n] ]; simpl in *.
    revert Visited P H H0 idx n nth_n; induction Remaining; simpl; intros.
    - eapply Ensemble_BoundedIndex_nth_eq with (a := idx); auto.
    - split_and.
      assert (nth_error ((Visited ++ [a]) ++ Remaining) n = Some idx)
        as nth_n'
          by (rewrite <- app_assoc; simpl; assumption).
      generalize (IHRemaining _ _ (Ensemble_nth_error_app A_eq_dec _ _ _ P H1 H) H2 _ _ nth_n').
      unfold Ensemble_BoundedIndex_app_cons, eq_rect; destruct (app_cons a Visited Remaining).
      intros; erewrite (eq_proofs_unicity_Opt_A A_eq_dec nth_n); eauto.
      Grab Existential Variables.
      rewrite app_nil_r in nth_n; assumption.
  Qed.

  Lemma Iterate_Ensemble_equiv'' {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P : Ensemble (BoundedIndex (Visited ++ Remaining))),
      (forall idx, P idx)
      -> Iterate_Ensemble_BoundedIndex' Visited Remaining P.
    induction Remaining; simpl; auto.
    intros; split; eauto.
    eapply IHRemaining; intros; eauto.
    intros; destruct idx as [idx [n nth_n] ]; simpl in *.
    eapply Ensemble_BoundedIndex_app_equiv; eauto.
    Grab Existential Variables.
    rewrite <- app_assoc in nth_n; simpl in nth_n; eassumption.
  Qed.

  Definition Iterate_Ensemble_BoundedIndex
          (Bound : list string)
          (P : Ensemble (BoundedIndex Bound)) : Prop :=
    Iterate_Ensemble_BoundedIndex' [] Bound P.

  Program Lemma refine_Iterate_Ensemble {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (As : list string)
           (P : Ensemble (BoundedIndex As)),
      refine {b | decides b (forall idx : BoundedIndex As, P idx)}
             {b | decides b (@Iterate_Ensemble_BoundedIndex As P)}.
  Proof.
    intros; eapply refine_pick_pick.
    intros; destruct x; simpl in *.
    intros; eapply Iterate_Ensemble_equiv' with (Visited := []);
    eauto using string_dec.
    destruct n; simpl; intros; discriminate.
    unfold not; intros; apply H.
    apply Iterate_Ensemble_equiv'';
      auto using string_dec.
  Qed.

  Lemma QSInsertSpec_refine' :
    forall qsSchema (qs : QueryStructure qsSchema) Ridx tup default,
      refine
           (Pick (QSInsertSpec {| qsHint := qs |} Ridx tup))
           (schConstr_self <-
                           {b |
                            decides b
                         (SatisfiesSchemaConstraints Ridx tup tup)};
             schConstr <-
                      {b |
                       decides
                         b
                         (forall tup',
                            GetRelation qs Ridx tup'
                            -> SatisfiesSchemaConstraints Ridx tup tup')};
            schConstr' <-
                      {b |
                       decides
                         b
                         (forall tup',
                            GetRelation qs Ridx tup'
                            -> SatisfiesSchemaConstraints Ridx tup' tup)};
            qsConstr <- {b | decides b
(forall Ridx', SatisfiesCrossRelationConstraints Ridx Ridx' tup (GetRelation qs Ridx'))};
            qsConstr' <- {b | decides
                                b
                                (forall Ridx',
                                   Ridx' <> Ridx ->
                                   forall tup',
                                     (GetRelation qs Ridx') tup'
                                                           -> SatisfiesCrossRelationConstraints
                                       Ridx' Ridx tup'
                                       (RelationInsert tup (GetRelation qs Ridx)))};
            match schConstr_self, schConstr, schConstr', qsConstr, qsConstr' with
              | true, true, true, true, true =>
                {qs' |
                 (forall Ridx',
                    Ridx <> Ridx' ->
                    GetRelation qsHint Ridx' =
                    GetRelation qs' Ridx')
                 /\ forall t,
                      GetRelation qs' Ridx t <->
                      (RelationInsert tup (GetRelation qsHint Ridx) t)
             }

              | _, _ , _, _, _ => default
            end).
  Proof.
    intros qsSchema qs Ridx tup default v Comp_v.
    do 5 (apply_in_hyp computes_to_inv; destruct_ex; split_and);
      destruct x;
      [ destruct x0;
        [ destruct x1;
          [ destruct x2;
            [ destruct x3;
              [ repeat (apply_in_hyp computes_to_inv; destruct_ex; split_and); simpl in *;
                econstructor; unfold QSInsertSpec; eauto |
              ]
            | ]
          | ]
        |  ]
      |  ];
      cbv delta [decides] beta in *; simpl in *;
      repeat (apply_in_hyp computes_to_inv; destruct_ex); eauto;
      econstructor; unfold QSInsertSpec; intros;
      solve [elimtype False; intuition].
  Qed.

  (* So that things play nicely with setoid rewriting *)
  Definition If_Then_Else {A}  (b : bool) (t e : A)
    := if b then t else e.

  Program Fixpoint Iterate_Decide_Comp' (A : Set)
          (Remaining Visited : list A)
          (P : Ensemble (BoundedIndex (Visited ++ Remaining)))
          {struct Remaining }
  : Comp bool :=
    match Remaining with
      | nil => ret true
      | cons a Remaining' =>
        Bind {b' |
              decides b' (P {| bindex := a;
                               indexb := {| ibound := List.length Visited;
                                            boundi := _ |} |})}%comp
             (fun b' =>
                If_Then_Else b'
                             (Iterate_Decide_Comp' Remaining' (Visited ++ [a]) _)
                             (ret false))
    end.
  Next Obligation.
    clear P; induction Visited; simpl; auto.
  Defined.
  Next Obligation.
    exact (Ensemble_BoundedIndex_app_cons _ _ _ P).
  Defined.

  Lemma refine_Iterate_Decided_Ensemble' {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P : Ensemble (BoundedIndex (Visited ++ Remaining))),
      refine {b | decides b (Iterate_Ensemble_BoundedIndex' Visited Remaining P)}
             (Iterate_Decide_Comp' Remaining Visited P).
  Proof.
    induction Remaining; simpl; intros.
    - econstructor; inversion_by computes_to_inv; subst; simpl; auto.
    - econstructor; apply computes_to_inv in H; destruct_ex;
      split_and; inversion_by computes_to_inv; subst.
      destruct x; simpl in *.
      {  destruct v; simpl in *; intuition; intros; eauto.
         - generalize (IHRemaining (Visited ++ [a]) _ _ H1).
           intros; inversion_by computes_to_inv; simpl in *; eauto.
         - generalize (IHRemaining (Visited ++ [a]) _ _ H1).
           intros; inversion_by computes_to_inv; simpl in *; eauto.
      }
      { inversion_by computes_to_inv; subst; simpl; intuition. }
  Qed.

  Lemma decides_True :
    refine {b | decides b True}%comp
           (ret true).
  Proof.
    econstructor; inversion_by computes_to_inv; subst; simpl; auto.
  Qed.

  Lemma decides_2_True (A : Type) (B : A -> Type) :
    refine {b' | decides b' (forall a : A, B a -> True)}%comp
           (ret true).
  Proof.
    econstructor; inversion_by computes_to_inv; subst; simpl; auto.
  Qed.

  Lemma decides_3_True (A B : Type) (C : B -> Type) :
    refine {b' | decides b' (A -> forall b : B, C b -> True)}%comp
           (ret true).
  Proof.
    econstructor; inversion_by computes_to_inv; subst; simpl; auto.
  Qed.

  Lemma decides_neq (A : Type) (B : Prop) (a : A) :
    refine {b' | decides b' (a <> a -> B)}%comp
           (ret true).
  Proof.
    econstructor; inversion_by computes_to_inv; subst; simpl; auto.
    congruence.
  Qed.

  Global Add Parametric Morphism A
  : If_Then_Else
      with signature
      (@eq bool) ==> (@refine A) ==> (@refine A) ==> (@refine A)
        as refine_If_Then_Else_if.
  Proof.
    compute.
    intros; destruct_head bool; intros; eauto.
  Qed.

  Definition Iterate_Decide_Comp
          (Bound : list string)
          (P : Ensemble (BoundedIndex Bound))
  : Comp bool :=
    Iterate_Decide_Comp' Bound [] P.

  Definition Iterate_Decide_Comp_BoundedIndex
  : forall (Bound : list string)
           (P : Ensemble (BoundedIndex Bound)),
      refine {b | decides b (forall Ridx', P Ridx')}
             (Iterate_Decide_Comp P).
  Proof.
    intros.
    setoid_rewrite refine_Iterate_Ensemble; auto using string_dec.
    setoid_rewrite refine_Iterate_Decided_Ensemble'; auto using string_dec.
    reflexivity.
  Qed.

  (* Definition GetRelevantConstraints
             qsSchema
             Ridx
  : list string :=
    map (fun f => bindex (snd (projT1 f)))
        (filter (fun f => if (BoundedIndex_eq_dec string_dec Ridx (fst (projT1 f)))
                          then true
                          else false)
                (qschemaConstraints qsSchema)).

  Definition lift_BoundedIndex
             qsSchema Ridx
             (Ridx' : BoundedIndex (GetRelevantConstraints qsSchema Ridx))
  : BoundedString (map relName (qschemaSchemas qsSchema)). *)


  Lemma QSInsertSpec_refine :
    forall qsSchema (qs : QueryStructure qsSchema) Ridx tup default,
      refine
           (Pick (QSInsertSpec {| qsHint := qs |} Ridx tup))
           (schConstr_self <- {b | decides b
                                           (SatisfiesSchemaConstraints Ridx tup tup)};
             schConstr <-
                      {b |
                       decides
                         b
                         (forall tup',
                            GetRelation qs Ridx tup'
                            -> SatisfiesSchemaConstraints Ridx tup tup')};
            schConstr' <-
                      {b |
                       decides
                         b
                         (forall tup',
                            GetRelation qs Ridx tup'
                            -> SatisfiesSchemaConstraints Ridx tup' tup)};
            qsConstr <- (@Iterate_Decide_Comp _
                                (fun Ridx' =>
                                   SatisfiesCrossRelationConstraints
                                     Ridx Ridx' tup
                                     (GetRelation qsHint Ridx')));
            qsConstr' <- (@Iterate_Decide_Comp _
                                (fun Ridx' =>
                                   Ridx' <> Ridx
                                   -> forall tup',
                                        (GetRelation qsHint Ridx') tup'
                                        -> SatisfiesCrossRelationConstraints
                                       Ridx' Ridx tup'
                                       (RelationInsert tup (GetRelation qs Ridx))));
            match schConstr_self, schConstr, schConstr', qsConstr, qsConstr' with
              | true, true, true, true, true =>
                {qs' |
                 (forall Ridx',
                    Ridx <> Ridx' ->
                    GetRelation qsHint Ridx' =
                    GetRelation qs' Ridx')
                 /\ forall t,
                      GetRelation qs' Ridx t <->
                      (RelationInsert tup (GetRelation qsHint Ridx) t)
             }

              | _, _, _, _, _ => default
            end).
  Proof.
    intros.
    rewrite QSInsertSpec_refine'; f_equiv.
    unfold pointwise_relation; intros.
    setoid_rewrite Iterate_Decide_Comp_BoundedIndex; f_equiv.
  Qed.

  Definition UpdateUnConstrRelation
             (qsSchema : QueryStructureSchema)
             (rels : ilist (fun ns => UnConstrRelation (relSchema ns))
                           (qschemaSchemas qsSchema))
             (Ridx : _)
             newRel :
    ilist (fun ns => UnConstrRelation (relSchema ns))
          (qschemaSchemas qsSchema) :=
    replace_BoundedIndex relName rels Ridx newRel.


  Lemma QSInsertSpec_UnConstr_refine' :
    forall qsSchema (qs : UnConstrQueryStructure qsSchema)
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (tup : @Tuple (schemaHeading (QSGetNRelSchema qsSchema Ridx)))
           (or : QueryStructure qsSchema),
      DropQSConstraints_SiR or qs ->
      refine
        (Pick (fun qs' =>
                 exists or' : QueryStructure qsSchema,
                   (Pick (QSInsertSpec {| qsHint := or |} Ridx tup)) ↝ or' /\
                   DropQSConstraints_SiR or' qs'))
        (schConstr_self <- {b | decides b (SatisfiesSchemaConstraints Ridx tup tup)};
         schConstr <-
                   {b | decides b
                      (forall tup',
                         GetUnConstrRelation qs Ridx tup'
                         -> SatisfiesSchemaConstraints Ridx tup tup')};
         schConstr' <-
                    {b |
                     decides
                       b
                       (forall tup',
                          GetUnConstrRelation qs Ridx tup'
                          -> SatisfiesSchemaConstraints Ridx tup' tup)};
         qsConstr <- (@Iterate_Decide_Comp _
                                           (fun Ridx' =>
                                              SatisfiesCrossRelationConstraints
                                     Ridx Ridx' tup
                                     (GetUnConstrRelation qs Ridx')));
            qsConstr' <- (@Iterate_Decide_Comp _
                                (fun Ridx' =>
                                   Ridx' <> Ridx
                                   -> forall tup',
                                        (GetUnConstrRelation qs Ridx') tup'
                                        -> SatisfiesCrossRelationConstraints
                                       Ridx' Ridx tup'
                                       (RelationInsert tup (GetUnConstrRelation qs Ridx))));
            ret match schConstr_self, schConstr, schConstr', qsConstr, qsConstr' with
              | true, true, true, true, true =>
                (UpdateUnConstrRelation _ qs Ridx (RelationInsert tup (GetUnConstrRelation qs Ridx)))
              | _, _, _, _, _ => qs
            end).
  Proof.
    intros.
    setoid_rewrite refineEquiv_split_ex.
    setoid_rewrite refineEquiv_pick_computes_to_and.
    simplify with monad laws.
    setoid_rewrite refineEquiv_pick_eq';
      simplify with monad laws.
    unfold DropQSConstraints_SiR in *; intros; subst.
    rewrite QSInsertSpec_refine with (default := ret or).
    unfold refine; intros; subst.
      do 5 (apply_in_hyp computes_to_inv; destruct_ex; split_and).
      repeat rewrite GetRelDropConstraints in *.
      (* These assert are gross. Need to eliminate them. *)
      assert ((fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
          SatisfiesCrossRelationConstraints Ridx Ridx' tup
            (GetUnConstrRelation (DropQSConstraints or) Ridx')) =
              (fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
                 SatisfiesCrossRelationConstraints Ridx Ridx' tup
                                                   (GetRelation or Ridx'))) as rewriteSat
        by (apply functional_extensionality; intros; rewrite GetRelDropConstraints;
            reflexivity); rewrite rewriteSat in H3; clear rewriteSat.
      assert ((fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
          Ridx' <> Ridx ->
          forall
            tup' : @Tuple
                     (schemaHeading
                        (relSchema
                           (nth_Bounded relName (qschemaSchemas qsSchema)
                              Ridx'))),
          GetUnConstrRelation (DropQSConstraints or) Ridx' tup' ->
          SatisfiesCrossRelationConstraints Ridx' Ridx tup'
            (RelationInsert tup (GetRelation or Ridx))) =
              (fun Ridx' : BoundedIndex (map relName (qschemaSchemas qsSchema)) =>
      Ridx' <> Ridx ->
      forall
        tup' : @Tuple
                 (schemaHeading
                    (relSchema
                       (nth_Bounded relName (qschemaSchemas qsSchema) Ridx'))),
      GetRelation or Ridx' tup' ->
      SatisfiesCrossRelationConstraints Ridx' Ridx tup'
                                        (RelationInsert tup (GetRelation or Ridx))))
          as rewriteSat
            by (apply functional_extensionality; intros; rewrite GetRelDropConstraints;
                reflexivity); rewrite rewriteSat in H4; clear rewriteSat.
      (* Resume not-terribleness *)
      generalize (Iterate_Decide_Comp_BoundedIndex _ H3) as H3';
      generalize (Iterate_Decide_Comp_BoundedIndex _ H4) as H4'; intros.
      revert H3 H4.
      repeat apply_in_hyp computes_to_inv.
      econstructor 2 with
      (comp_a_value := match x as x', x0 as x0', x1 as x1', x2 as x2', x3 as x3'
                              return decides x' _ ->
                                     decides x0' _ ->
                                     decides x1' _ ->
                                     decides x2' _ ->
                                     decides x3' _ -> _
                        with
                          | true, true, true, true, true =>
                            fun H H0 H1 H2 H3 => @Insert_Valid _ or Ridx tup H0 H1 H H2 H3
                          | _, _, _, _, _ => fun _ _ _ _ _ => or
                        end H0 H1 H2 H3' H4').
      repeat (econstructor; eauto).
      repeat find_if_inside; try econstructor; simpl in *.
      unfold GetRelation, Insert_Valid, UpdateUnConstrRelation,
      UpdateRelation ; simpl; split; intros.
      rewrite ith_replace_BoundIndex_neq; eauto using string_dec; simpl.
      rewrite ith_replace_BoundIndex_eq; unfold RelationInsert, GetRelation;
      simpl; intuition.
      repeat find_if_inside; subst; repeat econstructor.
      unfold DropQSConstraints, Insert_Valid, RelationInsert; simpl.
      unfold GetRelation, Insert_Valid, UpdateUnConstrRelation,
      UpdateRelation; rewrite imap_replace_BoundedIndex; simpl; eauto using string_dec.
  Qed.

  Lemma QSInsertSpec_UnConstr_refine :
    forall qsSchema (qs : UnConstrQueryStructure qsSchema)
           (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
           (tup : @Tuple (schemaHeading (QSGetNRelSchema qsSchema Ridx)))
           (or : QueryStructure qsSchema)
           refined_schConstr_self refined_schConstr refined_schConstr'
           refined_qsConstr refined_qsConstr',
      refine {b | decides b (SatisfiesSchemaConstraints Ridx tup tup)}
             refined_schConstr_self
      -> refine {b | decides b
                             (forall tup',
                                GetUnConstrRelation qs Ridx tup'
                                -> SatisfiesSchemaConstraints Ridx tup tup')}
                refined_schConstr
      -> refine
           {b |
            decides
              b
              (forall tup',
                 GetUnConstrRelation qs Ridx tup'
                 -> SatisfiesSchemaConstraints Ridx tup' tup)}
           refined_schConstr'
      -> refine
           (@Iterate_Decide_Comp _
                                 (fun Ridx' =>
                                    SatisfiesCrossRelationConstraints
                                      Ridx Ridx' tup
                                      (GetUnConstrRelation qs Ridx')))
           refined_qsConstr
      -> refine
            (@Iterate_Decide_Comp _
                                  (fun Ridx' =>
                                     Ridx' <> Ridx
                                     -> forall tup',
                                          (GetUnConstrRelation qs Ridx') tup'
                                          -> SatisfiesCrossRelationConstraints
                                               Ridx' Ridx tup'
                                               (RelationInsert tup (GetUnConstrRelation qs Ridx))))
           refined_qsConstr'
      -> DropQSConstraints_SiR or qs ->
      refine
        (Pick (fun qs' =>
                 exists or' : QueryStructure qsSchema,
                   (Pick (QSInsertSpec {| qsHint := or |} Ridx tup)) ↝ or' /\
                   DropQSConstraints_SiR or' qs'))
        (schConstr_self <- refined_schConstr_self;
         schConstr <- refined_schConstr;
         schConstr' <- refined_schConstr';
         qsConstr <- refined_qsConstr ;
         qsConstr' <- refined_qsConstr';
            ret match schConstr_self, schConstr, schConstr', qsConstr, qsConstr' with
              | true, true, true, true, true =>
                (UpdateUnConstrRelation _ qs Ridx
                                      (RelationInsert tup (GetUnConstrRelation qs Ridx)))
              | _, _, _, _, _ => qs
            end).
  Proof.
    intros; rewrite QSInsertSpec_UnConstr_refine'; try eassumption.
    setoid_rewrite H; setoid_rewrite H0; setoid_rewrite H1;
    setoid_rewrite H2; setoid_rewrite H3; reflexivity.
  Qed.

End InsertRefinements.

(* We should put all these simplification hints into a distinct file
   so we're not unfolding things all willy-nilly. *)
Arguments Iterate_Decide_Comp _ _ / .
Arguments Iterate_Decide_Comp' _ _ _ _ / .
Arguments Ensemble_BoundedIndex_app_cons  _ _ _ _ _ _ / .
Arguments SatisfiesCrossRelationConstraints  _ _ _ _ _ / .
Arguments BuildQueryStructureConstraints  _ _ _ _ _ / .
Arguments BuildQueryStructureConstraints'  _ _ _ _ _ _ / .
Arguments BuildQueryStructureConstraints_cons / .
Arguments GetNRelSchemaHeading  _ _ / .
Arguments Ensemble_BoundedIndex_app_cons  _ _ _ _ _ _ / .
Arguments id  _ _ / .

  (* When we insert a tuple into a relation which has another relation has
     a foreign key into, we need to show that we haven't messed up any
     references (which is, of course, trivial. We should bake this into
     our the [QSInsertSpec_refine'] refinement itself by filtering out the
     irrelevant constraints somehow, but for now we can use the following
     tactic to rewrite them away. *)

  Ltac remove_trivial_insertion_constraints r tup Ridx Ridx' attr attr' SiR :=
    let refine_trivial := fresh in
    assert
           (refine {b' |
                    decides b'
                            (Ridx <> Ridx' ->
                             forall tup',
                               (GetUnConstrRelation r Ridx) tup' ->
                               exists
                                 tup2,
                                 RelationInsert tup (GetUnConstrRelation r Ridx') tup2 /\
                                 tup' attr = tup2 attr')} (ret true))
          as refine_trivial by
              (let v := fresh in
               let Comp_v := fresh in
               intros v Comp_v;
               apply computes_to_inv in Comp_v;
               rewrite <- SiR; subst;
               repeat rewrite GetRelDropConstraints;
               let neq := fresh in
               let tup' := fresh in
               let In_tup' := fresh in
               econstructor; simpl; intros neq tup' In_tup';
               unfold RelationInsert;
               destruct (@crossConstr _ _ Ridx Ridx' tup' neq In_tup'); split_and; eauto);
      setoid_rewrite refine_trivial;
      clear refine_trivial;
      autosetoid_rewrite with refine_monad.

Create HintDb refine_keyconstraints discriminated.
(*Hint Rewrite refine_Any_DecideableSB_True : refine_keyconstraints.*)

Arguments ith_Bounded _ _ _ _ _ _ _ / .
Arguments SatisfiesSchemaConstraints _ _ _ _ / .
Arguments GetUnConstrRelation : simpl never.
Arguments replace_BoundedIndex : simpl never.
