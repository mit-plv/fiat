Require Import List String Ensembles Arith
        ADTNotation Program QueryStructureSchema QueryStructure.

(* Definitions for updating query structures. *)

(* 'Inserting' a Tuple [tup] into a relation [R] represented
    as an ensemble produces a new ensemble that holds for any
    Tuple [tup'] equal to [tup] or which is already in [R]. *)
Definition RelationInsert
           {Heading}
           (tup : Tuple Heading)
           (R : Ensemble _)
           (tup' : Tuple Heading) :=
  tup' = tup \/ R tup'.

Definition SatisfiesSchemaConstraints
           {qsSchema} Ridx tup :=
  schemaConstraints (QSGetNRelSchema qsSchema Ridx) tup.

Definition SatisfiesCrossRelationConstraints
           {qsSchema} Ridx Ridx' tup R :=
  BuildQueryStructureConstraints qsSchema Ridx Ridx' tup R.

Definition QSInsertSpec
           (qs : QueryStructureHint)
           (Ridx : _)
           (tup : Tuple (schemaHeading (QSGetNRelSchema _ Ridx)))
           (qs' : QueryStructure qsSchemaHint)
: Prop :=
  (* All of the relations with a different index are untouched
     by insert. *)
  (forall Ridx',
     Ridx <> Ridx' ->
     GetRelation qsHint Ridx' = GetRelation qs' Ridx') /\
  (* If [tup] is consistent with the schema constraints, *)
  SatisfiesSchemaConstraints Ridx tup
  (* and [tup] is consistent with the other tables per the cross-relation
     constraints, *)
  -> (forall Ridx', SatisfiesCrossRelationConstraints Ridx Ridx' tup (GetRelation qsHint Ridx'))
  (* and each tuple in the other tables is consistent with the
     table produced by inserting [tup] into the relation indexed by [Ridx], *)
  -> (forall Ridx' tup',
        Ridx' <> Ridx ->
        SatisfiesCrossRelationConstraints
          Ridx' Ridx tup'
          (RelationInsert tup (GetRelation qsHint Ridx)))
  (* [tup] is included in the relation indexed by [Ridx] after insert.
   The behavior of insertion is unspecified otherwise. *)
  -> (forall t, GetRelation qs' Ridx t <->
               (RelationInsert tup (GetRelation qsHint Ridx) t)).

Notation "'Insert' b 'into' Ridx " :=
  (Bind (Pick (QSInsertSpec _ Ridx b))
        (fun r' => Pick (fun r => r' = r)))
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

  Program
    Definition Insert_Valid
    (qsSchema : QueryStructureSchema)
    (qs : QueryStructure qsSchema)
    (Ridx : _)
    (tup : Tuple (QSGetNRelSchemaHeading qsSchema Ridx))
    (schConstr : SatisfiesSchemaConstraints Ridx tup)
    (qsConstr : forall Ridx',
                  SatisfiesCrossRelationConstraints Ridx Ridx' tup (GetRelation qs Ridx'))
    (qsConstr' : forall Ridx' tup',
                   Ridx' <> Ridx ->
                   SatisfiesCrossRelationConstraints
                     Ridx' Ridx tup'
                     (RelationInsert tup (GetRelation qs Ridx)))
  : QueryStructure qsSchema :=
    {| rels :=
         replace_BoundedIndex _ (rels qs) Ridx
                       {| rel := RelationInsert tup (GetRelation qs Ridx)|}
    |}.
  Next Obligation.
    unfold RelationInsert in *; simpl in *; intuition; subst; eauto.
    eapply ((ith_Bounded _ (rels qs) Ridx )); eassumption.
  Qed.
  Next Obligation.
    unfold SatisfiesCrossRelationConstraints in *;
    destruct (BoundedString_eq_dec Ridx idx'); subst.
    - rewrite ith_replace_BoundIndex_eq; eauto.
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
                 (nth_error_app (As ++ [a]%SchemaConstraints) As'
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
                 (nth_error_app (As ++ [a]%SchemaConstraints) As'
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
      assert (nth_error ((Visited ++ [a]%SchemaConstraints) ++ Remaining) n = Some idx)
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

  Lemma QSInsertSpec_refine :
    forall qsSchema (qs : QueryStructure qsSchema) Ridx tup default,
      refine
           (Pick (QSInsertSpec {| qsHint := qs |} Ridx tup))
           (schConstr <- {b | decides b (SatisfiesSchemaConstraints Ridx tup)};
            qsConstr <- {b | decides b
(forall Ridx', SatisfiesCrossRelationConstraints Ridx Ridx' tup (GetRelation qs Ridx'))};
            qsConstr' <- {b | decides
                                b
                                (forall Ridx',
                                   Ridx' <> Ridx ->
                                   forall tup',
                                     SatisfiesCrossRelationConstraints
                                       Ridx' Ridx tup'
                                       (RelationInsert tup (GetRelation qs Ridx)))};
            match schConstr, qsConstr, qsConstr' with
              | true, true, true =>
                {qs' |
                 (forall Ridx',
                    Ridx <> Ridx' ->
                    GetRelation qsHint Ridx' =
                    GetRelation qs' Ridx')
                 /\ forall t,
                      GetRelation qs' Ridx t <->
                      (RelationInsert tup (GetRelation qsHint Ridx) t)
             }

              | _, _, _ => default
            end).
  Proof.
    intros qsSchema qs Ridx tup default v Comp_v.
    do 3 (apply_in_hyp computes_to_inv; destruct_ex; split_and);
      destruct x;
      [ destruct x0;
        [ destruct x1;
          [ repeat (apply_in_hyp computes_to_inv; destruct_ex; split_and); simpl in *;
            econstructor; unfold QSInsertSpec; eauto |
             ]
        |  ]
      |  ];
      cbv delta [decides] beta in *; simpl in *;
      repeat (apply_in_hyp computes_to_inv; destruct_ex); eauto;
      econstructor; unfold QSInsertSpec; intros;
      elimtype False; intuition.
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

  Lemma decides_2_True (A B : Type) :
    refine {b' | decides b' (A -> B -> True)}%comp
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
        as refine_if.
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
  : BoundedString (map relName (qschemaSchemas qsSchema)).
    destruct Ridx' as [Ridx' [n nth_n]];
    econstructor 1 with (bindex := Ridx').
    unfold GetRelevantConstraints in *.
    revert n nth_n.
    induction (qschemaConstraints qsSchema); simpl in *; intros.
    - destruct n; discriminate.
    - destruct n; simpl in *.
      revert nth_n.
      case_eq (BoundedIndex_eq_dec string_dec Ridx (fst (projT1 a)));
        intros; subst.

    econstructor; eauto.

    intros


  Lemma Iterate_Decide_Comp_refine :
    forall qsSchema (qs : QueryStructure qsSchema) Ridx tup,
      refine (@Iterate_Decide_Comp _
                                   (fun Ridx' =>
                                      SatisfiesCrossRelationConstraints
                                        Ridx Ridx' tup
                                        (GetRelation qs Ridx')))
             (@Iterate_Decide_Comp (GetRelevantConstraints qsSchema Ridx)
                                   (fun Ridx' =>
                                      SatisfiesCrossRelationConstraints
                                        Ridx Ridx' tup
                                        (GetRelation qs Ridx'))).


Definition SatisfiesCrossRelationConstraints
           {qsSchema} Ridx Ridx' tup R :=
  BuildQueryStructureConstraints qsSchema Ridx Ridx' tup R. *)


  Lemma QSInsertSpec_refine' :
    forall qsSchema (qs : QueryStructure qsSchema) Ridx tup default,
      refine
           (Pick (QSInsertSpec {| qsHint := qs |} Ridx tup))
           (schConstr <- {b | decides b (SatisfiesSchemaConstraints Ridx tup)};
            qsConstr <- (@Iterate_Decide_Comp _
                                (fun Ridx' =>
                                   SatisfiesCrossRelationConstraints
                                     Ridx Ridx' tup
                                     (GetRelation qsHint Ridx')));
            qsConstr' <- (@Iterate_Decide_Comp _
                                (fun Ridx' =>
                                   Ridx' <> Ridx ->
                                   forall tup',
                                     SatisfiesCrossRelationConstraints
                                       Ridx' Ridx tup'
                                       (RelationInsert tup (GetRelation qs Ridx))));
            match schConstr, qsConstr, qsConstr' with
              | true, true, true =>
                {qs' |
                 (forall Ridx',
                    Ridx <> Ridx' ->
                    GetRelation qsHint Ridx' =
                    GetRelation qs' Ridx')
                 /\ forall t,
                      GetRelation qs' Ridx t <->
                      (RelationInsert tup (GetRelation qsHint Ridx) t)
             }

              | _, _, _ => default
            end).
  Proof.
    intros.
    rewrite QSInsertSpec_refine; f_equiv.
    unfold pointwise_relation; intros.
    rewrite Iterate_Decide_Comp_BoundedIndex; f_equiv.
    unfold pointwise_relation; intros.
    rewrite Iterate_Decide_Comp_BoundedIndex; reflexivity.
  Qed.

  (* Lemma Iterate_Ensemble_equiv {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P : Ensemble (BoundedIndex (Visited ++ Remaining))),
      (forall a n (nth : nth_error Visited n = Some a),
         P {| bindex := a;
              indexb := {| ibound := n;
                           boundi := nth_error_app _ _ _ nth |} |})
      -> (Iterate_Ensemble_BoundedIndex Visited Remaining P ->
         forall idx, P idx).
    intros; destruct idx as [idx [n nth_n] ]; simpl in *.
    revert Visited P H H0 idx n nth_n; induction Remaining; simpl; intros.
    - eapply Ensemble_BoundedIndex_nth_eq with (a := idx); auto.
    - split_and.
      assert (nth_error ((Visited ++ [a]%SchemaConstraints) ++ Remaining) n = Some idx)
        as nth_n'
          by (rewrite <- app_assoc; simpl; assumption).
      generalize (IHRemaining _ _ (Ensemble_nth_error_app A_eq_dec _ _ _ P H1 H) H2 _ _ nth_n').
      unfold Ensemble_BoundedIndex_app_cons, eq_rect; destruct (app_cons a Visited Remaining).
      intros; erewrite (eq_proofs_unicity_Opt_A A_eq_dec nth_n); eauto.
      Grab Existential Variables.
      rewrite app_nil_r in nth_n; assumption.
  Qed.

  Lemma Iterate_Ensemble_equiv' {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (Remaining Visited : list A)
           (P : Ensemble (BoundedIndex (Visited ++ Remaining))),
      (forall idx, P idx)
      -> Iterate_Ensemble_BoundedIndex Visited Remaining P.
    induction Remaining; simpl; auto.
    intros; split; eauto.
    eapply IHRemaining; intros; eauto.
    intros; destruct idx as [idx [n nth_n] ]; simpl in *.
    eapply Ensemble_BoundedIndex_app_equiv; eauto.
    Grab Existential Variables.
    rewrite <- app_assoc in nth_n; simpl in nth_n; eassumption.
  Qed.

  Lemma refine_Iterate_Ensemble {A : Set}
        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
  : forall (As : list A)
           (P : Ensemble (BoundedIndex As)),
      refine {b | decides b (forall idx, P idx)}
             {b | decides b (Iterate_Ensemble_BoundedIndex [] As P)}.
  Proof.
    intros; eapply refine_pick_pick.
    intros; destruct x; simpl in *.
    intros; eapply Iterate_Ensemble_equiv with (Visited := []); eauto.
    destruct n; simpl; intros; discriminate.
    unfold not; intros; apply H.
    apply Iterate_Ensemble_equiv'; auto.
  Qed.



  Lemma QSInsertSpec_refine :
    forall qsSchema (qs : QueryStructure qsSchema) Ridx tup default,
      refine
           (Pick (QSInsertSpec {| qsHint := qs |} Ridx tup))
           (schConstr <- {b | decides b (SatisfiesSchemaConstraints Ridx tup)};
            qsConstr <- {b | decides b
(forall Ridx', SatisfiesCrossRelationConstraints Ridx Ridx' tup (GetRelation qs Ridx'))};
            qsConstr' <- {b | decides
                                b
                                (forall Ridx',
                                   Ridx' <> Ridx ->
                                   forall tup',
                                     SatisfiesCrossRelationConstraints
                                       Ridx' Ridx tup'
                                       (RelationInsert tup (GetRelation qs Ridx)))};
            match schConstr, qsConstr, qsConstr' with
              | true, true, true =>
                {qs' |
                 (forall Ridx',
                    Ridx <> Ridx' ->
                    GetRelation qsHint Ridx' =
                    GetRelation qs' Ridx')
                 /\ forall t,
                      GetRelation qs' Ridx t <->
                      (RelationInsert tup (GetRelation qsHint Ridx) t)
             }

              | _, _, _ => default
            end).
  Proof.
    intros qsSchema qs Ridx tup default v Comp_v.
    do 3 (apply_in_hyp computes_to_inv; destruct_ex; split_and);
      destruct x;
      [ destruct x0;
        [ destruct x1;
          [ repeat (apply_in_hyp computes_to_inv; destruct_ex; split_and); simpl in *;
            econstructor; unfold QSInsertSpec; eauto |
             ]
        |  ]
      |  ];
      cbv delta [decides] beta in *; simpl in *;
      repeat (apply_in_hyp computes_to_inv; destruct_ex); eauto;
      econstructor; unfold QSInsertSpec; intros;
      elimtype False; intuition.
  Qed.

  (* Infrastructure for Inserting into QueryStructures built using
     BuildQueryStructure*)

  Program Fixpoint DecideableSB_Comp (A : Type)
          (Bound : list A)
          (P : Ensemble A)
          {struct Bound}
  : Comp bool :=
    match Bound as Bound' with
      | nil => ret true
      | cons a Bound' => Bind {b' | decides b' (P a)}%comp
                                 (fun b' =>
                                    if b'
                                    then
                                      DecideableSB_Comp Bound' P
                                    else ret false)
    end.

  (* Next Obligation.

    destruct b'; destruct b; simpl in *; try discriminate.
    destruct (A_eq_dec a a0).
    -
    Focus 2.
    apply ValidBound'; tauto.
  Defined. *)

  Definition Iterate_Constraints_dec
             qsSchema
             (qs : QueryStructure qsSchema)
             Ridx
             (tup : Tuple (QSGetNRelSchemaHeading qsSchema Ridx))
    := DecideableSB_Comp
         (map (fun constr => snd (projT1 constr)) (qschemaConstraints qsSchema))
         (fun Ridx' =>
            BuildQueryStructureConstraints
              qsSchema Ridx Ridx' tup (GetRelation qs Ridx')).

  Lemma DecideableSB_Comp_refine :
  forall qsSchema
         (qs : QueryStructure qsSchema)
         Ridx
         (tup : Tuple (QSGetNRelSchemaHeading qsSchema Ridx)),
      refine
        {b | decides b (forall Ridx',
                          SatisfiesCrossRelationConstraints Ridx Ridx' tup (GetRelation qs Ridx')) }
      (Iterate_Constraints_dec qs Ridx tup).
  Proof.
    unfold Iterate_Constraints_dec, SatisfiesCrossRelationConstraints,
    QSGetNRelSchema; simpl.
    unfold BuildQueryStructureConstraints.
    intro; induction (qschemaConstraints qsSchema); simpl; intros.
    - repeat econstructor; inversion_by computes_to_inv; subst; simpl; auto.
    - intros v Comp_v; apply computes_to_inv in Comp_v; destruct_ex; split_and.
      destruct x.
      generalize (IHl _ _ _ _ H1).
      econstructor.
      unfold BuildQueryStructureConstraints_cons; simpl.
      destruct (Peano_dec.eq_nat_dec (ibound Ridx) (ibound (fst (projT1 a)))).
      simpl.

    intros.
    repeat econstructor.

  Qed.

  Definition Iterate_Constraints_dec'
             qsSchema
             (qs : QueryStructure qsSchema)
             Ridx
             (tup : Tuple (QSGetNRelSchemaHeading qsSchema Ridx))
    := DecideableSB_Comp
         string_dec
         (map relName (qschemaSchemas qsSchema))
         (fun Ridx' =>
            Ridx' <> Ridx ->
            forall tup' : Tuple (QSGetNRelSchemaHeading qsSchema Ridx'),
            BuildQueryStructureConstraints
              qsSchema Ridx' Ridx tup' (tup :: (GetRelation qs Ridx)))
         (ValidBound_DecideableSB_Comp' qsSchema _ tup ).

  Lemma DecideableSB_Comp'_refine :
  forall qsSchema
         (qs : QueryStructure qsSchema)
         Ridx
         (tup : Tuple (QSGetNRelSchemaHeading qsSchema Ridx)),
      refine
      (Any (QSSchemaConstraints_dec' qs Ridx tup))
      (Iterate_Constraints_dec' qs Ridx tup).
  Proof.
    intros.
    repeat econstructor.
  Qed.

  Definition ValidBound_DecideableSB_Comp
             qsSchema
             (qs : forall Ridx : string,
                     list
                       (Tuple
                          (QSGetNRelSchemaHeading qsSchema Ridx)))
             Ridx
             (tup : Tuple (QSGetNRelSchemaHeading qsSchema Ridx))
  : forall a : string,
      ~ List.In a (map relName (qschemaSchemas qsSchema)) ->
      (fun Ridx' : string =>
         BuildQueryStructureConstraints qsSchema
           Ridx Ridx' tup (qs Ridx')) a.
  Proof.
    destruct qsSchema as [namedSchemas constraints]; simpl in *.
    simpl in *; induction constraints;
    unfold BuildQueryStructureConstraints;  simpl; auto; intros.
    destruct a; destruct x; simpl in *.
    unfold BuildQueryStructureConstraints',
    BuildQueryStructureConstraints_cons,
    BuildQueryStructureConstraints_cons_obligation_1 in *;
      simpl in *.
    destruct (string_dec s Ridx); try (apply IHconstraints; eauto; fail).
    destruct (string_dec s0 a0); try (apply IHconstraints; eauto; fail).
    destruct e; destruct e0.
    unfold eq_sym, eq_rect; simpl.
    destruct (in_dec string_dec s (map relName namedSchemas)); auto.
    destruct (in_dec string_dec s0 (map relName namedSchemas)); tauto.
  Qed.

  Definition ValidBound_DecideableSB_Comp'
             qsSchema
             (qs : forall Ridx : string,
                     list
                       (Tuple
                          (QSGetNRelSchemaHeading qsSchema Ridx)))
             Ridx
             (tup : Tuple (QSGetNRelSchemaHeading qsSchema Ridx))
  : forall a : string,
      ~ List.In a (map relName (qschemaSchemas qsSchema)) ->
      a <> Ridx ->
      forall
        tup' : Tuple (QSGetNRelSchemaHeading qsSchema a),
        BuildQueryStructureConstraints qsSchema
                                       a Ridx tup' (tup :: qs Ridx).
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
    destruct (string_dec s0 Ridx); try (apply IHconstraints; eauto; fail).
    destruct e; destruct e0.
    unfold eq_sym, eq_rect; simpl.
    destruct (in_dec string_dec s (map relName namedSchemas)); auto.
    destruct (in_dec string_dec s0 (map relName namedSchemas)); tauto.
  Qed.

  Definition Iterate_Constraints_dec
             qsSchema
             (qs : QueryStructure qsSchema)
             Ridx
             (tup : Tuple (QSGetNRelSchemaHeading qsSchema Ridx))
    := DecideableSB_Comp
         string_dec
         (map relName (qschemaSchemas qsSchema))
         (fun Ridx' =>
            BuildQueryStructureConstraints
              qsSchema Ridx Ridx' tup (GetRelation qs Ridx'))
         (ValidBound_DecideableSB_Comp qsSchema _
                                       Ridx tup ).

  Set Printing All.

  Lemma DecideableSB_Comp_refine :
  forall qsSchema
         (qs : QueryStructure qsSchema)
         Ridx
         (tup : Tuple (QSGetNRelSchemaHeading qsSchema Ridx)),
      refine
      (Any (QSSchemaConstraints_dec qs Ridx tup))
      (Iterate_Constraints_dec qs Ridx tup).
  Proof.
    intros.
    repeat econstructor.
  Qed.

  Definition Iterate_Constraints_dec'
             qsSchema
             (qs : QueryStructure qsSchema)
             Ridx
             (tup : Tuple (QSGetNRelSchemaHeading qsSchema Ridx))
    := DecideableSB_Comp
         string_dec
         (map relName (qschemaSchemas qsSchema))
         (fun Ridx' =>
            Ridx' <> Ridx ->
            forall tup' : Tuple (QSGetNRelSchemaHeading qsSchema Ridx'),
            BuildQueryStructureConstraints
              qsSchema Ridx' Ridx tup' (tup :: (GetRelation qs Ridx)))
         (ValidBound_DecideableSB_Comp' qsSchema _ tup ).

  Lemma DecideableSB_Comp'_refine :
  forall qsSchema
         (qs : QueryStructure qsSchema)
         Ridx
         (tup : Tuple (QSGetNRelSchemaHeading qsSchema Ridx)),
      refine
      (Any (QSSchemaConstraints_dec' qs Ridx tup))
      (Iterate_Constraints_dec' qs Ridx tup).
  Proof.
    intros.
    repeat econstructor.
  Qed.

  Lemma QSInsertSpec_BuildQuerySpec_refine :
    forall qsSchema
           (qs : QueryStructure qsSchema)
           Ridx tup default,
      refine
        (Pick (QSInsertSpec {| qsHint := qs |} Ridx tup))
        (schConstr <- Any (SchemaConstraints_dec _ Ridx tup);
         qsConstr <- (Iterate_Constraints_dec qs Ridx tup);
         qsConstr' <- (Iterate_Constraints_dec' qs Ridx tup);
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
