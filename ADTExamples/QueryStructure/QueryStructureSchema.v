Require Import List String Common FunctionalExtensionality Ensembles
        ADTNotation.ilist ADTNotation.StringBound Program.
Require Export
        ADTExamples.QueryStructure.Notations
        Heading Tuple Schema Relation.

(* A Query Structure schema is a set of named relation
   schemas and a set of cross-relation constraints
   (i.e. foreign key constraints). *)

Record QueryStructureSchema :=
  { qschemaIndex : Set;
    qschemaSchema : qschemaIndex -> Schema;
    qschemaConstraints:
      forall idx idx',
        Relation (qschemaSchema idx)
        -> Relation (qschemaSchema idx')
        -> Prop
  }.

Definition Prod_eq {A B C D : Type}
      (A_eq : A -> C -> bool)
      (B_eq : B -> D -> bool)
      (idx : A * B) (idx' : C * D) : bool :=
  andb (A_eq (fst idx) (fst idx')) (B_eq (snd idx) (snd idx')).

Definition BoundedString_eq bounds bstr str :=
  if (string_dec (bstring bounds bstr) str) then true else false.

Arguments BoundedString_eq _ _ _ / .

Definition BoundedStringProd_eq bounds bounds' :=
  Prod_eq (@BoundedString_eq bounds)
          (@BoundedString_eq bounds').

(* Notations for Query Structures. *)

Record NamedSchema  :=
  { relName : string;
    relSchema : Schema
  }.

Notation "'relation' name 'has' sch " :=
  {| relName := name%string;
     relSchema := sch%Schema
  |} : NamedSchema_scope.

Bind Scope NamedSchema_scope with NamedSchema.

Definition NamedSchema_eq (rn : NamedSchema) (idx : string) :=
  if (string_dec (relName rn) idx) then true else false.

Definition defaultSchema := (relation "null" has schema < "null" : () >)%NamedSchema.

Definition BuildQueryStructureIndex
           (namedSchemas : list NamedSchema) :=
           BoundedString (map relName namedSchemas).

Definition BuildQueryStructureSchema
           (namedSchemas : list NamedSchema)
           (idx : BoundedString (map relName namedSchemas)) :=
  relSchema (nth (findIndex NamedSchema_eq namedSchemas idx)
                 namedSchemas defaultSchema).

Lemma BuildQueryStructureSchema_idx_eq
      (namedSchemas : list NamedSchema)
: forall idx idx' : BuildQueryStructureIndex namedSchemas,
    bstring _ idx = bstring _ idx'
    -> BuildQueryStructureSchema namedSchemas idx =
       BuildQueryStructureSchema namedSchemas idx'.
Proof.
  intros.
  destruct idx as [idx idxBnd]; destruct idx' as [idx' idx'Bnd];
  simpl in *; subst.
  unfold BuildQueryStructureSchema; f_equal.
Defined.

(* A notation for foreign key constraints. This gives us
  a pair of relation schema names and a predicate on
  tuples in those tables. We use the namedSchemaHint
  typeclass to get the typechecking to work. *)

Definition ForeignKey_P rel1 rel2 attr1 attr2 tupmap
           (R1 : Relation rel1)
           (R2 : Relation rel2) :=
  forall tup1,
    rel R1 tup1 ->
    exists tup2,
      rel R2 tup2 /\
      tup1 attr1 =
      tupmap (tup2 attr2 ).

Definition BuildForeignKeyConstraints
           (namedSchemas :  list NamedSchema)
           (rel1 rel2 : string)
           {relBnd1}
           {relBnd2}
           attr1
           attr2
           {tupmap} :=
  (existT (fun ids => Relation (BuildQueryStructureSchema namedSchemas (fst ids))
                      -> Relation (BuildQueryStructureSchema namedSchemas (snd ids))
                    -> Prop)
          ({|bstring :=rel1; stringb := relBnd1 |},
           {|bstring :=rel2; stringb := relBnd2 |})
          (ForeignKey_P attr1 attr2 tupmap)).

Class namedSchemaHint :=
  { nSchemaHint :> list NamedSchema }.

Notation "'attribute' attr 'of' rel1 'references' rel2 " :=
  (
      @BuildForeignKeyConstraints
        (@nSchemaHint _) rel1%string rel2%string _ _
        {| bstring := attr%string;
           stringb := _|}
        {| bstring := attr%string;
           stringb := _|} id) : QSSchemaConstraints_scope.

Program Definition BuildQueryStructureConstraints_cons
           (namedSchemas : list NamedSchema)
           (idx' : sigT (fun idxs =>
                 Relation (BuildQueryStructureSchema namedSchemas (fst idxs))
                 -> Relation (BuildQueryStructureSchema namedSchemas (snd idxs))
                 -> Prop) )
           (constraints :
              list (sigT (fun idxs =>
                 Relation (BuildQueryStructureSchema namedSchemas (fst idxs))
                 -> Relation (BuildQueryStructureSchema namedSchemas (snd idxs))
                 -> Prop) ))
           (idx : (BuildQueryStructureIndex namedSchemas *
                   BuildQueryStructureIndex namedSchemas))
           (HInd : Relation (BuildQueryStructureSchema namedSchemas (fst idx))
                   -> Relation (BuildQueryStructureSchema namedSchemas (snd idx))
                   -> Prop)
: Relation (BuildQueryStructureSchema namedSchemas (fst idx))
  -> Relation (BuildQueryStructureSchema namedSchemas (snd idx))
  -> Prop :=
  if (string_dec (bstring _ (fst (projT1 idx'))) (bstring _ (fst idx))) then
    if (string_dec (bstring _ (snd (projT1 idx'))) (bstring _ (snd idx)) ) then
      _ else (fun r1 r2 => HInd r1 r2)
  else (fun r1 r2 => HInd r1 r2).
Next Obligation.
  simpl in *.
  subst; apply X1.
  erewrite BuildQueryStructureSchema_idx_eq;
    [ eapply X
    | simpl; rewrite H; eauto].
  erewrite BuildQueryStructureSchema_idx_eq;
    [ eapply X0
    | simpl; rewrite H0; eauto].
Defined.

Fixpoint BuildQueryStructureConstraints
(namedSchemas : list NamedSchema)
(constraints :
   list (sigT (fun idxs =>
                 Relation (BuildQueryStructureSchema namedSchemas (fst idxs))
                 -> Relation (BuildQueryStructureSchema namedSchemas (snd idxs))
                 -> Prop) ))
(idx : (BuildQueryStructureIndex namedSchemas *
        BuildQueryStructureIndex namedSchemas)) {struct constraints}
: Relation (BuildQueryStructureSchema namedSchemas (fst idx))
  -> Relation (BuildQueryStructureSchema namedSchemas (snd idx))
  -> Prop :=
  match constraints with
    | idx' :: constraints' =>
      @BuildQueryStructureConstraints_cons
        namedSchemas idx' constraints' idx
      (BuildQueryStructureConstraints constraints' idx)
    | nil => fun _ _ => True
  end.

(*

Lemma BuildQueryStructureConstraints_eq
: forall (namedSchemas : list NamedSchema)
         P
         (constraints :
            list (sigT P))
         (idx idx' : BuildQueryStructureIndex namedSchemas),
    (bstring _ idx, bstring _ idx') =
    (bstring _ (fst (nth
       (findIndex
          (BoundedStringProd_eq (bounds':=map relName namedSchemas))
          (map (projT1 (P:=P)) constraints)
          (bstring _ idx, bstring _ idx'))
       (map (projT1 (P := P)) constraints)
       (idx, idx'))),
     bstring _ (snd (nth
       (findIndex
          (BoundedStringProd_eq (bounds':=map relName namedSchemas))
          (map (projT1 (P := P)) constraints)
          (bstring _ idx, bstring _ idx'))
       (map (projT1 (P := P)) constraints)
       (idx, idx'))))
     .
Proof.
  intros.
  induction (map (projT1 (P:=P)) constraints); simpl; try reflexivity.
  unfold BoundedStringProd_eq, BoundedString_eq, Prod_eq; simpl.
  destruct (string_dec (fst a) idx); simpl; try exact IHl.
  destruct (string_dec (snd a) idx'); simpl in *; try reflexivity.
  rewrite e, e0; reflexivity.
  rewrite IHl at 1; reflexivity.
Defined.

     Print BuildQueryStructureConstraints_eq.

Lemma BuildQueryStructureConstraints_eq_fst
: forall (namedSchemas : list NamedSchema)
         P
         (constraints :
            list (sigT P))
         (idx idx' : BuildQueryStructureIndex namedSchemas),
    bstring _ idx =
    fst (bstring _ (fst (nth
       (findIndex
          (BoundedStringProd_eq (bounds':=map relName namedSchemas))
          (map (projT1 (P:=P)) constraints)
          (bstring _ idx, bstring _ idx'))
       (map (projT1 (P := P)) constraints)
       (idx, idx'))),
     bstring _ (snd (nth
       (findIndex
          (BoundedStringProd_eq (bounds':=map relName namedSchemas))
          (map (projT1 (P := P)) constraints)
          (bstring _ idx, bstring _ idx'))
       (map (projT1 (P := P)) constraints)
       (idx, idx')))).
  intros; rewrite <- BuildQueryStructureConstraints_eq; reflexivity.
Defined.

Lemma BuildQueryStructureConstraints_eq_snd
: forall (namedSchemas : list NamedSchema)
         P
         (constraints :
            list (sigT P))
         (idx idx' : BuildQueryStructureIndex namedSchemas),
    bstring _ idx' =
    snd (bstring _ (fst (nth
       (findIndex
          (BoundedStringProd_eq (bounds':=map relName namedSchemas))
          (map (projT1 (P:=P)) constraints)
          (bstring _ idx, bstring _ idx'))
       (map (projT1 (P := P)) constraints)
       (idx, idx'))),
     bstring _ (snd (nth
       (findIndex
          (BoundedStringProd_eq (bounds':=map relName namedSchemas))
          (map (projT1 (P := P)) constraints)
          (bstring _ idx, bstring _ idx'))
       (map (projT1 (P := P)) constraints)
       (idx, idx')))).
  intros; rewrite <- BuildQueryStructureConstraints_eq; reflexivity.
Defined.

Program Definition BuildQueryStructureConstraints
(namedSchemas : list NamedSchema)
(constraints :
   list (sigT (fun idxs =>
                 Relation (BuildQueryStructureSchema namedSchemas (fst idxs))
                 -> Relation (BuildQueryStructureSchema namedSchemas (snd idxs))
                 -> Prop) ))
:
  forall (idx : (BuildQueryStructureIndex namedSchemas *
                 BuildQueryStructureIndex namedSchemas)),
    Relation (BuildQueryStructureSchema namedSchemas (fst idx))
    -> Relation (BuildQueryStructureSchema namedSchemas (snd idx))
    -> Prop :=
  fun idx =>
    ith (@BoundedStringProd_eq _ _) (siglist2ilist constraints)
        (bstring _ (fst idx), bstring _ (snd idx)) idx (fun _ _ => True).
Next Obligation.
  eapply BuildQueryStructureSchema_idx_eq.
  apply BuildQueryStructureConstraints_eq_fst.
Defined.
Next Obligation.
  eapply BuildQueryStructureSchema_idx_eq.
  apply BuildQueryStructureConstraints_eq_snd.
Defined.

Definition BuildQueryStructureConstraints'
(namedSchemas : list NamedSchema)
(constraints :
   list (sigT (fun idxs =>
                 Relation (BuildQueryStructureSchema namedSchemas (fst idxs))
                 -> Relation (BuildQueryStructureSchema namedSchemas (snd idxs))
                 -> Prop) ))
:
  forall (idx : (BuildQueryStructureIndex namedSchemas *
                 BuildQueryStructureIndex namedSchemas)),
    Relation _
    -> Relation _
    -> Prop :=
  fun idx =>
    ith (@BoundedStringProd_eq _ _) (siglist2ilist constraints)
        (bstring _ (fst idx), bstring _ (snd idx)) idx (fun _ _ => True).

Print BuildQueryStructureConstraints'. *)

Definition BuildQueryStructure
           (namedSchemas : list NamedSchema)
           constraints :=
  {| qschemaIndex :=
       BoundedString (map relName namedSchemas);
     qschemaSchema idx :=
       relSchema (nth (findIndex NamedSchema_eq namedSchemas idx)
                      namedSchemas defaultSchema);
     qschemaConstraints idx idx' := @BuildQueryStructureConstraints
                                      namedSchemas
                                      constraints (idx, idx') |}.

Notation "'query' 'structure' 'schema' relList " :=
  (BuildQueryStructure relList%NamedSchema []) : QSSchema_scope.

Notation "'query' 'structure' 'schema' relList 'enforcing' constraints" :=
  (BuildQueryStructure relList%NamedSchema
                       (let relListHint := Build_namedSchemaHint relList%NamedSchema in
                        constraints%QSSchemaConstraints)) : QSSchema_scope.

Arguments BuildForeignKeyConstraints _ _ [_ _ _ _] _ _ / .
Arguments BuildQueryStructureConstraints_cons [_] _ _ _ _ / _ _.
Arguments BuildQueryStructureConstraints_cons_obligation_1 [_] _ / _ _ _ _ _ _ _ .
Arguments eq_rect_r _ _ _ _ _ _ / .
Arguments ForeignKey_P _ _ _ _ _ / _ _ .
Arguments BuildQueryStructureSchema _ _ / .

Bind Scope QSSchema_scope with QueryStructureSchema.
