Require Import List String Common FunctionalExtensionality Ensembles
        ADTNotation.ilist ADTNotation.StringBound Program.
Require Export
        ADTExamples.QueryStructure.Notations
        Heading Tuple Schema Relation.

(* A Query Structure schema is a set of named relation
   schemas and a set of cross-relation constraints
   (i.e. foreign key constraints). *)

Record NamedSchema  :=
  { relName : string;
    relSchema : Schema
  }.

Definition NamedSchema_eq (rn : NamedSchema) (idx : string) :=
  if (string_dec (relName rn) idx) then true else false.

Definition defaultSchema :=
  {| relName := "null"%string;
     relSchema :=  {| schemaHeading := <"null" : ()>%Heading;
                      schemaConstraints tup := True
                      |} |}.

Definition BuildQSSchema
           (namedSchemas : list NamedSchema)
           (idx : string) :=
  relSchema (nth (findIndex NamedSchema_eq namedSchemas idx)
                 namedSchemas defaultSchema).

Record QueryStructureSchema :=
  { qschemaSchemas : list NamedSchema;
    qschemaConstraints:
      forall idx idx',
        Tuple (schemaHeading (BuildQSSchema qschemaSchemas idx))
        -> list (Tuple (schemaHeading (BuildQSSchema qschemaSchemas idx')))
        -> Prop
  }.

Definition GetNamedSchema 
           (QSSchema : QueryStructureSchema)
           (idx : string) :=
  BuildQSSchema (qschemaSchemas QSSchema) idx.

(* Notations for Query Structures. *)

Notation "'relation' name 'has' sch " :=
  {| relName := name%string;
     relSchema := sch%Schema
  |} : NamedSchema_scope.

Bind Scope NamedSchema_scope with NamedSchema.

Lemma BuildQSSchema_idx_eq
      (namedSchemas : list NamedSchema)
: forall idx idx' : string,
    idx = idx'
    -> BuildQSSchema namedSchemas idx =
       BuildQSSchema namedSchemas idx'.
Proof.
  intros; rewrite H; auto.
Defined.

(* A notation for foreign key constraints. This gives us
  a pair of relation schema names and a predicate on
  tuples in those tables. We use the namedSchemaHint
  typeclass to get the typechecking to work. *)

Definition ForeignKey_P heading relSchema attr1 attr2 tupmap
           (tup : Tuple heading)
           (R : list (Tuple relSchema)) :=
  exists tup2,
    List.In tup2 R /\
    tup attr1 =
    tupmap (tup2 attr2 ).

Definition BuildForeignKeyConstraints
           (namedSchemas :  list NamedSchema)
           (rel1 rel2 : string)
           attr1
           attr2
           {tupmap} :=
  (existT (fun ids => Tuple (schemaHeading (BuildQSSchema namedSchemas (fst ids)))
                      -> list (Tuple (schemaHeading (BuildQSSchema namedSchemas (snd ids))))
                    -> Prop)
          (rel1, rel2)
          (ForeignKey_P attr1 attr2 tupmap)).

Class namedSchemaHint :=
  { nSchemaHint :> list NamedSchema }.

Notation "'attribute' attr 'of' rel1 'references' rel2 " :=
  (
      @BuildForeignKeyConstraints
        (@nSchemaHint _) rel1%string rel2%string
        attr%string
        attr%string id) : QSSchemaConstraints_scope.

Program Definition BuildQueryStructureConstraints_cons
           (namedSchemas : list NamedSchema)
           (idx' : sigT (fun idxs =>
                 Tuple (schemaHeading (BuildQSSchema namedSchemas (fst idxs)))
                 -> list (Tuple (schemaHeading (BuildQSSchema namedSchemas (snd idxs))))
                 -> Prop) )
           (constraints :
              list (sigT (fun idxs =>
                 Tuple (schemaHeading (BuildQSSchema namedSchemas (fst idxs)))
                 -> list (Tuple (schemaHeading (BuildQSSchema namedSchemas (snd idxs))))
                 -> Prop) ))
           (idx : (string * string))
           (HInd : Tuple (schemaHeading (BuildQSSchema namedSchemas (fst idx)))
                   -> list (Tuple (schemaHeading (BuildQSSchema namedSchemas (snd idx))))
                   -> Prop)
: Tuple (schemaHeading (BuildQSSchema namedSchemas (fst idx)))
  -> list (Tuple (schemaHeading (BuildQSSchema namedSchemas (snd idx))))
  -> Prop :=
  if (string_dec (fst (projT1 idx')) (fst idx)) then
    if (string_dec (snd (projT1 idx')) (snd idx) ) then
      _ else (fun r1 r2 => HInd r1 r2)
  else (fun r1 r2 => HInd r1 r2).
Next Obligation.
  simpl in *.
  subst; apply X1.
  erewrite BuildQSSchema_idx_eq;
    [ eapply X
    | simpl; eauto].
  erewrite BuildQSSchema_idx_eq;
    [ eapply X0
    | simpl; eauto].
Defined.

Fixpoint BuildQueryStructureConstraints
(namedSchemas : list NamedSchema)
(constraints :
   list (sigT (fun idxs =>
                 Tuple (schemaHeading (BuildQSSchema namedSchemas (fst idxs)))
                 -> list (Tuple (schemaHeading (BuildQSSchema namedSchemas (snd idxs))))
                 -> Prop) ))
(idx : string * string) {struct constraints}
: Tuple (schemaHeading (BuildQSSchema namedSchemas (fst idx)))
  -> list (Tuple (schemaHeading (BuildQSSchema namedSchemas (snd idx))))
  -> Prop :=
  match constraints with
    | idx' :: constraints' =>
      @BuildQueryStructureConstraints_cons
        namedSchemas idx' constraints' idx
      (BuildQueryStructureConstraints namedSchemas constraints' idx)
    | nil => fun _ _ => True
  end.

Definition BuildQueryStructure
           (namedSchemas : list NamedSchema)
           constraints :=
  {| qschemaSchemas := namedSchemas;
     qschemaConstraints idx idx' := @BuildQueryStructureConstraints
                                      namedSchemas
                                      constraints (idx, idx') |}.

Notation "'query' 'structure' 'schema' relList " :=
  (BuildQueryStructure relList%NamedSchema []) : QSSchema_scope.

Notation "'query' 'structure' 'schema' relList 'enforcing' constraints" :=
  (BuildQueryStructure relList%NamedSchema
                       (let relListHint := Build_namedSchemaHint relList%NamedSchema in
                        constraints%QSSchemaConstraints)) : QSSchema_scope.

Arguments BuildForeignKeyConstraints _ _ [_ _] _ _ / .
Arguments BuildQueryStructureConstraints_cons [_] _ _ _ _ / _ _.
Arguments BuildQueryStructureConstraints_cons_obligation_1 [_] _ / _ _ _ _ _ _ _ .
Arguments eq_rect_r _ _ _ _ _ _ / .
Arguments ForeignKey_P _ _ _ _ _ / _ _ .
Arguments BuildQSSchema _ _ / .

Bind Scope QSSchema_scope with QueryStructureSchema.

Instance Astring_eq : Query_eq string := {| A_eq_dec := string_dec |}.

Require Import Omega.
Instance Anat_eq : Query_eq nat := {| A_eq_dec := eq_nat_dec |}.
