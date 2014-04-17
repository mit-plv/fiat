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

Definition GetNRelSchema
           (namedSchemas : list NamedSchema)
           (idx : string) :=
  relSchema (nth (findIndex NamedSchema_eq namedSchemas idx)
                 namedSchemas defaultSchema).

Definition GetNRelSchemaHeading
           (namedSchemas :  list NamedSchema)
           (idx : string)
:= schemaHeading (GetNRelSchema namedSchemas idx).

Definition crossRelationR
           (namedSchemas : list NamedSchema)
           (idx idx' : string)
  := Tuple (GetNRelSchemaHeading namedSchemas idx)
     -> list (Tuple (GetNRelSchemaHeading namedSchemas idx'))
     -> Prop.

Definition crossRelationProdR
           (namedSchemas : list NamedSchema)
           (idxs : string * string)
  := crossRelationR namedSchemas (fst idxs) (snd idxs).

Record QueryStructureSchema :=
  { qschemaSchemas : list NamedSchema;
    qschemaConstraints:
      list (sigT (crossRelationProdR qschemaSchemas))
  }.

Definition QSGetNRelSchema
           (QSSchema : QueryStructureSchema)
           (idx : string) :=
  GetNRelSchema (qschemaSchemas QSSchema) idx.

Definition QSGetNRelSchemaHeading
           (QSSchema : QueryStructureSchema)
           (idx : string) :=
  GetNRelSchemaHeading (qschemaSchemas QSSchema) idx.

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
    -> GetNRelSchema namedSchemas idx =
       GetNRelSchema namedSchemas idx'.
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
  (existT (crossRelationProdR namedSchemas)
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

Local Obligation Tactic := intros.

Program Definition BuildQueryStructureConstraints_cons
           (namedSchemas : list NamedSchema)
           (constr : sigT (crossRelationProdR namedSchemas))
           (constraints :
              list (sigT (crossRelationProdR namedSchemas)))
           (idx idx' : string)
           (HInd : crossRelationR namedSchemas idx idx')
: crossRelationR namedSchemas idx idx' :=
  if (string_dec (fst (projT1 constr)) idx) then
    if (string_dec (snd (projT1 constr)) idx') then
      _
    else (fun r1 r2 => HInd r1 r2)
 else (fun r1 r2 => HInd r1 r2).
Next Obligation.
  destruct constr; simpl in *.
  destruct (In_dec string_dec idx (map relName namedSchemas)).
  destruct (In_dec string_dec idx' (map relName namedSchemas)).
  subst; exact (fun X X0 => c X X0).
  exact (fun X X0 => True).
  exact (fun X X0 => True).
Defined.

Fixpoint BuildQueryStructureConstraints'
         (namedSchemas : list NamedSchema)
         (constraints :
            list (sigT (crossRelationProdR namedSchemas)))
(idx idx' : string) {struct constraints}
: crossRelationR namedSchemas idx idx' :=
  match constraints with
    | idx'' :: constraints' =>
      @BuildQueryStructureConstraints_cons
        namedSchemas idx'' constraints' idx idx'
      (BuildQueryStructureConstraints' constraints' idx idx')
    | nil => fun _ _ => True
  end.

Definition BuildQueryStructureConstraints qsSchema :=
  BuildQueryStructureConstraints' (qschemaConstraints qsSchema).

Notation "'query' 'structure' 'schema' relList " :=
  (@Build_QueryStructureSchema relList%NamedSchema []) : QSSchema_scope.

Notation "'query' 'structure' 'schema' relList 'enforcing' constraints" :=
  (@Build_QueryStructureSchema relList%NamedSchema
                       (let relListHint := Build_namedSchemaHint relList%NamedSchema in
                        constraints%QSSchemaConstraints)) : QSSchema_scope.

Arguments BuildForeignKeyConstraints _ _ [_ _] _ _ (*/*) .
Arguments BuildQueryStructureConstraints _ _ _ _ _.
Arguments BuildQueryStructureConstraints_cons [_] _ _ _ _ (*/*) _ _ _.

Arguments BuildQueryStructureConstraints_cons_obligation_1 [_] _ (*/*) _ _ _ _ _ _ _ _.
Arguments eq_rect_r _ _ _ _ _ _ / .
Arguments ForeignKey_P _ _ _ _ _ / _ _ .

Bind Scope QSSchema_scope with QueryStructureSchema.

Instance Astring_eq : Query_eq string := {| A_eq_dec := string_dec |}.

Require Import Omega.
Instance Anat_eq : Query_eq nat := {| A_eq_dec := eq_nat_dec |}.
