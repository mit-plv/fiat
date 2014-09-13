Require Import List String Common Arith
        FunctionalExtensionality Ensembles
        ADTNotation.ilist ADTNotation.StringBound Program.
Require Export
        QueryStructure.Notations
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

Definition GetNRelSchema
           (namedSchemas : list NamedSchema)
           (idx : @BoundedString (map relName namedSchemas)) :=
  relSchema (nth_Bounded _ namedSchemas idx).

Definition GetNRelSchemaHeading
           (namedSchemas :  list NamedSchema)
           (idx : @BoundedString (map relName namedSchemas))
:= schemaHeading (GetNRelSchema namedSchemas idx).

Definition crossRelationR
           (namedSchemas : list NamedSchema)
           (idx idx' : _)
  := @Tuple (GetNRelSchemaHeading namedSchemas idx)
     -> Ensemble (@IndexedTuple (GetNRelSchemaHeading namedSchemas idx'))
     -> Prop.

Definition crossRelationProdR
           (namedSchemas : list NamedSchema)
           (idxs : _ * _)
  := crossRelationR namedSchemas (fst idxs) (snd idxs).

Record QueryStructureSchema :=
  { qschemaSchemas : list NamedSchema;
    qschemaConstraints:
      list (sigT (crossRelationProdR qschemaSchemas))
  }.

Definition QSGetNRelSchema
           (QSSchema : QueryStructureSchema)
           (idx : _) :=
  GetNRelSchema (qschemaSchemas QSSchema) idx.

Definition QSGetNRelSchemaHeading
           (QSSchema : QueryStructureSchema)
           (idx : _) :=
  GetNRelSchemaHeading (qschemaSchemas QSSchema) idx.

Notation GetHeading QSSchema index :=
  (@QSGetNRelSchemaHeading QSSchema (@Build_BoundedIndex _ _ index _)).


(* Notations for Query Structures. *)

Notation "'relation' name 'has' sch " :=
  {| relName := name%string;
     relSchema := sch%Schema
  |} : NamedSchema_scope.

Bind Scope NamedSchema_scope with NamedSchema.

Lemma BuildQSSchema_idx_eq
      (namedSchemas : list NamedSchema)
: forall idx idx' : _,
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
           (tup : @Tuple heading)
           (R : Ensemble (@IndexedTuple relSchema)) :=
  exists tup2,
    R tup2 /\
    tup attr1 =
    tupmap ((indexedTuple tup2) attr2 ).

Definition BuildForeignKeyConstraints
           (namedSchemas :  list NamedSchema)
           (rel1 rel2 : _)
           attr1
           attr2
           {tupmap} :=
  (existT (crossRelationProdR namedSchemas)
          (rel1, rel2)
          (ForeignKey_P attr1 attr2 tupmap)).

Class namedSchemaHint :=
  { nSchemaHint :> list NamedSchema }.

Notation "'attribute' attr 'for' rel1 'references' rel2 " :=
  (
      @BuildForeignKeyConstraints
        (@nSchemaHint _) {| bindex := rel1%string |} {| bindex := rel2%string |}
        {| bindex := attr%string |}
        {| bindex := attr%string |} id) : QSSchemaConstraints_scope.

Notation "'Query' 'Structure' 'Schema' relList 'enforcing' constraints" :=
  (@Build_QueryStructureSchema relList%NamedSchema
                       (let relListHint := Build_namedSchemaHint relList%NamedSchema in
                        constraints%QSSchemaConstraints)) : QSSchema_scope.

Arguments BuildForeignKeyConstraints _ _ [_ _] _ _ (*/*) .

Arguments eq_rect_r _ _ _ _ _ _ / .
(*Arguments ForeignKey_P _ _ _ _ _ / _ _ . *)

Notation "'Query' 'Structure' 'Schema' relList " :=
  (@Build_QueryStructureSchema relList%NamedSchema []) : QSSchema_scope.

Bind Scope QSSchema_scope with QueryStructureSchema.

Instance Astring_eq : Query_eq string := {| A_eq_dec := string_dec |}.

Instance Anat_eq : Query_eq nat := {| A_eq_dec := eq_nat_dec |}.

Require Import NArith ZArith.
Instance AN_eq : Query_eq N := {| A_eq_dec := N.eq_dec |}.
Instance AZ_eq : Query_eq Z := {| A_eq_dec := Z.eq_dec |}.

Notation GetAttributeKey Rel index :=
  ((fun x : Attributes (GetNRelSchemaHeading (qschemaSchemas _) Rel) => x)  {| bindex := index |}).

Notation GetRelationKey QSSchema index :=
  (@Build_BoundedIndex _ (map relName (qschemaSchemas QSSchema))
                      index _).

Notation TupleDef QSSchema index :=
  (@Tuple (QSGetNRelSchemaHeading QSSchema {| bindex := index%string |})).
