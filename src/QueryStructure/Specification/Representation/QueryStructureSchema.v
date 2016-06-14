Require Import Coq.Lists.List
        Coq.Strings.String
        Fiat.Common
        Coq.Arith.Arith
        Coq.Logic.FunctionalExtensionality
        Coq.Sets.Ensembles
        Fiat.Common.StringBound.
Require Export
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.QueryStructure.Specification.Representation.Schema
        Fiat.QueryStructure.Specification.Representation.Relation.

Import Vectors.VectorDef.VectorNotations.

(* A Query Structure schema is a set of named relation
   schemas and a set of cross-relation constraints
   (i.e. foreign key constraints). *)

Record NamedSchema  :=
  { relName : string;
    relSchema : Schema
  }.

Definition GetNRelSchema
           {n}
           (namedSchemas : Vector.t RawSchema n)
           (idx : Fin.t n) :=
  Vector.nth namedSchemas idx.

Definition GetNRelSchemaHeading
           {n}
           (namedSchemas : Vector.t RawSchema n)
           (idx : Fin.t n)
  := rawSchemaHeading (GetNRelSchema namedSchemas idx).

Definition crossRelationR
           {n}
           (namedSchemas : Vector.t RawSchema n)
           (idx idx' : Fin.t n)
  := @RawTuple (GetNRelSchemaHeading namedSchemas idx)
     -> Ensemble (@IndexedRawTuple (GetNRelSchemaHeading namedSchemas idx'))
     -> Prop.

Definition crossRelationProdR
           {n}
           (namedSchemas : Vector.t RawSchema n)
           (idxs : _ * _)
  := crossRelationR namedSchemas (fst idxs) (snd idxs).

Record RawQueryStructureSchema :=
  { numRawQSschemaSchemas : nat;
    qschemaSchemas : Vector.t RawSchema numRawQSschemaSchemas;
    qschemaConstraints:
      list (sigT (crossRelationProdR qschemaSchemas))
  }.

Record QueryStructureSchema :=
  { numQSschemaSchemas : nat;
    QSschemaSchemas : Vector.t Schema numQSschemaSchemas;
    QSschemaConstraints:
      list (sigT (crossRelationProdR (Vector.map schemaRaw QSschemaSchemas)));
    QSschemaNames : Vector.t string numQSschemaSchemas  }.

Definition QueryStructureSchemaRaw
           (QSSchema : QueryStructureSchema)
  : RawQueryStructureSchema :=
  {| numRawQSschemaSchemas := numQSschemaSchemas QSSchema;
     qschemaConstraints := QSschemaConstraints QSSchema |}.

Coercion QueryStructureSchemaRaw : QueryStructureSchema >-> RawQueryStructureSchema.

Definition QSGetNRelSchema
           (QSSchema : QueryStructureSchema)
           (idx : BoundedString (QSschemaNames QSSchema)) :=
  Vector.nth (QSschemaSchemas QSSchema) (ibound (indexb idx)).

Definition QSGetNRelSchemaHeading
           (QSSchema : QueryStructureSchema)
           (idx : BoundedString (QSschemaNames QSSchema)) :=
  schemaHeading (QSGetNRelSchema QSSchema idx).

Notation GetHeading QSSchema index :=
  (@QSGetNRelSchemaHeading QSSchema (@Build_BoundedIndex _ _ _ index _)).

(* Notations for Query Structures. *)

Notation "'relation' name 'has' sch " :=
  {| relName := name%string;
     relSchema := sch%Schema
  |} : NamedSchema_scope.

Notation "[ rel1 ; .. ; reln ]" :=
  (@Vector.cons _ rel1 _ (.. (@Vector.cons _ reln _ (Vector.nil _)) .. )) : NamedSchema_scope.
Notation "[ rel1 ; rel2 ; .. ; reln ]" :=
  (@Vector.cons _ rel1 _ (@Vector.cons _ rel2 _ (.. (@Vector.cons _ reln _ (Vector.nil _)) .. ))) : NamedSchema_scope.

Bind Scope NamedSchema_scope with NamedSchema.

(* A notation for foreign key constraints. This gives us
  a pair of relation schema names and a predicate on
  tuples in those tables. We use the namedSchemaHint
  typeclass to get the typechecking to work. *)

Definition ForeignKey_P heading relSchema attr1 attr2 tupmap
           (tup : @RawTuple heading)
           (R : Ensemble (@IndexedRawTuple relSchema)) :=
  exists tup2,
    R tup2 /\
    GetAttributeRaw tup attr1 =
    tupmap (GetAttributeRaw (indexedRawTuple tup2) attr2).

Definition BuildForeignKeyConstraints
           {n}
           (namedSchemas : Vector.t RawSchema n)
           (rel1 rel2 : _)
           attr1
           attr2
           {tupmap} :=
  (existT (crossRelationProdR namedSchemas)
          (rel1, rel2)
          (ForeignKey_P attr1 attr2 tupmap)).

Class namedSchemaHint :=
  { numnSchemaHint : nat;
    nSchemaHint :> Vector.t Schema numnSchemaHint;
    nSchemaNamesHint :> Vector.t string numnSchemaHint}.

Notation "'attribute' attr 'for' rel1 'references' rel2 " :=
  (let hint : namedSchemaHint := _ in
   let rel1' := ibound (indexb (@Build_BoundedIndex _ _ (@nSchemaNamesHint hint) rel1%string _)) in
   let rel2' := ibound (indexb (@Build_BoundedIndex _ _ (@nSchemaNamesHint hint) rel2%string _)) in
   @BuildForeignKeyConstraints
     _ (Vector.map schemaRaw (@nSchemaHint hint)) rel1' rel2'
     (ibound (indexb (@Build_BoundedIndex _ _ (schemaHeadingNames (Vector.nth (@nSchemaHint hint) rel1')) attr%string _)))
     (ibound (indexb (@Build_BoundedIndex _ _ (schemaHeadingNames (Vector.nth (@nSchemaHint hint) rel2')) attr%string _)))
     id) : QSSchemaConstraints_scope.

Notation "'Query' 'Structure' 'Schema' relList 'enforcing' constraints" :=
  (let relNames := Vector.map relName relList%NamedSchema in
   let relSchemas := Vector.map relSchema relList%NamedSchema in
   @Build_QueryStructureSchema
     _ relSchemas
     (let relListHint := Build_namedSchemaHint relSchemas relNames in
          (constraints%QSSchemaConstraints)%list)
     relNames) : QSSchema_scope.

Arguments BuildForeignKeyConstraints _ _ [_ _] _ _ _ (*/*) .

Arguments eq_rect_r _ _ _ _ _ _ / .
(*Arguments ForeignKey_P _ _ _ _ _ / _ _ . *)


Notation "'Query' 'Structure' 'Schema' relList " :=
    (let relNames := Vector.map relName relList%NamedSchema in
   let relSchemas := Vector.map relSchema relList%NamedSchema in
   @Build_QueryStructureSchema _ relSchemas nil relNames) : QSSchema_scope.

Bind Scope QSSchema_scope with QueryStructureSchema.
Require Export Fiat.Common.DecideableEnsembles.

Instance Astring_eq : Query_eq string := {| A_eq_dec := string_dec |}.

Instance Anat_eq : Query_eq nat := {| A_eq_dec := eq_nat_dec |}.

Instance Query_eq_list {A : Type}
         {a_eq_dec : Query_eq A}
: Query_eq (list A) :=
  {| A_eq_dec := list_eq_dec (@A_eq_dec A a_eq_dec) |}.

Require Import Coq.NArith.NArith Coq.ZArith.ZArith.
Instance AN_eq : Query_eq N := {| A_eq_dec := N.eq_dec |}.
Instance AZ_eq : Query_eq Z := {| A_eq_dec := Z.eq_dec |}.

(*Notation GetAttributeKey Rel index :=
  ((fun x : Attributes (GetNRelSchemaHeading (qschemaSchemas _) Rel) => x)  {| bindex := index |}).

Notation GetRelationKey QSSchema index :=
  (@Build_BoundedIndex _ (map relName (qschemaSchemas QSSchema))
                      index _).

Notation RawTupleDef QSSchema index :=
  (@RawTuple (QSGetNRelSchemaHeading QSSchema {| bindex := index%string |})). *)
