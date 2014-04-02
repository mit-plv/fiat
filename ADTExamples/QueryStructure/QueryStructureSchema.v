Require Import List String FunctionalExtensionality Ensembles
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
        @Relation (qschemaSchema idx)
        -> @Relation (qschemaSchema idx')
        -> Prop
  }.

(* A notation for foreign key constraints. *)

Notation "'attribute' attr 'of' rel1 'references' rel2 " :=
  (sigT (fun ids => @Relation (fst ids)
                    -> Relation (snd ids)
                    -> Prop)
        ({| bstring := rel1%string|}, {| bstring := rel2%string|})
        (fun ids (R1 : Relation (fst ids))
             (R2 : Relation (snd ids)) =>
           forall tup1,
             rel R1 tup1 ->
             exists tup2,
               rel R2 tup2 /\
               (tup1 {| bstring := attr%string|} = tup2 {| bstring := attr%string|} )))
  : QSSchemaConstraints_scope.

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

Definition BuildQueryStructure
           (namedSchemas : list NamedSchema)
           constraints :=
  {| qschemaIndex :=
       BoundedString (map relName namedSchemas);
     qschemaSchema idx :=
       relSchema (nth (findIndex NamedSchema_eq namedSchemas idx)
                namedSchemas defaultSchema);
     qschemaConstraints := constraints%QSSchemaConstraints |}.

Notation "'query' 'structure' 'schema' relList " :=
  (BuildQueryStructure relList%NamedSchema (fun _ _ _ _ => True)) : QSSchema_scope.

Notation "'query' 'structure' 'schema' relList 'enforcing' constraints" :=
  (BuildQueryStructure relList%NamedSchema constraints) : QSSchema_scope.

Bind Scope QSSchema_scope with QueryStructureSchema.
