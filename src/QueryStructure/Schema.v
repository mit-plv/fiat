Require Import List String FunctionalExtensionality Ensembles
        Common.ilist ADTNotation.StringBound Program
        QueryStructure.Notations
        Heading Tuple.

(* A relation schema is a heading for the tuples of the
   relation and constraints on the members
   (usually functional dependencies). *)

Record Schema :=
  { schemaHeading : Heading;
    schemaConstraints: option (@Tuple schemaHeading
                               -> @Tuple schemaHeading
                               -> Prop)
  }.

(* A notation for functional dependencies. *)

Definition tupleAgree
           {h : Heading}
           (tup1 tup2 : @Tuple h) attrlist :=
  forall attr,
    List.In attr attrlist ->
    tup1 attr = tup2 attr.

Notation "[ attr1 ; .. ; attr2 ] " :=
  ({|bindex := attr1%string |} :: .. ({| bindex := attr2%string |} :: nil) ..)
  : SchemaConstraints_scope.

Notation "'attributes' attrlist1 'depend' 'on' attrlist2 " :=
  (fun tup1 tup2 : @Tuple _ =>
          tupleAgree tup1 tup2 attrlist2%SchemaConstraints ->
          tupleAgree tup1 tup2 attrlist1%SchemaConstraints)
  : SchemaConstraints_scope.

(* Notations for Schemas. *)

Notation "'schema' headings 'where' constraints" :=
  {| schemaHeading := headings%Heading;
     schemaConstraints :=
       @Some (@Tuple headings%Heading
              -> @Tuple headings%Heading
              -> Prop) constraints%SchemaConstraints |} : Schema_scope.

Notation "'schema' headings" :=
  {| schemaHeading := headings%Heading;
     schemaConstraints := None |} : Schema_scope.
