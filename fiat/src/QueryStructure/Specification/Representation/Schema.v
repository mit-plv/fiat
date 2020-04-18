Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Logic.FunctionalExtensionality
        Coq.Sets.Ensembles
        Fiat.Common.StringBound
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple.

(* A relation schema is a heading for the tuples of the
   relation and constraints on the members
   (usually functional dependencies). *)

Record RawSchema :=
  { rawSchemaHeading : RawHeading;
    attrConstraints: option (@RawTuple rawSchemaHeading
                             -> Prop);
    tupleConstraints: option (@RawTuple rawSchemaHeading
                             -> @RawTuple rawSchemaHeading
                             -> Prop)
  }.

Record Schema :=
  { schemaRaw :> RawSchema;
    schemaHeadingNames : Vector.t string (NumAttr (rawSchemaHeading schemaRaw)) }.

Definition schemaHeading (sch : Schema) : Heading :=
  {| HeadingRaw := rawSchemaHeading (schemaRaw sch);
     HeadingNames := schemaHeadingNames sch |}.

Class HeadingHint :=
  { headingHint :> Heading }.

(* A notation for functional dependencies. *)
Definition tupleAgree
           {h : RawHeading}
           (tup1 tup2 : @RawTuple h) attrlist :=
  forall attr,
    List.In attr attrlist ->
    GetAttributeRaw tup1 attr = GetAttributeRaw tup2 attr.

Definition AttributeList {hHint : HeadingHint}
  := list (Attributes headingHint).

Definition UniqueAttribute' {heading : RawHeading}
           attr
           (tup1 tup2 : @RawTuple heading) :=
  GetAttributeRaw tup1 attr <> GetAttributeRaw tup2 attr.

Definition UniqueAttribute {heading}
           (attr : BoundedString (HeadingNames heading)) :=
  UniqueAttribute' (ibound (indexb attr)).

Notation "[ attr1 ; .. ; attr2 ] " :=
  (cons (ibound (indexb (@Build_BoundedIndex _ _ (HeadingNames headingHint) attr1%string _)))
        .. (cons
                 (ibound (indexb ((@Build_BoundedIndex _ _  (HeadingNames headingHint) attr2%string _)))) nil) ..)
  : SchemaConstraints_scope.

Notation "[ attr1 ; attr2 ; .. ; attr3 ] " :=
  (cons (ibound (indexb (@Build_BoundedIndex _ _ (HeadingNames headingHint) attr1%string _)))
        (cons (ibound (indexb (@Build_BoundedIndex _ _ (HeadingNames headingHint) attr2%string _)))
              .. (cons
                    (ibound (indexb ((@Build_BoundedIndex _ _  (HeadingNames headingHint) attr3%string _)))) nil) ..))
  : SchemaConstraints_scope.

Definition FunctionalDependency_P
           (hHint : RawHeading)
  :  list (Attributes hHint)
     -> list (Attributes hHint)
     -> @RawTuple hHint
     -> @RawTuple hHint
     -> Prop :=
  fun attrlist1 attrlist2 tup1 tup2 =>
    tupleAgree tup1 tup2 attrlist2 ->
    tupleAgree tup1 tup2 attrlist1.

Notation "'attributes' attrlist1 'depend' 'on' attrlist2 " :=
  (let hint := @headingHint _ in
    (@FunctionalDependency_P hint : list (Attributes hint)
                                          -> list (Attributes hint)
                                          -> @RawTuple hint
                                          -> @RawTuple hint
                                          -> Prop)
     (attrlist1%SchemaConstraints : list (Attributes hint))
     (attrlist2%SchemaConstraints : list (Attributes hint)))
  : SchemaConstraints_scope.

(* Notations for Schemas. *)

Notation "'schema' headings' 'where' aconstraints 'and' tupconstraints" :=
  (let headings := headings'%Heading in
   {| schemaRaw :=
       {| rawSchemaHeading := headings;
          attrConstraints := @Some (@RawTuple headings
                                    -> Prop) (let hHint := {|headingHint := headings |} in
                                              aconstraints%SchemaConstraints);
          tupleConstraints :=
            @Some (@RawTuple headings
                   -> @RawTuple headings
                   -> Prop) (let hHint := {|headingHint := headings |} in
                             tupconstraints%SchemaConstraints) |};
     schemaHeadingNames := HeadingNames headings |})
       : Schema_scope.


Notation "'schema' headings' 'where' constraints" :=
    (let headings := headings'%Heading in
   {| schemaRaw :=
       {| rawSchemaHeading := headings;
          attrConstraints := None;
          tupleConstraints :=
            @Some (@RawTuple headings
                   -> @RawTuple headings
                   -> Prop) (let hHint := {|headingHint := headings |} in
                             constraints%SchemaConstraints) |};
      schemaHeadingNames := HeadingNames headings |})

       : Schema_scope.

Notation "'schema' headings'" :=
      (let headings := headings'%Heading in
       {| schemaRaw :=
            {| rawSchemaHeading := headings;
               attrConstraints := None;
               tupleConstraints := None |};
          schemaHeadingNames := HeadingNames headings |})
       : Schema_scope.
