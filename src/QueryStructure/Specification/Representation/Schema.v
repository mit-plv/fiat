Require Import Coq.Lists.List Coq.Strings.String Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        ADTSynthesis.Common.ilist ADTSynthesis.Common.StringBound Coq.Program.Program
        ADTSynthesis.QueryStructure.Specification.Representation.Notations
        ADTSynthesis.QueryStructure.Specification.Representation.Heading ADTSynthesis.QueryStructure.Specification.Representation.Tuple.

(* A relation schema is a heading for the tuples of the
   relation and constraints on the members
   (usually functional dependencies). *)

Record Schema :=
  { schemaHeading : Heading;
    schemaConstraints: option (@Tuple schemaHeading
                               -> @Tuple schemaHeading
                               -> Prop)
  }.

Class HeadingHint :=
  { headingHint :> Heading }.

(* A notation for functional dependencies. *)
Definition tupleAgree
           {h : Heading}
           (tup1 tup2 : @Tuple h) attrlist :=
  forall attr,
    List.In attr attrlist ->
    tup1 attr = tup2 attr.

Definition AttributeList {hHint : HeadingHint}
  := list (Attributes headingHint).

Notation "[ attr1 ; .. ; attr2 ] " :=
  (cons (@Build_BoundedIndex _ _ attr1%string _)
        .. (cons
                 (@Build_BoundedIndex _ _ attr2%string _) nil) ..)
  : SchemaConstraints_scope.

Definition FunctionalDependency_P
           (hHint : Heading)
:  list (Attributes hHint)
   -> list (Attributes hHint)
   -> @Tuple hHint
   -> @Tuple hHint
   -> Prop :=
  fun attrlist1 attrlist2 tup1 tup2 =>
    tupleAgree tup1 tup2 attrlist2 ->
    tupleAgree tup1 tup2 attrlist1.

Notation "'attributes' attrlist1 'depend' 'on' attrlist2 " :=
  ((@FunctionalDependency_P headingHint : list BoundedString -> _)
     (attrlist1%SchemaConstraints : list BoundedString)
     (attrlist2%SchemaConstraints : list BoundedString))
  : SchemaConstraints_scope.

(* Notations for Schemas. *)

Notation "'schema' headings 'where' constraints" :=
  {| schemaHeading := headings%Heading;
     schemaConstraints :=
       @Some (@Tuple headings%Heading
              -> @Tuple headings%Heading
              -> Prop) (let hHint := {|headingHint := headings%Heading |} in
                        constraints%SchemaConstraints) |} : Schema_scope.

Notation "'schema' headings" :=
  {| schemaHeading := headings%Heading;
     schemaConstraints := None |} : Schema_scope.
