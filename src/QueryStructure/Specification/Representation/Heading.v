Require Import Coq.Lists.List Coq.Strings.String Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Fiat.Common.ilist Fiat.Common.StringBound Coq.Program.Program
        Fiat.QueryStructure.Specification.Representation.Notations.

(* Notations for attributes. *)

Record Attribute :=
  { attrName : string;
    attrType : Type }.

Infix "::" := Build_Attribute : Attribute_scope.

Bind Scope Attribute_scope with Attribute.

Definition attrName_eq (cs : Attribute) (idx : string) :=
  if (string_dec (attrName cs) idx) then true else false .

(* A heading describes a tuple as a set of Attributes
   and types. *)
Record Heading :=
  { AttrList : list Attribute }.

Definition Attributes (heading : Heading) : Set :=
  @BoundedString (map attrName (AttrList heading)).

Definition Domain (heading : Heading) (idx : Attributes heading) : Type :=
  attrType (nth_Bounded _ (AttrList heading) idx).
Arguments Domain : clear implicits.

(* Notations for schemas. *)

Definition BuildHeading
           (attrs : list Attribute)
: Heading :=
  {| AttrList := attrs |}.

(* Notation for schemas built from [BuildHeading]. *)

Notation "< col1 , .. , coln >" :=
  (BuildHeading ( col1%Attribute :: .. (coln%Attribute :: []) ..))
  : Heading_scope.
