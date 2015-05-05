Require Import Coq.Lists.List Coq.Strings.String Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Fiat.Common.ilist Fiat.Common.StringBound Coq.Program.Program
        Fiat.QueryStructure.Specification.Representation.Notations.

(* Duplicate notations for attributes to avoid universe inconsistencies. *)

Record Attribute2 :=
  { attrName2 : string;
    attrType2 : Type }.

Infix "::" := Build_Attribute2 : Attribute2_scope.

Bind Scope Attribute2_scope with Attribute2.

Definition attrName2_eq (cs : Attribute2) (idx : string) :=
  if (string_dec (attrName2 cs) idx) then true else false .

(* A heading describes a tuple as a set of Attributes
   and types. *)
Record Heading2 :=
  { AttrList2 : list Attribute2 }.

Definition Attributes2 (heading : Heading2) : Set :=
  @BoundedString (map attrName2 (AttrList2 heading)).

Definition Domain2 (heading : Heading2) (idx : Attributes2 heading) : Type :=
  attrType2 (nth_Bounded _ (AttrList2 heading) idx).
Arguments Domain2 : clear implicits.

(* Notations for schemas. *)

Definition BuildHeading2
           (attrs : list Attribute2)
: Heading2 :=
  {| AttrList2 := attrs |}.

(* Notation for schemas built from [BuildHeading]. *)

Notation "< col1 , .. , coln >" :=
  (BuildHeading2 ( col1%Attribute :: .. (coln%Attribute :: []) ..))
  : Heading2_scope.

Delimit Scope Heading2_scope with Heading2.
