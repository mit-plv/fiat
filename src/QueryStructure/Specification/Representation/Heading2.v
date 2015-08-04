Require Import Coq.Lists.List Coq.Strings.String Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Fiat.Common.ilist Fiat.Common.StringBound Coq.Program.Program
        Fiat.QueryStructure.Specification.Representation.Notations.

(* Notations for attributes. *)

Record Attribute2 :=
  { attrName2 : string;
    attrType2 : Type }.

Infix "::" := Build_Attribute2 : Attribute_scope.

Definition attrName_eq (cs : Attribute2) (idx : string) :=
  if (string_dec (attrName2 cs) idx) then true else false .

(* A heading describes a tuple as a set of Attributes
   and types. *)
Record RawHeading2 :=
  { NumAttr2 : nat;
    AttrList2 : Vector.t Type NumAttr2 }.

Definition Attributes2 (heading : RawHeading2) : Set := Fin.t (NumAttr2 heading).

Definition Domain2 (heading : RawHeading2) (idx : Attributes2 heading) : Type :=
  Vector.nth (AttrList2 heading) idx.
Arguments Domain2 : clear implicits.

(* Notations for schemas. *)

Record Heading2 :=
  { HeadingRaw2 :> RawHeading2;
    HeadingNames2 : Vector.t string (NumAttr2 HeadingRaw2) }.

Definition BuildHeading2
           {n}
           (attrs : Vector.t Attribute2 n)
  : Heading2 :=
  {| HeadingRaw2 := {| NumAttr2 := n;
                      AttrList2 := Vector.map attrType2 attrs |};
     HeadingNames2 := Vector.map attrName2 attrs |}.
