Require Import
        Coq.Vectors.Vector
        Coq.Vectors.VectorDef
        Coq.Lists.List
        Coq.Strings.String
        Coq.Logic.FunctionalExtensionality
        Coq.Sets.Ensembles
        Fiat.Common.ilist
        Fiat.Common.StringBound
        Coq.Program.Program
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
Record RawHeading :=
  { NumAttr : nat;
    AttrList : Vector.t Type NumAttr }.

Definition Attributes (heading : RawHeading) : Set := Fin.t (NumAttr heading).

Definition Domain (heading : RawHeading) (idx : Attributes heading) : Type :=
  Vector.nth (AttrList heading) idx.
Arguments Domain : clear implicits.

(* Notations for schemas. *)

Record Heading :=
  { HeadingRaw :> RawHeading;
    HeadingNames : Vector.t string (NumAttr HeadingRaw) }.

Definition BuildHeading
           {n}
           (attrs : Vector.t Attribute n)
  : Heading :=
  {| HeadingRaw := {| NumAttr := n;
                      AttrList := Vector.map attrType attrs |};
     HeadingNames := Vector.map attrName attrs |}.

(* Notation for schemas built from [BuildHeading]. *)

Notation "< col1 , .. , coln >" :=
  (BuildHeading (@Vector.cons _ col1%Attribute _ .. (Vector.cons _ coln%Attribute _ (Vector.nil _)) ..))
  : Heading_scope.

(* Extending Headings *)
Definition AppendRawHeading (h1 h2 : RawHeading) : RawHeading :=
  {| NumAttr := NumAttr h1 + NumAttr h2;
     AttrList := Vector.append (AttrList h1) (AttrList h2) |}.

Definition AppendHeading (h1 h2 : Heading) : Heading :=
  {| HeadingRaw := AppendRawHeading (HeadingRaw h1) (HeadingRaw h2);
     HeadingNames := Vector.append (HeadingNames h1) (HeadingNames h2) |}.

Notation " h1 ++ h2 " := (AppendHeading h1%Heading h2%Heading) : Heading_scope.
