Require Import Coq.Lists.List Coq.Strings.String Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Fiat.Common.ilist Fiat.Common.StringBound Coq.Program.Program Fiat.QueryStructure.Specification.Representation.Heading2
        Fiat.Common.Ensembles.IndexedEnsembles Fiat.QueryStructure.Specification.Representation.Notations.

(* A tuple is a heterogeneous list indexed by a heading. *)
Definition Tuple2 {heading : Heading2} :=
  ilist attrType2 (AttrList2 heading).

(* Notations for tuple field. *)

Record Component2 (Heading : Attribute2) :=
  { value : attrType2 Heading }.

Notation "id :: value" :=
  (Build_Component2 {| attrName2 := id;
                       attrType2 := _ |}
                    value) : Component2_scope.

Bind Scope Component2_scope with Component2.
Delimit Scope Component2_scope with Component2.
Delimit Scope Tuple2_scope with Tuple2.
(* Notation-friendly tuple definition. *)

Fixpoint BuildTuple2
         (attrs : list Attribute2)
         (components : ilist Component2 attrs)
: @Tuple2 (BuildHeading2 attrs) :=
  match components with
    | icons _ _ x xs => icons _ (value x) (BuildTuple2 xs)
    | inil => inil _
  end.

(* Notation for tuples built from [BuildTuple]. *)

Notation "< col1 , .. , coln >" :=
  (@BuildTuple2 _ (icons _ col1%Component2 .. (icons _ coln%Component2 (inil _)) ..))
  : Tuple2_scope.

Definition GetAttribute2 {heading}
: @Tuple2 heading -> forall attr : Attributes2 heading, Domain2 heading attr :=
  ith_Bounded attrName2.

Definition getHeading2 {Bound} (tup : @Tuple2 (BuildHeading2 Bound))
: list string := map attrName2 Bound.

Definition GetAttribute2' {heading}
: @Tuple2 (BuildHeading2 heading) ->
  forall attr : @BoundedString (map attrName2 heading),
    Domain2 (BuildHeading2 heading) attr :=
  ith_Bounded attrName2.

Notation "t ! R" :=
  (GetAttribute2 t%Tuple2 (@Build_BoundedIndex _ _ R%string _))
  : Tuple2_scope.

Definition SetAttribute2 {heading}
: @Tuple2 heading ->
  forall attr : Attributes2 heading,
    Domain2 heading attr -> @Tuple2 heading :=
  replace_BoundedIndex attrName2 (Bound:=AttrList2 heading).
