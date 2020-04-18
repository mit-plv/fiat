Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Logic.FunctionalExtensionality
        Coq.Sets.Ensembles
        Fiat.Common.ilist2
        Fiat.Common.StringBound
        Coq.Program.Program
        Fiat.QueryStructure.Specification.Representation.Heading2
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.QueryStructure.Specification.Representation.Notations.

(* A tuple is a heterogeneous list indexed by a heading. *)
Definition Tuple2 {heading : RawHeading2} :=
  ilist2 (B := id) (AttrList2 heading).

Definition DecTuple2 {n} attrs
  := @Tuple2 (BuildHeading2 (n := n) attrs).

(* Notations for tuple field. *)

Record Component2 (Heading : Attribute2) :=
  { value2 : attrType2 Heading }.

(* Notation-friendly tuple definition. *)

Fixpoint BuildTuple2
         {n}
         (attrs : Vector.t Attribute2 n)
  : ilist2 (B := Component2) attrs -> DecTuple2 attrs :=
  match attrs return ilist2 (B := Component2) attrs -> DecTuple2 attrs with
  | Vector.nil => fun components => inil2
  | Vector.cons attr n' attrs' =>
    fun components =>
      icons2 (B := id) (value2 (ilist2_hd components))
            (BuildTuple2 attrs' (ilist2_tl components))
  end.

Definition GetAttribute2 {heading}
: @Tuple2 heading -> forall attr : Attributes2 heading, Domain2 heading attr := ith2.

Definition GetAttribute2' {n} {attrs}
  : @DecTuple2 n attrs ->
    forall attr : @BoundedString _ (Vector.map attrName2 attrs),
      Domain2 (BuildHeading2 attrs) (ibound (indexb attr)) :=
  fun t idx => ith2 t (ibound (indexb idx)).

Definition SetAttribute2 {heading}
: @Tuple2 heading ->
  forall attr : Attributes2 heading,
    Domain2 heading attr -> @Tuple2 heading :=
  fun tup attr dom => replace_Index2 _ tup attr dom.

Definition SetAttribute2' {n} {attrs}
  : @DecTuple2 n attrs ->
    forall attr : @BoundedString _ (Vector.map attrName2 attrs),
      Domain2 (HeadingRaw2 (BuildHeading2 attrs)) (ibound (indexb attr))
      -> @DecTuple2 n attrs :=
  fun tup attr dom => SetAttribute2 tup (ibound (indexb attr)) dom.


Notation "id :: value" :=
  (Build_Component2 {| attrName2 := id;
                       attrType2 := _ |}
                    value) : Component2_scope.

Bind Scope Component2_scope with Component2.
Delimit Scope Component2_scope with Component2.
Delimit Scope Tuple2_scope with Tuple2.
(* Notation for tuples built from [BuildTuple2]. *)
