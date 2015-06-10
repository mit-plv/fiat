Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Logic.FunctionalExtensionality
        Coq.Sets.Ensembles
        Fiat.Common.ilist2
        Fiat.Common.StringBound
        Coq.Program.Program
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.QueryStructure.Specification.Representation.Notations.

(* A tuple is a heterogeneous list indexed by a heading. *)
Definition RawTuple {heading : RawHeading} :=
  ilist2 (B := id) (AttrList heading).

Definition Tuple {heading : Heading}
  := @RawTuple heading.

(* Notations for tuple field. *)

Record Component (Heading : Attribute) :=
  { value : attrType Heading }.

Notation "id :: value" :=
  (Build_Component {| attrName := id;
                      attrType := _ |}
                   value) : Component_scope.

Bind Scope Component_scope with Component.

(* Notation-friendly tuple definition. *)
Fixpoint BuildTuple
         {n}
         (attrs : Vector.t Attribute n)
  : ilist2 (B := Component) attrs -> @Tuple (BuildHeading attrs) :=
  match attrs return ilist2 (B := Component) attrs -> @Tuple (BuildHeading attrs) with
  | Vector.nil => fun components => inil2
  | Vector.cons attr n' attrs' =>
    fun components =>
      icons2 (B := id) (value (ilist2_hd components))
            (BuildTuple attrs' (ilist2_tl components))
  end.

(* Notation
for tuples built from [BuildTuple]. *)

Notation "< col1 , .. , coln >" :=
  (@BuildTuple _ _ (icons2 col1%Component .. (icons2 coln%Component inil2) ..))
  : Tuple_scope.

Definition GetAttributeRaw {heading}
: @RawTuple heading -> forall attr : Attributes heading, Domain heading attr := ith2.

Definition GetAttribute {heading}
  : @Tuple heading ->
    forall attr : @BoundedString _ (HeadingNames heading),
      Domain heading (ibound (indexb attr)) :=
  fun t idx => GetAttributeRaw t (ibound (indexb idx)).

Notation "t ! R" :=
  (GetAttribute t%Tuple (@Build_BoundedIndex _ _ _ R%string _))
  : Tuple_scope.

Definition SetAttributeRaw {heading}
: @RawTuple heading ->
  forall attr : Attributes heading,
    Domain heading attr -> @RawTuple heading :=
  fun tup attr dom => replace_Index2 _ tup attr dom.

Definition SetAttribute {heading}
: @Tuple heading ->
  forall attr : Attributes heading,
    Domain heading attr -> @Tuple heading :=
  fun tup attr dom => replace_Index2 _ tup attr dom.

Definition IndexedRawTuple {heading} := @IndexedElement (@RawTuple heading).
Definition RawTupleIndex {heading} (I : @IndexedRawTuple heading) : nat :=
  elementIndex I.
Definition indexedRawTuple {heading} (I : @IndexedRawTuple heading)
  : @RawTuple heading := indexedElement I.

Definition IndexedTuple {heading} := @IndexedElement (@Tuple heading).
Definition TupleIndex {heading} (I : @IndexedTuple heading) : nat :=
  elementIndex I.
Definition indexedTuple {heading} (I : @IndexedTuple heading)
: @Tuple heading := indexedElement I.
