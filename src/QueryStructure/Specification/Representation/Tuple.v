Require Import Coq.Lists.List Coq.Strings.String Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        ADTSynthesis.Common.ilist ADTSynthesis.Common.StringBound Coq.Program.Program ADTSynthesis.QueryStructure.Specification.Representation.Heading
        ADTSynthesis.Common.Ensembles.IndexedEnsembles ADTSynthesis.QueryStructure.Specification.Representation.Notations.

Definition Tuple {heading : Heading} :=
  ilist attrType (AttrList heading).

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
         (attrs : list Attribute)
         (components : ilist Component attrs)
: @Tuple (BuildHeading attrs) :=
  match components with
    | icons _ _ x xs => icons _ (value x) (BuildTuple xs)
    | inil => inil _
  end.

(* Notation for tuples built from [BuildTuple]. *)

Notation "< col1 , .. , coln >" :=
  (@BuildTuple _ (icons _ col1%Component .. (icons _ coln%Component (inil _)) ..))
  : Tuple_scope.

Definition GetAttribute {heading}
: @Tuple heading -> forall attr : Attributes heading, Domain heading attr :=
  ith_Bounded attrName.

Definition getHeading {Bound} (tup : @Tuple (BuildHeading Bound))
: list string := map attrName Bound.

Definition GetAttribute' {heading}
: @Tuple (BuildHeading heading) ->
  forall attr : @BoundedString (map attrName heading),
    Domain (BuildHeading heading) attr :=
  ith_Bounded attrName.

Notation "t ! R" :=
  (GetAttribute' t%Tuple (@Build_BoundedIndex _ _ R%string _))
  : Tuple_scope.

Definition SetAttribute {heading}
: @Tuple heading ->
  forall attr : Attributes heading,
    Domain heading attr -> @Tuple heading :=
  replace_BoundedIndex attrName (Bound:=AttrList heading).

Definition IndexedTuple {heading} := @IndexedElement (@Tuple heading).
Definition tupleIndex {heading} (I : @IndexedTuple heading) : nat :=
  elementIndex I.
Definition indexedTuple {heading} (I : @IndexedTuple heading)
: @Tuple heading := indexedElement I.
