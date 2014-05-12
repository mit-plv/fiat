Require Import List String FunctionalExtensionality Ensembles
        ADTNotation.ilist ADTNotation.StringBound Program Heading
        ADTExamples.QueryStructure.Notations.

(* A tuple is a map from attributes to values. *)
Definition Tuple (Heading : Heading) :=
  forall (i : Attributes Heading), Domain Heading i.

(* Notations for tuple field. *)

Record Component (Heading : Attribute) :=
  { value : attrType Heading }.

Notation "id :: value" :=
  (Build_Component {| attrName := id;
                      attrType := _ |}
                   value) : Component_scope.

Bind Scope Component_scope with Component.

(* Notation-friendly tuple definition. *)

Definition DefaultAttribute :=
  Build_Component ("null" :: unit)%Attribute tt.

Definition BuildTuple
        (attrs : list Attribute)
        (components : ilist Component attrs)
: Tuple (BuildHeading attrs) :=
  fun idx =>
    value (ith_Bounded _ components idx).

(* Notation for tuples built from [BuildTuple]. *)

Notation "< col1 , .. , coln >" :=
  (@BuildTuple _ (icons _ col1%Component .. (icons _ coln%Component (inil _)) ..))
  : Tuple_scope.

Definition GetAttribute
           {heading}
           (tup : Tuple heading)
           (attr : Attributes heading)
: Domain heading attr :=
  tup attr.

Notation "t ! R" :=
  (GetAttribute t%Tuple R%string): Tuple_scope.

Arguments Tuple [Heading] .
