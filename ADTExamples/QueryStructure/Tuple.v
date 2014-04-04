Require Import List String FunctionalExtensionality Ensembles
        ADTNotation.ilist ADTNotation.StringBound Program Heading
        ADTExamples.QueryStructure.Notations.

(* A tuple is a map from attributes to values. *)
Definition Tuple (Heading : Heading) :=
  forall (i : Attributes Heading), Domain Heading i.

(* Notations for tuple field. *)

Record Component (Heading : Attribute) :=
  { value : attrType Heading }.

Notation "id : value" :=
  (Build_Component {| attrName := id;
                      attrType := _ |}
                   value) : Component_scope.

Bind Scope Component_scope with Component.

(* Notation-friendly tuple definition. *)

Definition DefaultAttribute :=
  Build_Component ("null" : unit)%Attribute tt.

Definition BuildTuple
        (attrs : list Attribute)
        (components : ilist Component attrs)
: Tuple (BuildHeading attrs) :=
  fun idx =>
    value (ith attrName_eq components idx _ DefaultAttribute).

(* Notation for tuples built from [BuildTuple]. *)

Notation "< col1 , .. , coln >" :=
  (@BuildTuple _ (icons _ col1%Component .. (icons _ coln%Component (inil _)) ..))
  : Tuple_scope.

Notation "t 's col" :=
  (t%Tuple {| bstring := col%string |}) : Tuple_scope.

Definition Title : string := "Title"%string .
Definition ReleaseDate : string := "ReleaseDate"%string.
