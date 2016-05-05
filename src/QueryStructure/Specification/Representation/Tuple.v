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

(* Always parse the heading argument in Heading scope. *)
Arguments Tuple [_%Heading].

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
  forall attr : @BoundedString _ (HeadingNames heading),
    Domain heading (ibound (indexb attr)) -> @Tuple heading :=
  fun tup attr dom => replace_Index2 _ tup (ibound (indexb attr)) dom.

(*Notation "tup '!!' attr '<-' v " := (SetAttribute tup (@Build_BoundedIndex _ _ _ attr%string _) v) : Tuple_scope. *)

Definition AppendTupleRaw
           {heading1 heading2}
           (tup1 : @RawTuple heading1)
           (tup2 : @RawTuple heading2)
  : @RawTuple (AppendRawHeading heading1 heading2) :=
  ilist2_app tup1 tup2.

Notation "tup1 ++ tup2" := (AppendTupleRaw tup1 tup2) : Tuple_scope.

Definition UpdateAttributeRaw
           {heading}
           (attr : Attributes heading)
           (f : Domain heading attr -> Domain heading attr)
           (tup : @RawTuple heading)
  : @RawTuple heading := update_Index2 _ tup _ f.

Definition UpdateAttribute
           {heading}
           (tup : @Tuple heading)
           (attr : @BoundedString _ (HeadingNames heading))
           (f : Domain heading (ibound (indexb attr))
                -> Domain heading (ibound (indexb attr)))
  : @Tuple heading := UpdateAttributeRaw _ f tup.

Definition UpdateAttributes
           {heading}
           (tup : @Tuple heading)
           (attrs :
              list (@sigT (@BoundedString _ (HeadingNames heading))
                          (fun attr => Domain heading (ibound (indexb attr))
                                       -> Domain heading (ibound (indexb attr)))))
  : @Tuple heading := fold_left (fun (tup' : @Tuple heading)
                                     attr => UpdateAttribute tup' (projT1 attr) (projT2 attr)) attrs tup.

Class HeadingHint := { headingHint : Heading }.

Notation "tup ○ f" :=
  (let H := _ in
   let _ := {| headingHint := H |} in
   @UpdateAttributes H tup f%Update%list) : Tuple_scope.

Notation "x !! attr / f" :=
  (@existT (@BoundedString _ (HeadingNames headingHint))
           (fun attr' => Domain _ (ibound (indexb attr'))
                        -> Domain _ (ibound (indexb attr')))
           (@Build_BoundedIndex _ _ _ attr%string _)
           (fun x => f)) : Update_scope.

Notation "attr ::= v" :=
  (@existT (@BoundedString _ (HeadingNames headingHint))
           (fun attr' => Domain _ (ibound (indexb attr'))
                        -> Domain _ (ibound (indexb attr')))
           (@Build_BoundedIndex _ _ _ attr%string _)
           (fun _ => v)) : Update_scope.

(*Notation "'UpdateTuple' tup '!' attrs " :=
    (UpdateAttribute tup (@Build_BoundedIndex _ _ _ attr%string _) f)
      (tup at level 0, at level 80, attr at level 0,
       f at level 0, no associativity) : Tuple_scope.*)

Section TupleNotationExamples.
  Local Open Scope Tuple_scope.

  Definition MovieHeading : Heading := <"title" :: string, "year" :: nat>%Heading.
  Definition GwW : Tuple := <"title" :: "Gone With the Wind"%string, "year" :: 1938>.
  Definition GwW' := Eval simpl in GwW ○ ["title" ::= "Gone With the Wind Part 2"%string].
  Definition DupleMovie : RawTuple := GwW ++ GwW'.

  Definition GwW'' (tup : @Tuple MovieHeading)
    : @Tuple MovieHeading :=
    tup ○ [old !! "title" / append old "Gone With the Wind Part 3"%string;
           "year" ::= 10].

End TupleNotationExamples.
(*
Notation "a ++= b" := (@UpdateTuple _ {|attrName := a; attrType := string|}
                             (fun o => Build_Component (_::_) (append (value o) b))) (at level 80).
Notation "a :+= b" := (@UpdateTuple _ {|attrName := a; attrType := list _|}
                             (fun o => Build_Component (_::_) (cons b (value o)))) (at level 80).
Notation "[ a ; .. ; c ]" := (compose a .. (compose c id) ..) : Update_scope.

Delimit Scope Update_scope with Update.
*)

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

Definition GetAttributeRawBnd {heading : Heading}
           (tup : @RawTuple heading)
           (idx : (BoundedIndex (HeadingNames heading)))
  : Domain heading (ibound (indexb idx)) :=
  GetAttributeRaw tup (ibound (indexb idx)).

(* Raw tuple field accessor notation *)
Notation "tup '!' idx" := (GetAttributeRaw tup ``idx) : TupleImpl_scope.
