Require Import
        Coq.Lists.List
        Coq.Program.Program
        Coq.Bool.Bool
        Coq.Strings.String
        Fiat.Common.ilist
        Fiat.Common.ilist2
        Fiat.Common.ilist3
        Fiat.Common.DecideableEnsembles
        Fiat.Common.StringBound
        Fiat.ADTNotation
        Fiat.ADTRefinement
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation
        Fiat.ADTRefinement.BuildADTRefinements.HoneRepresentation.
(* Definitions for building BagADT search terms using decideable equalities
   over named attributes.*)

(* Implements a Search Term for heading as a list of optional key
   values given a list of attributes. *)

Local Open Scope string_scope.

Definition EqualityIndex : string := "EqualityIndex".

Ltac BuildLastEqualityIndex
     heading indices kind index k k_fail :=
  let is_equality := eval compute in (string_dec kind EqualityIndex) in
      let A' := eval compute in (Domain heading index) in
      match is_equality with
      | left _ => k
                    (fun (search_term : prod (option (Domain heading index)) (@RawTuple heading -> bool))
                         (tup : @RawTuple heading) =>
           match fst search_term with
           | Some val =>
                 if A_eq_dec (A := A') (GetAttributeRaw tup index) val then
                           true
                         else false
           | _ => true
           end && (snd search_term) tup)
      | right _ => k_fail heading indices kind index k
      end.

Ltac BuildEarlyEqualityIndex
     heading indices kind index matcher k k_fail :=
  let is_equality := eval compute in (string_dec kind EqualityIndex) in
      let A' := eval compute in (Domain heading index) in
      match is_equality with
      | left _ => k
                    (fun (search_term : prod (option (Domain heading index)) _)
                     (tup : @RawTuple heading) =>
           match fst search_term with
           | Some val =>
                 if A_eq_dec (A := A') (GetAttributeRaw tup index) val then
                   true
                         else false
           | _ => true
           end && matcher (snd search_term) tup)
      | right _ => k_fail heading indices kind index matcher k
      end.

(*Ltac BuildIndexSearchTerm'
     attrs heading indices DenoteIndex k :=
  match indices with
    | [(?kind, ?idx)] =>
      k (@DenoteIndex kind heading (@Build_BoundedIndex _ attrs idx _) _)
    | (?kind, ?idx) :: ?indices' =>
      BuildIndexSearchTerm' attrs heading indices'
                           ltac:(fun st' =>
                                   k (prod (@DenoteIndex kind heading
                                                         (@Build_BoundedIndex _ attrs idx _)  _) st'))
  end. *)

Ltac BuildIndexMatcher' heading indices BuildEarlyIndex BuildLastIndex k :=
  match indices with
    | [] =>
      k (fun (st : (@RawTuple heading -> bool))=> st)
    | [(?kind, ?idx)] =>
      BuildLastIndex heading indices kind idx k
    | (?kind, ?idx) :: ?indices' =>
      BuildIndexMatcher'
        heading indices' BuildEarlyIndex BuildLastIndex
        ltac:(fun matcher =>
                BuildEarlyIndex heading indices kind idx matcher k)
  end.

Record KindIndex
       {heading : RawHeading}
  := { KindIndexKind : string;
       KindIndexIndex : @Attributes heading }.

  Ltac BuildIndexes
       heading indices k :=
    match indices with
    | [] =>
      k (@nil (@KindIndex heading))
    | [(?kind, ?idx)] =>
      k ([@Build_KindIndex heading kind idx])
    | (?kind, ?idx) :: ?indices' =>
      BuildIndexes heading indices'
                   ltac:(fun indices'' =>
                           k ((@Build_KindIndex heading kind idx) :: indices''))
  end.

(* Aliases to make existing automation happy. *)
Definition BuildIndexSearchTerm
           {heading : RawHeading}
           (indices : list (@KindIndex heading))
           {BuildIndexSearchTermT : Type}
: Type := BuildIndexSearchTermT.

Definition MatchIndexSearchTerm
           {heading : RawHeading}
           {indices : list (@KindIndex heading)}
           {IndexSearchTermT : Type}
           {matcher : IndexSearchTermT -> @RawTuple heading -> bool} :
  @BuildIndexSearchTerm heading indices IndexSearchTermT
  -> @RawTuple heading -> bool := matcher.

(*Fixpoint BuildIndexSearchTerm {heading : RawHeading}
         (indices : list (@Attributes heading))
: Type :=
  match indices with
    | [] => (@Tuple heading -> bool)
    | idx :: indices' => prod (option (Domain heading idx)) (BuildIndexSearchTerm indices')
  end. *)

(* Implements a matcher function for a search term built using [BuildSearchTerm].
Fixpoint MatchIndexSearchTerm {heading}
         {indices : list (@Attributes heading)}
         {eq_dec_indices : ilist (fun attr => Query_eq (Domain heading attr)) indices}
: BuildIndexSearchTerm indices -> @Tuple heading -> bool :=
  match indices return
        ilist (fun attr => Query_eq (Domain heading attr)) indices
        -> BuildIndexSearchTerm indices -> @Tuple heading -> bool
  with
    | nil => fun _ f tup => f tup
    | index :: indices' =>
      fun (eq_dec_indices : ilist (fun attr => Query_eq (Domain heading attr))
                                  (index :: indices')) =>
         (fun (H : BuildIndexSearchTerm indices' -> @Tuple heading -> bool)
              (f : prod (option (Domain heading index))
                        (BuildIndexSearchTerm indices'))
              (tup : @Tuple heading) =>
            match f with
              | (Some k, index') =>
                (if (A_eq_dec (Query_eq := ilist_hd eq_dec_indices) k (GetAttribute tup index))
                 then true else false)
                  && (H index' tup)
              | (None, index') => H index' tup
            end) (@MatchIndexSearchTerm _ _ (ilist_tl eq_dec_indices))
  end eq_dec_indices. *)

Tactic Notation "build" "single" "index":=
repeat match goal with
         | [ |- ilist (fun ns => SearchUpdateTerms (rawSchemaHeading (relSchema ns))) [] ] =>
           econstructor 2
         | [ |- ilist (fun ns => SearchUpdateTerms (rawSchemaHeading (relSchema ns)))
                      (?sch :: ?sch') ]=> econstructor 1; [ econstructor | ]
         | [ |- ilist (fun ns => SearchUpdateTerms (rawSchemaHeading (relSchema ns))) ?sch] =>
           simpl sch
       end.

(* Ltac build_index_list heading As k :=
  match As with
    | nil => k (inil (fun attr : Attributes heading => Query_eq (Domain heading attr)))
    | cons ?a ?As' =>
      build_index_list heading As'
                       ltac:(fun Bs' =>
                               k (let a : Attributes heading := {| bindex := a; indexb := _ |} in
                                   icons
                                    (B := (fun attr : Attributes heading => Query_eq (Domain heading attr)))
                                    a
                                    (_ : Query_eq (Domain heading a))
                                    Bs'))
  end. *)

Ltac makeIndex' schemas IndexKeys BuildEarlyIndex BuildLastIndex k :=
  match schemas  with
    | Vector.nil _ => k (inil3 (B := fun sch : RawHeading => SearchUpdateTerms sch))
    | Vector.cons _ ?sch _ ?schemas' =>
      let ik := eval simpl in (prim_fst IndexKeys) in
      let IndexKeys' := eval simpl in (prim_snd IndexKeys) in
      let heading' := eval simpl in (rawSchemaHeading sch) in
          BuildIndexes heading' ik
                       ltac:(fun attrs' =>
                               BuildIndexMatcher' heading' ik
                                                  BuildEarlyIndex BuildLastIndex
                                                  ltac:(fun matcher' =>
                                                          makeIndex' schemas' IndexKeys'
                                                                     BuildEarlyIndex BuildLastIndex
                                                                     ltac:(fun Bs' => k (icons3 (a := heading')
                                                                                                {| BagMatchSearchTerm := @MatchIndexSearchTerm heading' attrs' _ matcher';
                                                                                                   BagApplyUpdateTerm := fun z => z |} Bs'))))
  end.
