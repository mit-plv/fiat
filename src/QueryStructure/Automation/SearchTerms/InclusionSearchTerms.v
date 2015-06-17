Require Import
        Coq.Strings.String
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Specification.SearchTerms.ListInclusion
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Automation.Common.

(* Instances for building indexes with make simple indexes. *)
(* Every Kind of index is keyed on an inductive type with a single constructor*)
Local Open Scope string_scope.
Definition InclusionIndex : string := "InclusionIndex".

(* This is our search term type. *)
Record InvertedSearchTerm
       (heading : RawHeading)
  :=
    { IndexSearchTerm : list string;
      ItemSearchTerm : @RawTuple heading -> bool }.

(* This builds the type of searchterms and the matching function on them *)
Global Instance InvertedIndexDenotation
       (heading : RawHeading)
       (index : @Attributes heading)
       (projection : @RawTuple heading -> list string)
: @IndexDenotation "InclusionIndex" heading index :=
  {| DenoteIndex := InvertedSearchTerm heading; (* Pick search term type *)
     MatchIndex search_term item := (* matching function : DenoteIndex -> Tuple heading -> bool *)
       if IncludedIn_dec (IndexSearchTerm search_term) (projection item) then
         ItemSearchTerm search_term item
       else false |}.

(* Extra type class magic for inverted indices. *)
Hint Extern 10 (@IndexDenotation "InclusionIndex" ?heading ?index) =>
let index_domain := eval hnf in (@Domain heading index) in
match index_domain with
  | list string =>
    apply (@InvertedIndexDenotation
             heading index
             (fun tup => GetAttributeRaw tup index ))
end
: typeclass_instances.

Ltac matchInclusionIndex qsSchema WhereClause k k_fail :=
  match WhereClause with
  | fun tups => IncludedIn _ (@?C1 tups) =>
    TermAttributes C1 ltac:(fun Ridx attr =>
                              k (@InsertOccurence _ qsSchema Ridx (InclusionIndex, attr) (InitOccurence _)))
  | _ => k_fail qsSchema WhereClause k
  end.

Ltac InclusionIndexUse SC F indexed_attrs f k k_fail :=
     match type of f with
       (* Inclusion Search Terms *)
       | forall a, {IncludedIn ?X (GetAttributeRaw _ ?fd)} + {_} =>
          let H := fresh in
          assert (List.In (@Build_KindIndex SC "InclusionIndex" fd) indexed_attrs) as H
              by (clear; subst_all; simpl; intuition eauto); clear H;
            k (@Build_KindIndex SC "InclusionIndex" fd, X) (fun _ : @RawTuple SC => true)
       | _ => k_fail SC F indexed_attrs f k
     end.

Ltac InclusionIndexUse_dep SC F indexed_attrs visited_attrs f T k k_fail :=
  match type of f with
  | forall a b, {IncludedIn (@?X a) (GetAttributeRaw _ ?fd)} + {_} =>
    let H := fresh in
    assert (List.In (@Build_KindIndex SC "InclusionIndex" fd) indexed_attrs) as H
        by (clear; subst_all; simpl; intuition eauto); clear H;
    match eval simpl in
          (in_dec fin_eq_dec fd visited_attrs) with
            | right _ => k (fd :: visited_attrs)
                           (@Build_KindIndex SC "InclusionIndex" fd, X)
                           (fun (a : T) (_ : @RawTuple SC) => true)
            | left _ => k visited_attrs tt F
          end
    | _ => k_fail SC F indexed_attrs visited_attrs f T k
  end.

Ltac createLastInclusionTerm f fds tail fs kind s k k_fail :=
  let is_equality := eval compute in (string_dec kind "InclusionIndex") in
      match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k {| IndexSearchTerm := X;
                                 ItemSearchTerm := tail |}))
            || k {| IndexSearchTerm := nil;
                    ItemSearchTerm := tail |}
        | _ => k_fail f fds tail fs kind s k
      end.

Ltac createLastInclusionTerm_dep dom f fds tail fs kind s k k_fail :=
  let is_equality := eval compute in (string_dec kind "InclusionIndex") in
      match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k (fun x : dom => {| IndexSearchTerm := X x;
                                                 ItemSearchTerm := tail x |}))
                    || k (fun x : dom => {| IndexSearchTerm := nil;
                                            ItemSearchTerm := tail x |}))
        | _ => k_fail dom f fds tail fs kind s k
      end.

Ltac createEarlyInclusionTerm f fds tail fs kind EarlyIndex LastIndex rest s k k_fail :=
  let is_equality := eval compute in (string_dec kind "InclusionIndex") in
      match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k (X, rest)))
            || k (@nil string, rest)
        | _ => k_fail f fds tail fs kind EarlyIndex LastIndex rest s k
      end.

Ltac createEarlyInclusionTerm_dep dom f fds tail fs kind EarlyIndex LastIndex rest s k k_fail :=
  let is_equality := eval compute in (string_dec kind "InclusionIndex") in
      match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k (fun x : dom => (X x, rest x))))
            || k (fun x : dom => (@nil string, rest x))
        | _ => k_fail dom f fds tail fs kind EarlyIndex LastIndex rest s k
      end.

Ltac InclusionIndexTactics f :=
  PackageIndexTactics
    matchInclusionIndex
    InclusionIndexUse createEarlyInclusionTerm createLastInclusionTerm
    InclusionIndexUse_dep createEarlyInclusionTerm_dep createLastInclusionTerm_dep f.
