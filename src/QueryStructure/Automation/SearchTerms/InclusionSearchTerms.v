Require Import
        Coq.Strings.String
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureNotations
        ADTSynthesis.QueryStructure.Specification.SearchTerms.ListInclusion
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        ADTSynthesis.QueryStructure.Automation.IndexSelection.

(* Instances for building indexes with make simple indexes. *)
(* Every Kind of index is keyed on an inductive type with a single constructor*)
Local Open Scope string_scope.
Definition InclusionIndex : string := "InclusionIndex".

(* This is our search term type. *)
Record InvertedSearchTerm
       (heading : Heading)
  :=
    { IndexSearchTerm : list string;
      ItemSearchTerm : @Tuple heading -> bool }.

(* This builds the type of searchterms and the matching function on them *)
Global Instance InvertedIndexDenotation
       (heading : Heading)
       (index : @Attributes heading)
       (projection : @Tuple heading -> list string)
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
             (fun tup => GetAttribute tup index ))
end
: typeclass_instances.

Ltac matchInclusionIndex WhereClause k :=
  match WhereClause with
    | fun tups => IncludedIn _ (@?C1 tups) =>
      let attrs1 := TermAttributes C1 in
      k (map (fun a12 => (InclusionIndex, (fst a12, snd a12)))
             (attrs1))
  end.

Ltac InclusionIndexUse SC F indexed_attrs f k :=
     match type of f with
       (* Inclusion Search Terms *)
       | forall a, {IncludedIn ?X (_!?fd)} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "InclusionIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
            k ({| KindNameKind := "InclusionIndex";
                  KindNameName := fd|}, X) (fun _ : @Tuple SC => true)
        | forall a, {IncludedIn ?X (_``?fd)} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "InclusionIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
            k ({| KindNameKind := "InclusionIndex";
                  KindNameName := fd|}, X) (fun _ : @Tuple SC => true)
     end.

Ltac InclusionIndexUse_dep SC F indexed_attrs visited_attrs f T k :=
  match type of f with
    | forall a b, {IncludedIn (@?X a) (_!?fd)} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "InclusionIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
          match eval simpl in
                (in_dec string_dec fd visited_attrs) with
            | right _ => k (fd :: visited_attrs)
                           ({| KindNameKind := "InclusionIndex";
                               KindNameName := fd |}, X)
                           (fun (a : T) (_ : @Tuple SC) => true)
            | left _ => k visited_attrs tt F
          end
        | forall a b, {IncludedIn (@?X a) (_``?fd)} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "InclusionIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto);
            match eval simpl in
                  (in_dec string_dec fd visited_attrs) with
              | right _ => k (fd :: visited_attrs)
                             ({| KindNameKind := "InclusionIndex";
                                 KindNameName := fd |}, X)
                             (fun (a : T) (_ : @Tuple SC) => true)
              | left _ => k visited_attrs tt F
            end
  end.

Ltac createLastInclusionTerm f fds tail fs kind s k :=
  match kind with
    | "InclusionIndex" =>
      (findMatchingTerm
         fds kind s
         ltac:(fun X => k {| IndexSearchTerm := X;
                             ItemSearchTerm := tail |}))
        || k {| IndexSearchTerm := nil;
                ItemSearchTerm := tail |}
  end.

Ltac createLastInclusionTerm_dep dom f fds tail fs kind rest s k :=
  match kind with
    | "InclusionIndex" =>
      (findMatchingTerm
         fds kind s
         ltac:(fun X => k (fun x : dom => {| IndexSearchTerm := X x;
                                             ItemSearchTerm := tail x |}))
                || k (fun x : dom => {| IndexSearchTerm := nil;
                                        ItemSearchTerm := tail x |}))
  end.

Ltac createEarlyInclusionTerm f fds tail fs kind EarlyIndex LastIndex rest s k :=
  match kind with
    | "InclusionIndex" =>
      (findMatchingTerm
         fds kind s
         ltac:(fun X => k (X, rest)))
        || k (@nil string, rest)
  end.
