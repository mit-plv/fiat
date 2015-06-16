Require Import
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Specification.SearchTerms.InRange
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Automation.Common.

(* Instances for building indexes with make simple indexes. *)
(* Every Kind of index is keyed on an inductive type with a single constructor*)
Definition RangeIndex : string := "RangeIndex".

(* This is our search term type. *)
Record RangeSearchTerm
       (heading : RawHeading)
  :=
    { RangeIndexSearchTerm : option (nat * nat);
      RangeItemSearchTerm : @RawTuple heading -> bool }.

(* This builds the type of searchterms and the matching function on them *)
Global Instance RangeIndexDenotation
       (heading : RawHeading)
       (index : @Attributes heading)
       (projection : @RawTuple heading -> nat)
: @IndexDenotation "RangeIndex" heading index :=
  {| DenoteIndex := RangeSearchTerm heading; (* Pick search term type *)
     MatchIndex search_term item := (* matching function : DenoteIndex -> RawTuple heading -> bool *)
       match RangeIndexSearchTerm search_term with
         | Some indexSearchTerm =>
           if InRange_dec (projection item) indexSearchTerm then
             RangeItemSearchTerm search_term item
           else false
         | None =>
           RangeItemSearchTerm search_term item
       end |}.

(* Extra type class magic for range indices. *)
Hint Extern 10 (@IndexDenotation "RangeIndex" ?heading ?index) =>
let index_domain := eval hnf in (@Domain heading index) in
match index_domain with
  | nat =>
    apply (@RangeIndexDenotation
             heading index
             (fun tup => GetAttributeRaw tup index ))
end
: typeclass_instances.

Ltac matchRangeIndex qsSchema WhereClause k k_fail :=
  match WhereClause with
  | fun tups => InRange (@?C1 tups) _ =>
    TermAttributes C1 ltac:(fun Ridx attr =>
                              k (@InsertOccurence _ qsSchema Ridx (RangeIndex, attr) (InitOccurence _)))
  | _ => k_fail qsSchema WhereClause k
  end.

Ltac RangeIndexUse SC F indexed_attrs f k k_fail :=
match type of f with
        (* Range Search Terms *)
  | forall a, {InRange (GetAttributeRaw _ ?fd') ?X} + {_} =>
    let H := fresh in
    let fd := eval simpl in (bindex fd') in
    assert (List.In {| KindNameKind := "RangeIndex";
                       KindNameName := fd|} indexed_attrs) as H
        by (clear; simpl; intuition eauto); clear H;
    k ({| KindNameKind := "RangeIndex";
          KindNameName := bindex fd|}, X) (fun _ : @RawTuple SC => true)
  | _ => k_fail SC F indexed_attrs f k
end.

Ltac RangeIndexUse_dep SC F indexed_attrs visited_attrs f T k k_fail :=
    match type of f with
      (* Range Search Terms *)
      | forall a b, {InRange (GetAttributeRaw _ ?fd') (@?X a)} + {_} =>
        let H := fresh in
        let fd := eval simpl in (bindex fd') in
        assert (List.In {| KindNameKind := "RangeIndex";
                           KindNameName := fd|} indexed_attrs) as H
            by (clear; simpl; intuition eauto); clear H;
        match eval simpl in
              (in_dec string_dec fd visited_attrs) with
          | right _ => k (fd :: visited_attrs)
                         ({| KindNameKind := "RangeIndex";
                             KindNameName := fd |}, X)
                         (fun (a : T) (_ : @RawTuple SC) => true)
          | left _ => k visited_attrs tt F
        end
      | _ => k_fail SC F indexed_attrs visited_attrs f T k
    end.

Ltac createLastRangeTerm f fds tail fs kind s k k_fail :=
  let is_equality := eval compute in (string_dec kind "RangeIndex") in
      match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k {| RangeIndexSearchTerm := Some X;
                                 RangeItemSearchTerm := tail |}))
            || k {| RangeIndexSearchTerm := @None (nat * nat);
                    RangeItemSearchTerm := tail |}
        | _ => k_fail f fds tail fs kind s k
      end.

Ltac createLastRangeTerm_dep dom f fds tail fs kind s k k_fail :=
  let is_equality := eval compute in (string_dec kind "RangeIndex") in
      match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k (fun x : dom => {| RangeIndexSearchTerm := Some (X x);
                                                 RangeItemSearchTerm := tail x |}))
                    || k (fun x : dom => {| RangeIndexSearchTerm := @None (nat * nat);
                                            RangeItemSearchTerm := tail x |}))
        | _ => k_fail dom f fds tail fs kind s k
      end.

Ltac createEarlyRangeTerm f fds tail fs kind EarlyIndex LastIndex rest s k k_fail :=
  let is_equality := eval compute in (string_dec kind "RangeIndex") in
      match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k (Some X, rest)))
            || k (@None (nat * nat), rest)
        | _ => k_fail f fds tail fs kind EarlyIndex LastIndex rest s k
      end.

Ltac createEarlyRangeTerm_dep dom f fds tail fs kind EarlyIndex LastIndex rest s k k_fail :=
  let is_equality := eval compute in (string_dec kind "RangeIndex") in
      match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k (fun x : dom => (Some (X x), rest x))))
            || k (fun x : dom => (@None (nat * nat), rest x))
        | _ => k_fail f fds tail fs kind EarlyIndex LastIndex rest s k
      end.

Ltac RangeIndexTactics f :=
  PackageIndexTactics
    matchRangeIndex
    RangeIndexUse createEarlyRangeTerm createLastRangeTerm
    RangeIndexUse_dep createEarlyRangeTerm_dep createLastRangeTerm_dep f.
