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
       (heading : Heading)
  :=
    { RangeIndexSearchTerm : ((option nat) * (option nat));
      RangeItemSearchTerm : @Tuple heading -> bool }.

(* This builds the type of searchterms and the matching function on them *)
Global Instance RangeIndexDenotation
       (heading : Heading)
       (index : @Attributes heading)
       (projection : @Tuple heading -> nat)
: @IndexDenotation "RangeIndex" heading index :=
  {| DenoteIndex := RangeSearchTerm heading; (* Pick search term type *)
     MatchIndex search_term item := (* matching function : DenoteIndex -> Tuple heading -> bool *)
       if InRange_dec (projection item) (RangeIndexSearchTerm search_term) then
         RangeItemSearchTerm search_term item
       else
         false |}.

Instance InRangeBothDec {A} {f : A -> nat} (min max : nat) :
  DecideableEnsemble (fun a => min <= f a <= max) :=
  DecideableEnsemble_InRange_f f (Some min, Some max).

(* TODO: All tactics below this need to be updated to the new definition on RangeSearchTerm *)

(* Extra type class magic for range indices. *)
Hint Extern 10 (@IndexDenotation "RangeIndex" ?heading ?index) =>
let index_domain := eval hnf in (@Domain heading index) in
match index_domain with
  | nat =>
    apply (@RangeIndexDenotation
             heading index
             (fun tup => GetAttribute tup index ))
end
: typeclass_instances.

Ltac matchRangeIndex WhereClause k k_fail :=
  match WhereClause with
    | fun tups => InRange (@?C1 tups) _ =>
      let attrs1 := TermAttributes C1 in
      k (map (fun a12 => (RangeIndex, (fst a12, snd a12)))
             (attrs1))
    | _ => k_fail WhereClause k
  end.

Ltac RangeIndexUse SC F indexed_attrs f k k_fail :=
match type of f with
        (* Range Search Terms *)
  | forall a, {InRange (GetAttribute _ ?fd') ?X} + {_} =>
    let H := fresh in
    let fd := eval simpl in (bindex fd') in
    assert (List.In {| KindNameKind := "RangeIndex";
                       KindNameName := fd|} indexed_attrs) as H
        by (clear; simpl; intuition eauto); clear H;
    k ({| KindNameKind := "RangeIndex";
          KindNameName := bindex fd|}, X) (fun _ : @Tuple SC => true)
  | _ => k_fail SC F indexed_attrs f k
end.

Ltac RangeIndexUse_dep SC F indexed_attrs visited_attrs f T k k_fail :=
    match type of f with
      (* Range Search Terms *)
      | forall a b, {InRange (GetAttribute _ ?fd') (@?X a)} + {_} =>
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
                         (fun (a : T) (_ : @Tuple SC) => true)
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
            || k {| RangeIndexSearchTerm := (@None nat, @None nat);
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
                    || k (fun x : dom => {| RangeIndexSearchTerm := (@None nat, @None nat);
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
            || k ((@None nat, @None nat), rest)
        | _ => k_fail f fds tail fs kind EarlyIndex LastIndex rest s k
      end.

Ltac createEarlyRangeTerm_dep dom f fds tail fs kind EarlyIndex LastIndex rest s k k_fail :=
  let is_equality := eval compute in (string_dec kind "RangeIndex") in
      match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k (fun x : dom => (Some (X x), rest x))))
            || k (fun x : dom => ((@None nat, @None nat), rest x))
        | _ => k_fail f fds tail fs kind EarlyIndex LastIndex rest s k
      end.

Ltac RangeIndexTactics f :=
  PackageIndexTactics
    matchRangeIndex
    RangeIndexUse createEarlyRangeTerm createLastRangeTerm
    RangeIndexUse_dep createEarlyRangeTerm_dep createLastRangeTerm_dep f.
