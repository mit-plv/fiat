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
    { RangeIndexSearchTerm : (option nat) * (option nat);
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
         | (Some minRange, Some maxRange) =>
           if InRange_dec (projection item) minRange maxRange then
             RangeItemSearchTerm search_term item
           else false
         | (None, Some maxRange) =>
           if le_dec (projection item) maxRange then
             RangeItemSearchTerm search_term item
           else false
         | (Some minRange, None) =>
           if le_dec minRange (projection item) then
             RangeItemSearchTerm search_term item
           else false
         | (_, _) => RangeItemSearchTerm search_term item
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
  | fun tups => (@?C2 tups) <= (@?C1 tups) <= _ =>
    TermAttributes C1 ltac:(fun Ridx1 attr1 =>
                              TermAttributes C2
                              ltac:(fun Ridx2 attr2 =>
                                      k (@InsertOccurence _ qsSchema Ridx1 (RangeIndex, attr1) (@InsertOccurence _ qsSchema Ridx2 (RangeIndex, attr2) (InitOccurence _)))))

  | fun tups => _ <= (@?C1 tups) <= (@?C2 tups) =>
    TermAttributes C1 ltac:(fun Ridx1 attr1 =>
                              TermAttributes C2
                              ltac:(fun Ridx2 attr2 =>
                                      k (@InsertOccurence _ qsSchema Ridx1 (RangeIndex, attr1) (@InsertOccurence _ qsSchema Ridx2 (RangeIndex, attr2) (InitOccurence _)))))

  | fun tups => (@?C1 tups) <= (@?C2 tups) =>
    TermAttributes C1 ltac:(fun Ridx1 attr1 =>
                              TermAttributes C2
                                             ltac:(fun Ridx2 attr2 =>
                                      k (@InsertOccurence _ qsSchema Ridx1 (RangeIndex, attr1) (@InsertOccurence _ qsSchema Ridx2 (RangeIndex, attr2) (InitOccurence _)))))

  | fun tups => _ <= (@?C1 tups) =>
    TermAttributes C1 ltac:(fun Ridx attr =>
                              k (@InsertOccurence _ qsSchema Ridx (RangeIndex, attr) (InitOccurence _)))
  | fun tups => (@?C1 tups) <= _ =>
    TermAttributes C1 ltac:(fun Ridx attr =>
                              k (@InsertOccurence _ qsSchema Ridx (RangeIndex, attr) (InitOccurence _)))
  | _ => k_fail qsSchema WhereClause k
  end.

Ltac RangeIndexUse SC F indexed_attrs f k k_fail :=
match type of f with
        (* Range Search Terms *)
  | forall a, {?X <= GetAttributeRaw _ ?fd <= ?Y} + {_} =>
    let H := fresh in
    assert (List.In (@Build_KindIndex SC "RangeIndex" fd) indexed_attrs) as H
        by (clear; simpl; intuition eauto); clear H;
    k ((@Build_KindIndex SC "RangeIndex" fd), (Some X, Some Y)) (fun _ : @RawTuple SC => true)

  | forall a, { GetAttributeRaw _ ?fd <= ?X} + {_} =>
    let H := fresh in
    assert (List.In (@Build_KindIndex SC "RangeIndex" fd) indexed_attrs) as H
        by (clear; simpl; intuition eauto); clear H;
    k ((@Build_KindIndex SC "RangeIndex" fd), (@None nat, Some X)) (fun _ : @RawTuple SC => true)
  | forall a, {?X <= GetAttributeRaw _ ?fd} + {_} =>
    let H := fresh in
    assert (List.In (@Build_KindIndex SC "RangeIndex" fd) indexed_attrs) as H
        by (clear; simpl; intuition eauto); clear H;
    k ((@Build_KindIndex SC "RangeIndex" fd), (Some X, @None nat)) (fun _ : @RawTuple SC => true)

  | _ => k_fail SC F indexed_attrs f k
end.

Ltac RangeIndexUse_dep SC F indexed_attrs visited_attrs f T k k_fail :=
    match type of f with
    (* Range Search Terms *)
    | forall (a : ?Dom) b, { @?X a <= GetAttributeRaw _ ?fd <= @?Y a} + {_} =>
      let H := fresh in
          assert (List.In (@Build_KindIndex SC "RangeIndex" fd) indexed_attrs) as H
          by (clear; simpl; intuition eauto); clear H;
                              match eval simpl in
                                    (in_dec fin_eq_dec fd visited_attrs) with
                              | right _ => k (fd :: visited_attrs)
                                             ((@Build_KindIndex SC "RangeIndex" fd), fun a : Dom => (Some (X a), Some (Y a)))
                                             (fun (a : T) (_ : @RawTuple SC) => true)
                              | left _ => k visited_attrs tt F
                              end

    | forall (a : ?Dom) b, { @?X a <= GetAttributeRaw _ ?fd} + {_} =>
        let H := fresh in
        assert (List.In (@Build_KindIndex SC "RangeIndex" fd) indexed_attrs) as H
            by (clear; simpl; intuition eauto); clear H;
        match eval simpl in
              (in_dec fin_eq_dec fd visited_attrs) with
          | right _ => k (fd :: visited_attrs)
                         ((@Build_KindIndex SC "RangeIndex" fd), fun a : Dom => (Some (X a), @None nat))
                         (fun (a : T) (_ : @RawTuple SC) => true)
          | left _ => k visited_attrs tt F
        end

      | forall (a : ?Dom) b, {GetAttributeRaw _ ?fd <= (@?X a)} + {_} =>
        let H := fresh in
        assert (List.In (@Build_KindIndex SC "RangeIndex" fd) indexed_attrs) as H
            by (clear; simpl; intuition eauto); clear H;
        match eval simpl in
              (in_dec fin_eq_dec fd visited_attrs) with
          | right _ => k (fd :: visited_attrs)
                         ((@Build_KindIndex SC "RangeIndex" fd), fun a : Dom => (@None nat, Some (X a)))
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
             ltac:(fun X => k {| RangeIndexSearchTerm := X;
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
             ltac:(fun X => k (fun x : dom => {| RangeIndexSearchTerm := X x;
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
             ltac:(fun X => k (X, rest)))
            || k ((@None nat, @None nat), rest)
        | _ => k_fail f fds tail fs kind EarlyIndex LastIndex rest s k
      end.

Ltac createEarlyRangeTerm_dep dom f fds tail fs kind EarlyIndex LastIndex rest s k k_fail :=
  let is_equality := eval compute in (string_dec kind "RangeIndex") in
      match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k (fun x : dom => (X x, rest x))))
            || k (fun x : dom => ((@None nat, @None nat), rest x))
        | _ => k_fail dom f fds tail fs kind EarlyIndex LastIndex rest s k
      end.

Ltac RangeIndexTactics f :=
  PackageIndexTactics
    matchRangeIndex
    RangeIndexUse createEarlyRangeTerm createLastRangeTerm
    RangeIndexUse_dep createEarlyRangeTerm_dep createLastRangeTerm_dep f.
