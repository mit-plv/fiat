Require Import
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Automation.Common
        Fiat.QueryStructure.Implementation.DataStructures.Bags.CountingListBags
        Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsOfTuples.

(* Instances for building indexes with make simple indexes. *)
(* Every Kind of index is keyed on an inductive type with a single constructor*)
Definition FindPrefixIndex : string := "FindPrefixIndex".

Ltac BuildLastFindPrefixIndex
     heading indices kind index k k_fail :=
  let is_equality := eval compute in (string_dec kind FindPrefixIndex) in
      match is_equality with
      | left _ => k
                    (fun (search_term : prod (option (Domain heading index)) (@RawTuple heading -> bool))
                         (tup : @RawTuple heading)=>
                       andb match fst search_term with
                            | Some indexSearchTerm =>
                              if IsPrefix_dec (GetAttributeRaw tup index) indexSearchTerm then
                                true
                              else false
                            | None => true
                            end (snd search_term tup))
      | right _ => k_fail heading indices kind index k
      end.

Ltac BuildEarlyFindPrefixIndex
     heading indices kind index matcher k k_fail :=
  let is_equality := eval compute in (string_dec kind FindPrefixIndex) in
      match is_equality with
      | left _ => k
                    (fun (search_term : prod (option (Domain heading index)) _)
                         (tup : @RawTuple heading)=>
                       andb match fst search_term with
                            | Some indexSearchTerm =>
                              if IsPrefix_dec (GetAttributeRaw tup index) indexSearchTerm then
                                true
                              else false
                            | None => true
                            end (matcher (snd search_term) tup))
      | right _ => k_fail heading indices kind index matcher k
      end.


Instance ExpressionAttributeCounterIsPrefixL {A }
         {qsSchema : RawQueryStructureSchema}
         {a a' : list A}
         (RidxL : Fin.t _)
         (BAidxL : @Attributes (Vector.nth _ RidxL))
         (ExpCountL : @TermAttributeCounter _ qsSchema a RidxL BAidxL)
  : @ExpressionAttributeCounter _ qsSchema (IsPrefix a a')
                                (@InsertOccurenceOfAny _ _ RidxL ("FindPrefixIndex", BAidxL)
                                                       (InitOccurences _)) | 0 := { }.

Ltac IsPrefixExpressionAttributeCounter k :=
  psearch_combine
    ltac:(eapply @ExpressionAttributeCounterIsPrefixL; intros) k.

Ltac PrefixIndexUse SC F indexed_attrs f k k_fail :=
  match type of f with
  (* FindPrefix Search Terms *)
  | forall a, {IsPrefix (GetAttributeRaw _ ?fd) ?X} + {_} =>
    let H := fresh in
    assert (List.In (@Build_KindIndex SC FindPrefixIndex fd) indexed_attrs) as H
        by (clear; simpl; intuition eauto); clear H;
    k ((@Build_KindIndex SC FindPrefixIndex fd), X) (fun _ : @RawTuple SC => true)
  | _ => k_fail SC F indexed_attrs f k
  end.

(* FindPrefix Search Terms *)
Ltac PrefixIndexUse_dep SC F indexed_attrs visited_attrs f T k k_fail :=
  match type of f with
  | forall a b, {IsPrefix (GetAttributeRaw _ ?fd) (@?X a)} + {_} =>
    let H := fresh in
    assert (List.In (@Build_KindIndex SC FindPrefixIndex fd) indexed_attrs) as H
        by (clear; simpl; intuition eauto); clear H;
    match eval simpl in
          (in_dec fin_eq_dec fd visited_attrs) with
    | right _ => k (fd :: visited_attrs)
                   ((@Build_KindIndex SC FindPrefixIndex fd), X)
                   (fun (a : T) (_ : @RawTuple SC) => true)
    | left _ => k visited_attrs tt F
    end
  | _ => k_fail SC F indexed_attrs visited_attrs f T k
  end.

Ltac createLastPrefixTerm f fds tail fs kind s k k_fail :=
  let is_equality := eval compute in (string_dec kind "FindPrefixIndex") in
      match is_equality with
      | left _ =>
        (findMatchingTerm
           fds kind s
           ltac:(fun X => k (Some X, tail)))
          || k (@None (Domain f s), tail)
      | _ => k_fail f fds tail fs kind s k
      end.

Ltac createLastPrefixTerm_dep dom f fds tail fs kind s k k_fail :=
  let is_equality := eval compute in (string_dec kind "FindPrefixIndex") in
      match is_equality with
      | left _ =>
        (findMatchingTerm
           fds kind s
           ltac:(fun X => k (fun x : dom => (Some (X x), tail x)))
                  || k (fun x : dom => (fun x : dom => (@None (Domain f s ), tail x))))
      | _ => k_fail dom f fds tail fs kind s k
      end.

Ltac createEarlyPrefixTerm f fds tail fs kind EarlyIndex LastIndex rest s k k_fail :=
  let is_equality := eval compute in (string_dec kind "FindPrefixIndex") in
      match is_equality with
      | left _ =>
        (findMatchingTerm
           fds kind s
           ltac:(fun X => k (Some X, rest)))
          || k (@None (Domain f s), rest)
      | _ => k_fail f fds tail fs kind EarlyIndex LastIndex rest s k
      end.

Ltac createEarlyPrefixTerm_dep dom f fds tail fs kind EarlyIndex LastIndex rest s k k_fail :=
  let is_equality := eval compute in (string_dec kind "FindPrefixIndex") in
      match is_equality with
      | left _ =>
        (findMatchingTerm
           fds kind s
           ltac:(fun X => k (fun x : dom => (Some (X x), rest x))))
          || k (fun x : dom => (@None (Domain f s), rest x))
      | _ => k_fail dom f fds tail fs kind EarlyIndex LastIndex rest s k
      end.

Require Import
        Coq.FSets.FMapInterface
        Coq.FSets.FMapFacts
        Coq.FSets.FMapAVL
        Coq.Structures.OrderedTypeEx
        Fiat.Common.String_as_OT
        Fiat.QueryStructure.Implementation.DataStructures.Bags.TrieBags.

Module NatTrieBag := TrieBag Nat_as_OT.
Module ZTrieBag := TrieBag Z_as_OT.
Module NTrieBag := TrieBag N_as_OT.
Module StringTrieBag := TrieBag String_as_OT.

Ltac BuildLastTrieBag heading AttrList AttrKind AttrIndex k k_fail :=
  let is_equality := eval compute in (string_dec AttrKind "FindPrefixIndex") in
      match is_equality with
      | left _ =>
        let AttrType := eval compute in (Domain heading AttrIndex) in
            match AttrType with
            | list nat =>
              k (@NatTrieBag.TrieBagAsCorrectBag _ _ _ _ _ _ _
                                                 (@CountingListAsCorrectBag
                                                    (@RawTuple heading)
                                                    (IndexedTreeUpdateTermType heading)
                                                    (IndexedTreebupdate_transform heading))
                                                 (fun x => GetAttributeRaw (heading := heading) x AttrIndex))
            | list N =>
              k (@NTrieBag.TrieBagAsCorrectBag _ _ _ _ _ _ _
                                                 (@CountingListAsCorrectBag
                                                    (@RawTuple heading)
                                                    (IndexedTreeUpdateTermType heading)
                                                    (IndexedTreebupdate_transform heading))
                                                 (fun x => GetAttributeRaw (heading := heading) x AttrIndex))

            | list Z =>
              k (@ZTrieBag.TrieBagAsCorrectBag _ _ _ _ _ _ _
                                                 (@CountingListAsCorrectBag
                                                    (@RawTuple heading)
                                                    (IndexedTreeUpdateTermType heading)
                                                    (IndexedTreebupdate_transform heading))
                                                 (fun x => GetAttributeRaw (heading := heading) x AttrIndex))
            | list string =>
              k (@StringTrieBag.TrieBagAsCorrectBag _ _ _ _ _ _ _
                                                 (@CountingListAsCorrectBag
                                                    (@RawTuple heading)
                                                    (IndexedTreeUpdateTermType heading)
                                                    (IndexedTreebupdate_transform heading))
                                                 (fun x => GetAttributeRaw (heading := heading) x AttrIndex))
            end
      | right _ => k_fail heading AttrList AttrKind AttrIndex k
      end.

Ltac BuildEarlyTrieBag heading AttrList AttrKind AttrIndex subtree k k_fail :=
  let is_equality := eval compute in (string_dec AttrKind "FindPrefixIndex") in
      match is_equality with
      | left _ =>
        let AttrType := eval compute in (Domain heading AttrIndex) in
            match AttrType with
            | list nat =>
              k (@NatTrieBag.TrieBagAsCorrectBag _ _ _ _ _ _ _
                                                 subtree
                                                 (fun x => GetAttributeRaw (heading := heading) x AttrIndex))

            | list N =>
              k (@NTrieBag.TrieBagAsCorrectBag _ _ _ _ _ _ _
                                                 subtree
                                                 (fun x => GetAttributeRaw (heading := heading) x AttrIndex))

            | list Z =>
              k (@ZTrieBag.TrieBagAsCorrectBag _ _ _ _ _ _ _
                                                 subtree
                                                 (fun x => GetAttributeRaw (heading := heading) x AttrIndex))

            | list string =>
              k (@StringTrieBag.TrieBagAsCorrectBag _ _ _ _ _ _ _
                                                 subtree
                                                 (fun x => GetAttributeRaw (heading := heading) x AttrIndex))
            end
      | right _ => k_fail heading AttrList AttrKind AttrIndex subtree k
      end.

Ltac PrefixIndexTactics f :=
  PackageIndexTactics
    IsPrefixExpressionAttributeCounter
    BuildEarlyFindPrefixIndex BuildLastFindPrefixIndex
    PrefixIndexUse createEarlyPrefixTerm createLastPrefixTerm
    PrefixIndexUse_dep createEarlyPrefixTerm_dep createLastPrefixTerm_dep
    BuildEarlyTrieBag BuildLastTrieBag f.
