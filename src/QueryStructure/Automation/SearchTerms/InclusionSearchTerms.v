Require Import
        Coq.Strings.String
        Fiat.Common.String_as_OT
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Specification.SearchTerms.ListInclusion
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Automation.Common
        Fiat.QueryStructure.Implementation.DataStructures.Bags.CountingListBags
        Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsOfTuples.

(* Instances for building indexes with make simple indexes. *)
(* Every Kind of index is keyed on an inductive type with a single constructor*)
Local Open Scope string_scope.
Definition InclusionIndex : string := "InclusionIndex".

Instance ExpressionAttributeCounterIncludedIn {A }
         {qsSchema : RawQueryStructureSchema}
         {a}
         {a' : list A}
         (RidxL : Fin.t _)
         (BAidxL : @Attributes (Vector.nth _ RidxL))
         (ExpCountL : @TermAttributeCounter _ qsSchema a' RidxL BAidxL)
  : @ExpressionAttributeCounter _ qsSchema (IncludedIn a a')
                                (@InsertOccurenceOfAny _ _ RidxL (InclusionIndex, BAidxL)
                                                       (InitOccurences _)) | 0 := { }.

Ltac IncludedInExpressionAttributeCounter k :=
  psearch_combine
    ltac:(eapply @ExpressionAttributeCounterIncludedIn; intros) k.

Ltac BuildLastInclusionIndex
     heading indices kind index k k_fail :=
  let is_equality := eval compute in (string_dec kind InclusionIndex) in
      let A := eval compute in (Domain heading index) in
          let A' := match A with | list ?A' => A' end in
          match is_equality with
          | left _ => k
                        (fun (search_term : prod (Domain heading index) (@RawTuple heading -> bool)) (tup : @RawTuple heading) =>
                           andb (if IncludedIn_dec (X := A')
                                                   (fst search_term) (GetAttributeRaw tup index) then
                                   true
                                 else false)
                                (snd search_term tup))
          | right _ => k_fail heading indices kind index k
          end.

Ltac BuildEarlyInclusionIndex
     heading indices kind index matcher k k_fail :=
  k_fail heading indices kind index matcher k.

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
           ltac:(fun X => k (X : (Domain f s), tail)))
          || k (nil : (Domain f s), tail)
      | _ => k_fail f fds tail fs kind s k
      end.

Ltac createLastInclusionTerm_dep dom f fds tail fs kind s k k_fail :=
  let is_equality := eval compute in (string_dec kind "InclusionIndex") in
      match is_equality with
      | left _ =>
        (findMatchingTerm
           fds kind s
           ltac:(fun X => k (fun x : dom => (X x : (Domain f s), tail x )))
                  || k (fun x : dom => (nil : (Domain f s), tail x)))
      | _ => k_fail dom f fds tail fs kind s k
      end.

Ltac createEarlyInclusionTerm f fds tail fs kind EarlyIndex LastIndex rest s k k_fail :=
  let is_equality := eval compute in (string_dec kind "InclusionIndex") in
      match is_equality with
      | left _ =>
        (findMatchingTerm
           fds kind s
           ltac:(fun X => k (X, rest)))
          || k (nil : (Domain f s), rest)
      | _ => k_fail f fds tail fs kind EarlyIndex LastIndex rest s k
      end.

Ltac createEarlyInclusionTerm_dep dom f fds tail fs kind EarlyIndex LastIndex rest s k k_fail :=
  let is_equality := eval compute in (string_dec kind "InclusionIndex") in
      match is_equality with
      | left _ =>
        (findMatchingTerm
           fds kind s
           ltac:(fun X => k (fun x : dom => (X x, rest x))))
          || k (fun x : dom => (nil : (Domain f s), rest x))
      | _ => k_fail dom f fds tail fs kind EarlyIndex LastIndex rest s k
      end.

Require Import
        Coq.FSets.FMapInterface
        Coq.FSets.FMapFacts
        Coq.FSets.FMapAVL
        Coq.Structures.OrderedTypeEx
        Fiat.Common.String_as_OT
        Fiat.QueryStructure.Implementation.DataStructures.Bags.InvertedIndexBags.

Module StringInvertedIndexBag := InvertedIndexBag StringIndexedMap NatIndexedMap.
Module NatInvertedIndexBag := InvertedIndexBag NatIndexedMap NatIndexedMap.
Module NInvertedIndexBag := InvertedIndexBag NIndexedMap NatIndexedMap.
Module ZInvertedIndexBag := InvertedIndexBag ZIndexedMap NatIndexedMap.

    Ltac BuildLastInclusionIndexBag heading AttrList AttrKind AttrIndex k k_fail :=
      let is_equality := eval compute in (string_dec AttrKind InclusionIndex) in
          match is_equality with
          | left _ =>
            let AttrType := eval compute in (Domain heading AttrIndex) in
                match AttrType with
                | list string =>
                  k (@StringInvertedIndexBag.InvertedIndexAsCorrectBag _ _                                                       (fun x => GetAttributeRaw (heading := heading) x AttrIndex)
                                                                       (IndexedTreebupdate_transform heading)
                    )

                | list nat =>
                  k (@NatInvertedIndexBag.InvertedIndexAsCorrectBag _ _                                                       (fun x => GetAttributeRaw (heading := heading) x AttrIndex)
                                                                       (IndexedTreebupdate_transform heading)
                    )

                | list N =>
                  k (@NInvertedIndexBag.InvertedIndexAsCorrectBag _ _                                                       (fun x => GetAttributeRaw (heading := heading) x AttrIndex)
                                                                       (IndexedTreebupdate_transform heading)
                    )

                | list Z =>
                  k (@ZInvertedIndexBag.InvertedIndexAsCorrectBag _ _                                                       (fun x => GetAttributeRaw (heading := heading) x AttrIndex)
                                                                       (IndexedTreebupdate_transform heading)
                    )

                end
          | right _ => k_fail heading AttrList AttrKind AttrIndex k
          end.


    Ltac BuildEarlyInclusionIndexBag heading AttrList AttrKind AttrIndex subtree k k_fail :=
      k_fail heading AttrList AttrKind AttrIndex subtree k.

Ltac InclusionIndexTactics f :=
  PackageIndexTactics
    IncludedInExpressionAttributeCounter
    BuildEarlyInclusionIndex BuildLastInclusionIndex
    InclusionIndexUse createEarlyInclusionTerm createLastInclusionTerm
    InclusionIndexUse_dep createEarlyInclusionTerm_dep createLastInclusionTerm_dep
    BuildEarlyInclusionIndexBag BuildLastInclusionIndexBag f.
