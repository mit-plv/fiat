Require Import
        Coq.Bool.Bool
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Automation.Common
        Fiat.QueryStructure.Implementation.DataStructures.Bags.CountingListBags
        Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsOfTuples.

(* Instances for building indexes with make simple indexes. *)
(* Every Kind of index is keyed on an inductive type with a single constructor*)
Definition FindStringPrefixIndex : string := "FindStringPrefixIndex".

Instance DecideablePrefix_f {A} {f s}: DecideableEnsemble (fun s' : A => is_true (prefix s (f s'))) :=
  {dec s' := ?[bool_dec (prefix s (f s')) true]}.
intros; find_if_inside; intuition.
Defined.

Instance DecideablePrefix_sym_f {A} {f s}: DecideableEnsemble (fun s' : A => is_true (prefix (f s') s)) :=
  {dec s' := ?[bool_dec (prefix (f s') s) true]}.
intros; find_if_inside; intuition.
Defined.

Ltac BuildLastFindStringPrefixIndex
     heading indices kind index k k_fail :=
  let is_equality := eval compute in (string_dec kind FindStringPrefixIndex) in
      match is_equality with
      | left _ => k
                    (fun (search_term : prod (option (Domain heading index)) (@RawTuple heading -> bool))
                         (tup : @RawTuple heading)=>
                       andb match fst search_term with
                            | Some indexSearchTerm =>
                              prefix (GetAttributeRaw tup index) indexSearchTerm
                            | None => true
                            end (snd search_term tup))
      | right _ => k_fail heading indices kind index k
      end.

Ltac BuildEarlyFindStringPrefixIndex
     heading indices kind index matcher k k_fail :=
  let is_equality := eval compute in (string_dec kind FindStringPrefixIndex) in
      match is_equality with
      | left _ => k
                    (fun (search_term : prod (option (Domain heading index)) _)
                         (tup : @RawTuple heading)=>
                       andb match fst search_term with
                            | Some indexSearchTerm =>
                              prefix (GetAttributeRaw tup index) indexSearchTerm
                            | None => true
                            end (matcher (snd search_term) tup))
      | right _ => k_fail heading indices kind index matcher k
      end.


Instance ExpressionAttributeCounterIsStringPrefixL
         {qsSchema : RawQueryStructureSchema}
         {a a' : string}
         (RidxL : Fin.t _)
         (BAidxL : @Attributes (Vector.nth _ RidxL))
         (ExpCountL : @TermAttributeCounter _ qsSchema a RidxL BAidxL)
  : @ExpressionAttributeCounter _ qsSchema (is_true (prefix a a'))
                                (@InsertOccurenceOfAny _ _ RidxL ("FindStringPrefixIndex", BAidxL)
                                                       (InitOccurences _)) | 0 := { }.

Ltac IsStringPrefixExpressionAttributeCounter k :=
  psearch_combine
    ltac:(eapply @ExpressionAttributeCounterIsStringPrefixL; intros) k.

Ltac StringPrefixIndexUse SC F indexed_attrs f k k_fail :=
  match type of f with
  (* FindPrefix Search Terms *)
  | forall a, {prefix (GetAttributeRaw _ ?fd) ?X = true} + {_} =>
    let H := fresh in
    assert (List.In (@Build_KindIndex SC FindStringPrefixIndex fd) indexed_attrs) as H
        by (clear; simpl; intuition eauto); clear H;
    k ((@Build_KindIndex SC FindStringPrefixIndex fd), X) (fun _ : @RawTuple SC => true)
  | _ => k_fail SC F indexed_attrs f k
  end.

(* FindPrefix Search Terms *)
Ltac StringPrefixIndexUse_dep SC F indexed_attrs visited_attrs f T k k_fail :=
  match type of f with
  | forall a b, {prefix (GetAttributeRaw _ ?fd) (@?X a) = true} + {_} =>
    let H := fresh in
    assert (List.In (@Build_KindIndex SC FindStringPrefixIndex fd) indexed_attrs) as H
        by (clear; simpl; intuition eauto); clear H;
    match eval simpl in
          (in_dec fin_eq_dec fd visited_attrs) with
    | right _ => k (fd :: visited_attrs)
                   ((@Build_KindIndex SC FindStringPrefixIndex fd), X)
                   (fun (a : T) (_ : @RawTuple SC) => true)
    | left _ => k visited_attrs tt F
    end
  | _ => k_fail SC F indexed_attrs visited_attrs f T k
  end.

Ltac createLastStringPrefixTerm f fds tail fs kind s k k_fail :=
  let is_equality := eval compute in (string_dec kind "FindStringPrefixIndex") in
      match is_equality with
      | left _ =>
        (findMatchingTerm
           fds kind s
           ltac:(fun X => k (Some X, tail)))
          || k (@None (Domain f s), tail)
      | _ => k_fail f fds tail fs kind s k
      end.

Ltac createLastStringPrefixTerm_dep dom f fds tail fs kind s k k_fail :=
  let is_equality := eval compute in (string_dec kind "FindStringPrefixIndex") in
      match is_equality with
      | left _ =>
        (findMatchingTerm
           fds kind s
           ltac:(fun X => k (fun x : dom => (Some (X x), tail x)))
                  || k (fun x : dom => (fun x : dom => (@None (Domain f s ), tail x))))
      | _ => k_fail dom f fds tail fs kind s k
      end.

Ltac createEarlyStringPrefixTerm f fds tail fs kind EarlyIndex LastIndex rest s k k_fail :=
  let is_equality := eval compute in (string_dec kind "FindStringPrefixIndex") in
      match is_equality with
      | left _ =>
        (findMatchingTerm
           fds kind s
           ltac:(fun X => k (Some X, rest)))
          || k (@None (Domain f s), rest)
      | _ => k_fail f fds tail fs kind EarlyIndex LastIndex rest s k
      end.

Ltac createEarlyStringPrefixTerm_dep dom f fds tail fs kind EarlyIndex LastIndex rest s k k_fail :=
  let is_equality := eval compute in (string_dec kind "FindStringPrefixIndex") in
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
  let is_equality := eval compute in (string_dec AttrKind "FindStringPrefixIndex") in
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
  let is_equality := eval compute in (string_dec AttrKind "FindStringPrefixIndex") in
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

Ltac StringPrefixIndexTactics f :=
  PackageIndexTactics
    IsStringPrefixExpressionAttributeCounter
    BuildEarlyFindStringPrefixIndex BuildLastFindStringPrefixIndex
    StringPrefixIndexUse createEarlyStringPrefixTerm createLastStringPrefixTerm
    StringPrefixIndexUse_dep createEarlyStringPrefixTerm_dep createLastStringPrefixTerm_dep
    BuildEarlyTrieBag BuildLastTrieBag f.
