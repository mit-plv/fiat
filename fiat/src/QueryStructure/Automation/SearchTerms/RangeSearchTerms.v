Require Import
        Coq.FSets.FMapInterface
        Coq.FSets.FMapFacts
        Coq.FSets.FMapAVL
        Coq.Structures.OrderedTypeEx
        Fiat.Common.String_as_OT
        Fiat.QueryStructure.Implementation.DataStructures.Bags.RangeTreeBags
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Specification.SearchTerms.InRange
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Automation.Common
        Fiat.QueryStructure.Implementation.DataStructures.Bags.CountingListBags
        Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsOfTuples
.

(* Instances for building indexes with make simple indexes. *)
(* Every Kind of index is keyed on an inductive type with a single constructor*)
Definition RangeIndex : string := "RangeIndex".

Instance ExpressionAttributeCounterInRangeYX
         {qsSchema : RawQueryStructureSchema}
         {y x z}
         (RidxX : Fin.t _)
         (BAidxX : @Attributes (Vector.nth _ RidxX))
         (ExpCountX : @TermAttributeCounter _ qsSchema x RidxX BAidxX)
         (RidxY : Fin.t _)
         (BAidxY : @Attributes (Vector.nth _ RidxY))
         (ExpCountY : @TermAttributeCounter _ qsSchema y RidxY BAidxY)
  : @ExpressionAttributeCounter _ qsSchema (y <= x <= z)
                                (@InsertOccurenceOfAny _ _ RidxX (RangeIndex, BAidxX)
                                                       (@InsertOccurenceOfAny _ _ RidxY (RangeIndex, BAidxY) (InitOccurences _))) | 0 := { }.

Instance ExpressionAttributeCounterInRangeX
         {qsSchema : RawQueryStructureSchema}
         {y x z}
         (RidxX : Fin.t _)
         (BAidxX : @Attributes (Vector.nth _ RidxX))
         (ExpCountX : @TermAttributeCounter _ qsSchema x RidxX BAidxX)
  : @ExpressionAttributeCounter _ qsSchema (y <= x <= z)
                                (@InsertOccurenceOfAny _ _ RidxX (RangeIndex, BAidxX)
                                                       (InitOccurences _)) | 0 := { }.

Instance ExpressionAttributeCounterInRangeXZ
         {qsSchema : RawQueryStructureSchema}
         {y x z}
         (RidxX : Fin.t _)
         (BAidxX : @Attributes (Vector.nth _ RidxX))
         (ExpCountX : @TermAttributeCounter _ qsSchema x RidxX BAidxX)
         (RidxZ : Fin.t _)
         (BAidxZ : @Attributes (Vector.nth _ RidxZ))
         (ExpCountZ : @TermAttributeCounter _ qsSchema z RidxZ BAidxZ)
  : @ExpressionAttributeCounter _ qsSchema (y <= x <= z)
                                (@InsertOccurenceOfAny _ _ RidxX (RangeIndex, BAidxX)
                                                       (@InsertOccurenceOfAny _ _ RidxZ (RangeIndex, BAidxZ) (InitOccurences _))) | 0 := { }.

Instance ExpressionAttributeCounterInRangeYX'
         {qsSchema : RawQueryStructureSchema}
         {y x}
         (RidxX : Fin.t _)
         (BAidxX : @Attributes (Vector.nth _ RidxX))
         (ExpCountX : @TermAttributeCounter _ qsSchema x RidxX BAidxX)
         (RidxY : Fin.t _)
         (BAidxY : @Attributes (Vector.nth _ RidxY))
         (ExpCountY : @TermAttributeCounter _ qsSchema y RidxY BAidxY)
  : @ExpressionAttributeCounter _ qsSchema (y <= x)
                                (@InsertOccurenceOfAny _ _ RidxX (RangeIndex, BAidxX)
                                                       (@InsertOccurenceOfAny _ _ RidxY (RangeIndex, BAidxY) (InitOccurences _))) | 0 := { }.

Instance ExpressionAttributeCounterInRangeX'
         {qsSchema : RawQueryStructureSchema}
         {y x}
         (RidxX : Fin.t _)
         (BAidxX : @Attributes (Vector.nth _ RidxX))
         (ExpCountX : @TermAttributeCounter _ qsSchema x RidxX BAidxX)
  : @ExpressionAttributeCounter _ qsSchema (y <= x)
                                (@InsertOccurenceOfAny _ _ RidxX (RangeIndex, BAidxX)
                                                       (InitOccurences _)) | 0 := { }.

Instance ExpressionAttributeCounterInRangeY
         {qsSchema : RawQueryStructureSchema}
         {y x}
         (RidxY : Fin.t _)
         (BAidxY : @Attributes (Vector.nth _ RidxY))
         (ExpCountX : @TermAttributeCounter _ qsSchema y RidxY BAidxY)
  : @ExpressionAttributeCounter _ qsSchema (y <= x)
                                (@InsertOccurenceOfAny _ _ RidxY (RangeIndex, BAidxY)
                                                       (InitOccurences _)) | 0 := { }.

Ltac InRangeExpressionAttributeCounter k :=
  psearch_combine
    ltac:(eapply @ExpressionAttributeCounterInRangeYX; intros)
  ltac:(psearch_combine
          ltac:(eapply @ExpressionAttributeCounterInRangeXZ; intros)
  ltac:(psearch_combine
          ltac:(eapply @ExpressionAttributeCounterInRangeX; intros)
  ltac:(psearch_combine
          ltac:(eapply @ExpressionAttributeCounterInRangeYX'; intros)
  ltac:(psearch_combine
          ltac:(eapply @ExpressionAttributeCounterInRangeX'; intros)
  ltac:(psearch_combine
          ltac:(eapply @ExpressionAttributeCounterInRangeY; intros)
                 k))))).

Ltac BuildLastRangeIndex
     heading indices kind index k k_fail :=
  let is_equality := eval compute in (string_dec kind RangeIndex) in
      match is_equality with
      | left _ => k
                    (fun (search_term : prod (prod (option (Domain heading index)) (option (Domain heading index))) (@RawTuple heading -> bool))
                         (tup : @RawTuple heading) =>
                       match fst search_term with
                       | (Some minRange, Some maxRange) =>
                         if InRange_dec (GetAttributeRaw tup index) minRange maxRange then
                           (snd search_term) tup
                         else false
                       | (None, Some maxRange) =>
                         if le_dec (GetAttributeRaw tup index) maxRange then
                           (snd search_term) tup
                         else false
                       | (Some minRange, None) =>
                         if le_dec minRange (GetAttributeRaw tup index) then
                           (snd search_term) tup
                         else false
                       | (None, None) => (snd search_term) tup
                       end)
      | right _ => k_fail heading indices kind index k
      end.

Ltac BuildEarlyRangeIndex
     heading indices kind index matcher k k_fail :=
  let is_equality := eval compute in (string_dec kind RangeIndex) in
      match is_equality with
      | left _ => k
                    (fun (search_term : prod (prod (option (Domain heading index)) (option (Domain heading index))) (@RawTuple heading -> bool))
                         (tup : @RawTuple heading) =>
                       match fst search_term with
                       | (Some minRange, Some maxRange) =>
                         if InRange_dec (GetAttributeRaw tup index) minRange maxRange then
                           matcher (snd search_term) tup
                         else false
                       | (None, Some maxRange) =>
                         if le_dec (GetAttributeRaw tup index) maxRange then
                           matcher (snd search_term)  tup
                         else false
                       | (Some minRange, None) =>
                         if le_dec minRange (GetAttributeRaw tup index) then
                           matcher (snd search_term) tup
                         else false
                       | (None, None) => matcher (snd search_term) tup
                       end)
      | right _ => k_fail heading indices kind index matcher k
      end.

Ltac matchRangeIndex qsSchema WhereClause k k_fail := idtac.
  (*match WhereClause with
  | fun tups => (@?C2 tups) <= (@?C1 tups) <= _ =>
    TermAttributes C1 ltac:(fun Ridx1 attr1 =>
                              TermAttributes C2
                                             ltac:(fun Ridx2 attr2 =>
                                                     k (@InsertOccurenceOfAny _ qsSchema Ridx1 (RangeIndex, attr1) (@InsertOccurenceOfAny _ qsSchema Ridx2 (RangeIndex, attr2) (InitOccurences _)))))

  | fun tups => _ <= (@?C1 tups) <= (@?C2 tups) =>
    TermAttributes C1 ltac:(fun Ridx1 attr1 =>
                              TermAttributes C2
                                             ltac:(fun Ridx2 attr2 =>
                                                     k (@InsertOccurenceOfAny _ qsSchema Ridx1 (RangeIndex, attr1) (@InsertOccurenceOfAny _ qsSchema Ridx2 (RangeIndex, attr2) (InitOccurences _)))))

  | fun tups => (@?C1 tups) <= (@?C2 tups) =>
    TermAttributes C1 ltac:(fun Ridx1 attr1 =>
                              TermAttributes C2
                                             ltac:(fun Ridx2 attr2 =>
                                                     k (@InsertOccurenceOfAny _ qsSchema Ridx1 (RangeIndex, attr1) (@InsertOccurenceOfAny _ qsSchema Ridx2 (RangeIndex, attr2) (InitOccurences _)))))

  | fun tups => _ <= (@?C1 tups) =>
    TermAttributes C1 ltac:(fun Ridx attr =>
                              k (@InsertOccurenceOfAny _ qsSchema Ridx (RangeIndex, attr) (InitOccurences _)))
  | fun tups => (@?C1 tups) <= _ =>
    TermAttributes C1 ltac:(fun Ridx attr =>
                              k (@InsertOccurenceOfAny _ qsSchema Ridx (RangeIndex, attr) (InitOccurences _)))
  | _ => k_fail qsSchema WhereClause k
  end. *)

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
           ltac:(fun X => k (X, tail)))
          || k ((@None nat, @None nat), tail)
      | _ => k_fail f fds tail fs kind s k
      end.

Ltac createLastRangeTerm_dep dom f fds tail fs kind s k k_fail :=
  let is_equality := eval compute in (string_dec kind "RangeIndex") in
      match is_equality with
      | left _ =>
        (findMatchingTerm
           fds kind s
           ltac:(fun X => k (fun x : dom => (X x, tail x)))
                  || k (fun x : dom => ((@None nat, @None nat), tail x )))
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

Module StringRangeTreeBag := RangeTreeBag String_as_OT.
Module NatRangeTreeBag := RangeTreeBag Nat_as_OT.
Module NRangeTreeBag := RangeTreeBag N_as_OT.
Module ZRangeTreeBag := RangeTreeBag Z_as_OT.

Definition NatRangeTreeBag'
           (heading : RawHeading)
           {BagType SearchTermType UpdateTermType : Type}
           (TBag : Bag BagType (@RawTuple heading) SearchTermType UpdateTermType)
           (projection : RawTuple -> NatRangeTreeBag.MoreXMapFacts.TKey)
           (bupdate_transform : UpdateTermType -> RawTuple -> RawTuple)
  : Bag (NatRangeTreeBag.RangeTreeBag (BagType := BagType)) (@RawTuple heading)
        (option NatRangeTreeBag.MoreXMapFacts.TKey *
         option NatRangeTreeBag.MoreXMapFacts.TKey * SearchTermType)
        UpdateTermType :=
  {| bempty            := NatRangeTreeBag.RangeTreeBag_bempty;
     bfind_matcher    :=
       fun (search_term : prod _ SearchTermType)
           (tup : @RawTuple heading) =>
         match fst search_term with
         | (Some minRange, Some maxRange) =>
           if InRange_dec (projection tup) minRange maxRange then
             (bfind_matcher (snd search_term)) tup
           else false
         | (None, Some maxRange) =>
           if le_dec (projection tup) maxRange then
             (bfind_matcher (snd search_term)) tup
           else false
         | (Some minRange, None) =>
           if le_dec minRange (projection tup) then
             (bfind_matcher (snd search_term)) tup
           else false
         | (None, None) => (bfind_matcher (snd search_term)) tup
         end;
     bupdate_transform := bupdate_transform;

     benumerate := NatRangeTreeBag.RangeTreeBag_benumerate TBag;
     bfind      := NatRangeTreeBag.RangeTreeBag_bfind TBag;
     binsert    := NatRangeTreeBag.RangeTreeBag_binsert TBag projection;
     bcount     := NatRangeTreeBag.RangeTreeBag_bcount TBag;
     bdelete    := NatRangeTreeBag.RangeTreeBag_bdelete TBag;
     bupdate    := NatRangeTreeBag.RangeTreeBag_bupdate TBag |}.

Lemma bfind_matcher_eq          (heading : RawHeading)
      {BagType SearchTermType UpdateTermType : Type}
      (TBag : Bag BagType (@RawTuple heading) SearchTermType UpdateTermType)
      projection
  : NatRangeTreeBag.RangeTreeBag_bfind_matcher TBag projection
    = @bfind_matcher _ _ _ _ (NatRangeTreeBag' _ _ projection bupdate_transform).
Proof.
  repeat (apply functional_extensionality; intros).
  destruct x as [ [ [st | ] [st' | ] ] st''];
    unfold NatRangeTreeBag.RangeTreeBag_bfind_matcher,
    NatRangeTreeBag.Range_InRange; simpl;
    unfold NatRangeTreeBag.X_le_dec; simpl;
    unfold InRange_dec;
    repeat first [
             solve [ eauto ]
           | match goal with
             | |- appcontext[Nat_as_OT.compare ?st ?st'] =>
               destruct (Nat_as_OT.compare st st'); simpl
             | |- appcontext[le_dec ?st ?st'] =>
               destruct (le_dec st st'); simpl
             end
           | progress (unfold Nat_as_OT.lt, Nat_as_OT.eq in *; omega)
           ].
Qed.

Instance NatRangeTreeBagCorrect
         (heading : RawHeading)
         {BagType SearchTermType UpdateTermType : Type}
         (TBag : Bag BagType (@RawTuple heading) SearchTermType UpdateTermType)
         (RepInv : BagType -> Prop)
         (ValidUpdate : UpdateTermType -> Prop)
         (CorrectTBag : CorrectBag RepInv ValidUpdate TBag)
         (projection : RawTuple -> NatRangeTreeBag.MoreXMapFacts.TKey)
  : @CorrectBag _ _ _
                UpdateTermType
                (NatRangeTreeBag.RangeTreeBag_RepInv _ RepInv projection)
                (NatRangeTreeBag.RangeTreeBag_ValidUpdate _ ValidUpdate projection)
                (@NatRangeTreeBag' heading BagType  SearchTermType UpdateTermType TBag projection bupdate_transform) :=
  { bempty_RepInv     := @NatRangeTreeBag.RangeTreeBag_Empty_RepInv BagType RawTuple SearchTermType UpdateTermType TBag RepInv projection;
    binsert_RepInv    := NatRangeTreeBag.RangeTreeBag_binsert_Preserves_RepInv CorrectTBag (projection := projection);
    bdelete_RepInv    := NatRangeTreeBag.RangeTreeBag_bdelete_Preserves_RepInv CorrectTBag (projection := projection);
    bupdate_RepInv    := NatRangeTreeBag.RangeTreeBag_bupdate_Preserves_RepInv CorrectTBag (projection := projection);

    binsert_enumerate := NatRangeTreeBag.RangeTreeBag_BagInsertEnumerate CorrectTBag (projection := projection);
    benumerate_empty  := NatRangeTreeBag.RangeTreeBag_BagEnumerateEmpty (TBag := TBag)
  }.
destruct (bfind_matcher_eq heading TBag projection);
  apply (NatRangeTreeBag.RangeTreeBag_BagFindCorrect CorrectTBag (projection := projection)).
destruct (bfind_matcher_eq heading TBag projection);
  apply (NatRangeTreeBag.RangeTreeBag_BagCountCorrect CorrectTBag (projection := projection)).
destruct (bfind_matcher_eq heading TBag projection);
  apply (NatRangeTreeBag.RangeTreeBag_BagDeleteCorrect CorrectTBag (projection := projection)).
destruct (bfind_matcher_eq heading TBag projection);
  apply (NatRangeTreeBag.RangeTreeBag_BagUpdateCorrect CorrectTBag (projection := projection)).
Qed.


Ltac BuildLastRangeTreeBag heading AttrList AttrKind AttrIndex k k_fail :=
  let is_equality := eval compute in (string_dec AttrKind "RangeIndex") in
      match is_equality with
      | left _ =>
        let AttrType := eval compute in (Domain heading AttrIndex) in
            match AttrType with
            | nat =>
              k (@NatRangeTreeBagCorrect _ _ _ _ _ _ _
                                         (@CountingListAsCorrectBag
                                            (@RawTuple heading)
                                            (IndexedTreeUpdateTermType heading)
                                            (IndexedTreebupdate_transform heading))
                                         (fun x => GetAttributeRaw (heading := heading) x AttrIndex))

            end
      | right _ => k_fail heading AttrList AttrKind AttrIndex k
      end.

Ltac BuildEarlyRangeTreeBag heading AttrList AttrKind AttrIndex subtree k k_fail :=
  let is_equality := eval compute in (string_dec AttrKind "RangeIndex") in
      match is_equality with
      | left _ =>
        let AttrType := eval compute in (Domain heading AttrIndex) in
            match AttrType with
            | nat =>
              k (@NatRangeTreeBagCorrect _ _ _ _ _ _ _
                                         subtree
                                         (fun x => GetAttributeRaw (heading := heading) x AttrIndex))

            end
      | right _ => k_fail heading AttrList AttrKind AttrIndex subtree k
      end.

Ltac RangeIndexTactics f :=
  PackageIndexTactics
    InRangeExpressionAttributeCounter
    BuildEarlyRangeIndex BuildLastRangeIndex
    RangeIndexUse createEarlyRangeTerm createLastRangeTerm
    RangeIndexUse_dep createEarlyRangeTerm_dep createLastRangeTerm_dep
    BuildEarlyRangeTreeBag BuildLastRangeTreeBag f.
