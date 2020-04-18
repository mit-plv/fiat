Require Export Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsInterface
        Fiat.QueryStructure.Implementation.DataStructures.Bags.CountingListBags
        Fiat.QueryStructure.Implementation.DataStructures.Bags.TreeBags
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.QueryStructure.Specification.Representation.Heading
        Coq.Lists.List Coq.Program.Program
        Fiat.Common.ilist.
Require Import Coq.Bool.Bool Coq.Strings.String
        Coq.Structures.OrderedTypeEx Coq.NArith.BinNat
        Coq.ZArith.ZArith_dec Coq.Arith.Arith
        Coq.FSets.FMapAVL
        Fiat.Common.Ensembles.EnsembleListEquivalence
        Fiat.Common.String_as_OT
        Fiat.Common.List.ListFacts
        Fiat.Common.ilist2
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Common.DecideableEnsembles
        Fiat.QueryStructure.Implementation.Operations.General.QueryRefinements
        Fiat.QueryStructure.Implementation.Operations.General.EmptyRefinements
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.Common.List.PermutationFacts
        Fiat.Common.List.ListMorphisms
        Fiat.QueryStructure.Specification.Operations.Delete
        Fiat.QueryStructure.Implementation.Operations.General.DeleteRefinements
        Fiat.QueryStructure.Implementation.Operations.List.ListQueryRefinements.

Unset Implicit Arguments.

Definition TSearchTermMatcher (heading: RawHeading) := (@RawTuple heading -> bool).

Definition RawTupleEqualityMatcher
           {heading: RawHeading}
           (attr: Attributes heading)
           (value: Domain heading attr)
           {ens_dec: DecideableEnsemble (fun x : Domain heading attr => value = x)} :=
  fun tuple => dec (tuple attr).

Definition RawTupleDisequalityMatcher
           {heading: RawHeading}
           (attr: Attributes heading)
           (value: Domain heading attr)
           {ens_dec: DecideableEnsemble (fun x : Domain heading attr => value = x)} :=
  fun tuple => negb (dec (tuple attr)).

Module NIndexedMap := FMapAVL.Make N_as_OT.
Module ZIndexedMap := FMapAVL.Make Z_as_OT.
Module NatIndexedMap := FMapAVL.Make Nat_as_OT.
Module StringIndexedMap := FMapAVL.Make String_as_OT.

Module NTreeBag := TreeBag NIndexedMap.
Module ZTreeBag := TreeBag ZIndexedMap.
Module NatTreeBag := TreeBag NatIndexedMap.
Module StringTreeBag := TreeBag StringIndexedMap.

Definition NTreeType      := @NTreeBag.IndexedBag.
Definition ZTreeType      := @ZTreeBag.IndexedBag.
Definition NatTreeType    := @NatTreeBag.IndexedBag.
Definition StringTreeType := @StringTreeBag.IndexedBag.

Record ProperAttribute {heading} :=
  {
    Attribute : Attributes heading;
    ProperlyTyped: { Domain heading Attribute = BinNums.N } + { Domain heading Attribute = BinNums.Z } +
                   { Domain heading Attribute = nat } + { Domain heading Attribute = string }
  }.

Definition ProperAttributeToFMap
           {heading}
           (pattr : @ProperAttribute heading)
: Type -> Type :=
  let (attr', cast) := pattr in
  match cast with
    | inleft (inleft (left cast'))  => @NTreeBag.IndexedBag
    | inleft (inleft (right cast')) => @ZTreeBag.IndexedBag
    | inleft (inright cast')         => @NatTreeBag.IndexedBag
    | inright cast'                  => @StringTreeBag.IndexedBag
  end.

Fixpoint NestedTreeFromAttributes
         {heading}
         (indices : list (@ProperAttribute heading))
: Type :=
  match indices with
    | [] => @CountingList (@RawTuple heading)
    | idx :: indices' =>
      ProperAttributeToFMap idx (NestedTreeFromAttributes indices')
  end.

Definition ProperAttributeToFMapKey
           {heading}
           (pattr : @ProperAttribute heading)
: Type :=
  let (attr', cast) := pattr in
  match cast with
    | inleft (inleft (left cast'))  => @NTreeBag.TKey
    | inleft (inleft (right cast')) => @ZTreeBag.TKey
    | inleft (inright cast')         => @NatTreeBag.TKey
    | inright cast'                  => @StringTreeBag.TKey
  end.

Fixpoint BuildSearchTermFromAttributes {heading}
         (indices : list (@ProperAttribute heading))
: Type :=
  match indices with
    | [] => (@RawTuple heading -> bool)
    | idx :: indices' => prod (option (ProperAttributeToFMapKey idx)) (BuildSearchTermFromAttributes indices')
  end.

Definition ProperAttribute_eq {heading}
           (index : @ProperAttribute heading)
           (k : ProperAttributeToFMapKey index)
           (attr : Domain heading (Attribute index))
: bool.
Proof.
  destruct index; simpl in *.
  destruct (ProperlyTyped0) as [ [ [ | ] | ]| ];
    rewrite e in attr.
  exact (if (N_eq_dec attr k) then true else false).
  exact (if (Z_eq_dec attr k) then true else false).
  exact (if (eq_nat_dec attr k) then true else false).
  exact (if (string_dec attr k) then true else false).
Defined.

Fixpoint SearchTermFromAttributesMatcher {heading}
         (indices : list (@ProperAttribute heading))
: BuildSearchTermFromAttributes indices -> @RawTuple heading -> bool :=
  match indices return
        BuildSearchTermFromAttributes indices -> @RawTuple heading -> bool
  with
    | nil => fun f tup => f tup
    | index :: indices' =>
      (fun (H : BuildSearchTermFromAttributes indices' -> @RawTuple heading -> bool)
           (f : prod (option (ProperAttributeToFMapKey index))
                     (BuildSearchTermFromAttributes indices'))
           (tup : @RawTuple heading) =>
         match f with
           | (Some k, index') => (ProperAttribute_eq index k (GetAttributeRaw tup (Attribute index))) && (H index' tup)
           | (None, index') => H index' tup
         end) (SearchTermFromAttributesMatcher indices')
  end.


Definition cast {T1 T2: Type} (eq: T1 = T2) (x: T1) : T2.
Proof.
  subst; auto.
Defined.

Definition ProperAttributeToBag
           {heading}
           TBag TSearchTerm TUpdateTerm
           (TBagAsBag : Bag TBag (@RawTuple heading) TSearchTerm TUpdateTerm)
           (pattr : @ProperAttribute heading)
: Bag (ProperAttributeToFMap pattr TBag) (@RawTuple heading)
      (prod (option (ProperAttributeToFMapKey pattr)) TSearchTerm) TUpdateTerm :=
  match pattr as pattr' return
        Bag (ProperAttributeToFMap pattr' TBag) (@RawTuple heading)
            (prod (option (ProperAttributeToFMapKey pattr')) TSearchTerm) TUpdateTerm with
    | {| Attribute := attr; ProperlyTyped := inleft (inleft (left cast')) |}
      => NTreeBag.IndexedBagAsBag TBagAsBag (fun x => cast cast' (GetAttributeRaw x attr))
    | {| Attribute := attr; ProperlyTyped := inleft (inleft (right cast')) |}
      => ZTreeBag.IndexedBagAsBag TBagAsBag (fun x => cast cast' (GetAttributeRaw x attr))
    | {| Attribute := attr; ProperlyTyped := inleft (inright cast') |}
      => NatTreeBag.IndexedBagAsBag TBagAsBag (fun x => cast cast' (GetAttributeRaw x attr))
    | {| Attribute := attr; ProperlyTyped := inright cast' |}
      => StringTreeBag.IndexedBagAsBag TBagAsBag (fun x => cast cast' (GetAttributeRaw x attr))
  end.

Fixpoint NestedTreeFromAttributesAsBag
         heading
         TUpdateTerm
         (bupdate_transform : TUpdateTerm -> @RawTuple heading -> @RawTuple heading)
         (indices : list (@ProperAttribute heading))
: Bag (NestedTreeFromAttributes indices)
      (@RawTuple heading)
      (BuildSearchTermFromAttributes indices)
      TUpdateTerm :=
  match indices return
        Bag (NestedTreeFromAttributes indices)
            (@RawTuple heading)
            (BuildSearchTermFromAttributes indices)
            TUpdateTerm with
    | [] => CountingListAsBag bupdate_transform
    | idx :: indices' => ProperAttributeToBag
                           _ _ _
                           (NestedTreeFromAttributesAsBag heading _ bupdate_transform indices') idx
  end.

Definition IndexedTreeUpdateTermType heading :=
  @RawTuple heading -> @RawTuple heading.

Definition IndexedTreebupdate_transform heading
           (upd : IndexedTreeUpdateTermType heading)

: @RawTuple heading -> @RawTuple heading := upd.

Instance NestedTreeFromAttributesAsBag'
         {heading}
         (indices : list (@ProperAttribute heading))
: Bag (NestedTreeFromAttributes indices)
      (@RawTuple heading)
      (BuildSearchTermFromAttributes indices)
      (IndexedTreeUpdateTermType heading) :=
  NestedTreeFromAttributesAsBag
    heading (IndexedTreeUpdateTermType heading)
    (IndexedTreebupdate_transform heading)
    indices.

Definition ProperAttributeToRepInv
           {heading}
           TBag TSearchTerm TUpdateTerm
           (RepInv : TBag -> Prop)
           (TBagAsBag : Bag TBag (@RawTuple heading) TSearchTerm TUpdateTerm)
           (pattr : @ProperAttribute heading)
: (@RawTuple heading -> ProperAttributeToFMapKey pattr)
  -> ProperAttributeToFMap pattr TBag -> Prop  :=
  match pattr as pattr' return
        (@RawTuple heading -> ProperAttributeToFMapKey pattr')
        -> ProperAttributeToFMap pattr' TBag -> Prop with
    | {| Attribute := attr; ProperlyTyped := inleft (inleft (left cast')) |}
      => NTreeBag.IndexedBag_RepInv TBagAsBag RepInv
    | {| Attribute := attr; ProperlyTyped := inleft (inleft (right cast')) |}
      => ZTreeBag.IndexedBag_RepInv TBagAsBag RepInv
    | {| Attribute := attr; ProperlyTyped := inleft (inright cast') |}
      => NatTreeBag.IndexedBag_RepInv TBagAsBag RepInv
    | {| Attribute := attr; ProperlyTyped := inright cast' |}
      => StringTreeBag.IndexedBag_RepInv TBagAsBag RepInv
  end.

Definition ProperAttributeToProjection
           {heading}
           (pattr : @ProperAttribute heading)
: @RawTuple heading -> ProperAttributeToFMapKey pattr :=
  match pattr as pattr' return
        @RawTuple heading -> ProperAttributeToFMapKey pattr' with
    | {| Attribute := attr; ProperlyTyped := inleft (inleft (left cast')) |}
      => fun x => cast cast' (GetAttributeRaw x attr)
    | {| Attribute := attr; ProperlyTyped := inleft (inleft (right cast')) |}
      => fun x => cast cast' (GetAttributeRaw x attr)
    | {| Attribute := attr; ProperlyTyped := inleft (inright cast') |}
      => fun x => cast cast' (GetAttributeRaw x attr)
    | {| Attribute := attr; ProperlyTyped := inright cast' |}
      => fun x => cast cast' (GetAttributeRaw x attr)
  end.

Definition ProperAttributeToValidUpdate
           {heading}
           TBag TSearchTerm TUpdateTerm
           (ValidUpdate : TUpdateTerm -> Prop)
           (TBagAsBag : Bag TBag (@RawTuple heading) TSearchTerm TUpdateTerm)
           (pattr : @ProperAttribute heading)
: (@RawTuple heading -> ProperAttributeToFMapKey pattr)
  -> TUpdateTerm -> Prop  :=
  match pattr as pattr' return
        (@RawTuple heading -> ProperAttributeToFMapKey pattr')
        -> TUpdateTerm -> Prop with
    | {| Attribute := attr; ProperlyTyped := inleft (inleft (left cast')) |}
      => NTreeBag.IndexedBag_ValidUpdate TBagAsBag ValidUpdate
    | {| Attribute := attr; ProperlyTyped := inleft (inleft (right cast')) |}
      => ZTreeBag.IndexedBag_ValidUpdate TBagAsBag ValidUpdate
    | {| Attribute := attr; ProperlyTyped := inleft (inright cast') |}
      => NatTreeBag.IndexedBag_ValidUpdate TBagAsBag ValidUpdate
    | {| Attribute := attr; ProperlyTyped := inright cast' |}
      => StringTreeBag.IndexedBag_ValidUpdate TBagAsBag ValidUpdate
  end.

Definition ProperAttributeToCorrectBag
           {heading}
           TBag TSearchTerm TUpdateTerm
           (TBagAsBag : Bag TBag (@RawTuple heading) TSearchTerm TUpdateTerm)
           (RepInv : TBag -> Prop)
           (ValidUpdate : TUpdateTerm -> Prop)
           (TBagAsCorrectBag : CorrectBag RepInv ValidUpdate TBagAsBag)
           (pattr : @ProperAttribute heading)
:  CorrectBag (ProperAttributeToRepInv _ _ _ RepInv TBagAsBag pattr
                                       (ProperAttributeToProjection pattr))
              (ProperAttributeToValidUpdate  _ _ _ ValidUpdate TBagAsBag pattr
                                             (ProperAttributeToProjection pattr))
              (ProperAttributeToBag TBag TSearchTerm TUpdateTerm TBagAsBag pattr) :=
  match pattr as pattr' return
        CorrectBag (ProperAttributeToRepInv _ _ _ RepInv TBagAsBag pattr'
                                            (ProperAttributeToProjection pattr'))
                   (ProperAttributeToValidUpdate  _ _ _ ValidUpdate TBagAsBag pattr'
                                                  (ProperAttributeToProjection pattr'))
                   (ProperAttributeToBag TBag TSearchTerm TUpdateTerm TBagAsBag pattr') with
    | {| Attribute := attr; ProperlyTyped := inleft (inleft (left cast')) |}
      => NTreeBag.IndexedBagAsCorrectBag TBagAsBag RepInv ValidUpdate TBagAsCorrectBag
                                         (fun x => cast cast' (GetAttributeRaw x attr))
    | {| Attribute := attr; ProperlyTyped := inleft (inleft (right cast')) |}
      => ZTreeBag.IndexedBagAsCorrectBag TBagAsBag RepInv ValidUpdate TBagAsCorrectBag
                                         (fun x => cast cast' (GetAttributeRaw x attr))
    | {| Attribute := attr; ProperlyTyped := inleft (inright cast') |}
      => NatTreeBag.IndexedBagAsCorrectBag TBagAsBag RepInv ValidUpdate TBagAsCorrectBag
                                           (fun x => cast cast' (GetAttributeRaw x attr))
    | {| Attribute := attr; ProperlyTyped := inright cast' |}
      => StringTreeBag.IndexedBagAsCorrectBag TBagAsBag RepInv ValidUpdate TBagAsCorrectBag
                                              (fun x => cast cast' (GetAttributeRaw x attr))
  end.

Fixpoint ProperAttributesToRepInv
         {heading}
         TUpdateTerm
         (bupdate_transform : TUpdateTerm -> @RawTuple heading -> @RawTuple heading)
         (indices : list (@ProperAttribute heading))
: NestedTreeFromAttributes indices -> Prop :=
  match indices return NestedTreeFromAttributes indices -> Prop with
    | [] => CountingList_RepInv
    | idx :: indices' =>
      ProperAttributeToRepInv _ _ TUpdateTerm
                              (ProperAttributesToRepInv TUpdateTerm bupdate_transform indices')
                              (NestedTreeFromAttributesAsBag heading TUpdateTerm bupdate_transform indices') idx
                              (ProperAttributeToProjection idx)
  end.

Fixpoint ProperAttributesToValidUpdate
         {heading}
         TUpdateTerm
         (bupdate_transform : TUpdateTerm -> @RawTuple heading -> @RawTuple heading)
         (indices : list (@ProperAttribute heading))
: TUpdateTerm -> Prop :=
  match indices return TUpdateTerm -> Prop with
    | [] => CountingList_ValidUpdate
    | idx :: indices' =>
      ProperAttributeToValidUpdate _ _ TUpdateTerm
                                   (ProperAttributesToValidUpdate TUpdateTerm bupdate_transform indices')
                                   (NestedTreeFromAttributesAsBag heading TUpdateTerm bupdate_transform indices') idx
                                   (ProperAttributeToProjection idx)
  end.

Program Fixpoint NestedTreeFromAttributesAsCorrectBag
        heading
        TUpdateTerm
        (bupdate_transform : TUpdateTerm -> @RawTuple heading -> @RawTuple heading)
        (indices : list (@ProperAttribute heading))
: CorrectBag (ProperAttributesToRepInv TUpdateTerm bupdate_transform indices)
             (ProperAttributesToValidUpdate TUpdateTerm bupdate_transform indices)
             (NestedTreeFromAttributesAsBag heading TUpdateTerm
                                            bupdate_transform indices) :=
  match indices return
        CorrectBag (ProperAttributesToRepInv TUpdateTerm bupdate_transform indices)
                   (ProperAttributesToValidUpdate TUpdateTerm bupdate_transform indices)
                   (NestedTreeFromAttributesAsBag heading TUpdateTerm
                                                  bupdate_transform indices) with
    | [] => CountingListAsCorrectBag bupdate_transform
    | idx :: indices' =>
      ProperAttributeToCorrectBag
        _ _ _
        (NestedTreeFromAttributesAsBag heading TUpdateTerm bupdate_transform indices')
        (ProperAttributesToRepInv TUpdateTerm bupdate_transform indices')
        (ProperAttributesToValidUpdate TUpdateTerm bupdate_transform indices')
        (NestedTreeFromAttributesAsCorrectBag heading TUpdateTerm bupdate_transform
                                              indices')
        idx
  end.

Lemma bupdate_transform_NestedTree :
  forall heading
         TUpdateTerm
         (bupdate_transform' : TUpdateTerm -> @RawTuple heading -> @RawTuple heading)
         (indices : list (@ProperAttribute heading)),
    bupdate_transform
      (Bag := NestedTreeFromAttributesAsBag _ _ bupdate_transform' indices) =
    bupdate_transform'.
Proof.
  induction indices; simpl; eauto.
  destruct a as [attr [ [ [s | s] | s] | s ] ]; simpl in *; eauto.
Qed.

Lemma KeyPreservingUpdateFAsUpdateTermOK {heading}
: forall (indices indices' : list (@ProperAttribute heading))
         (f : @RawTuple heading -> @RawTuple heading),
    (forall a, List.In a indices -> List.In a indices')
    -> (forall K tup,
          List.In K indices'
          -> GetAttributeRaw (f tup) (@Attribute _ K) = GetAttributeRaw tup (@Attribute _ K))
    -> ProperAttributesToValidUpdate (@RawTuple heading -> @RawTuple heading)
                                     (fun upd tup => upd tup)
                                     indices f.
Proof.
  induction indices; simpl; intuition.
  - unfold CountingList_ValidUpdate; auto.
  - destruct a as [attr [ [ [s | s] | s] | s ] ]; simpl in *.
    + unfold NTreeBag.IndexedBag_ValidUpdate; intuition.
      eapply (IHindices indices'); eauto.
      rewrite bupdate_transform_NestedTree, <- H1.
      erewrite (H0 {| Attribute := attr; ProperlyTyped := inleft (inleft in_left) |});
        simpl; eauto.
    + unfold ZTreeBag.IndexedBag_ValidUpdate; intuition.
      eapply (IHindices indices'); eauto.
      rewrite bupdate_transform_NestedTree, <- H1.
      erewrite (H0 {| Attribute := attr; ProperlyTyped := inleft (inleft in_right) |});
        simpl; eauto.
    + unfold NatTreeBag.IndexedBag_ValidUpdate; intuition.
      eapply (IHindices indices'); eauto.
      rewrite bupdate_transform_NestedTree, <- H1.
      erewrite (H0 {| Attribute := attr; ProperlyTyped := inleft (inright s) |});
        simpl; eauto.
    + unfold StringTreeBag.IndexedBag_ValidUpdate; intuition.
      eapply (IHindices indices'); eauto.
      rewrite bupdate_transform_NestedTree, <- H1.
      erewrite (H0 {| Attribute := attr; ProperlyTyped := inright s |});
        simpl; eauto.
Qed.

Instance NestedTreeFromAttributesAsCorrectBag_UpdateF
         {heading}
         (indices : list (@ProperAttribute heading))
: CorrectBag (ProperAttributesToRepInv _ _ indices)
             (ProperAttributesToValidUpdate _ _ indices)
             (NestedTreeFromAttributesAsBag heading
                                            (@RawTuple heading -> @RawTuple heading)
                                            (fun upd tup => upd tup)
                                            indices)
  := NestedTreeFromAttributesAsCorrectBag heading _ _ _ .

Definition NestedTreeFromAttributesAsCorrectBagPlusProof
           {heading}
           (indices : list (@ProperAttribute heading))
: BagPlusProof (@RawTuple heading) :=
  {| CorrectBagPlus := (NestedTreeFromAttributesAsCorrectBag_UpdateF indices) |}.

Definition CheckType {heading} (attr: Attributes heading) (rightT: _) :=
  {| Attribute := attr; ProperlyTyped := rightT |}.


(* An equivalence relation between Ensembles of RawTuples and Bags
   which incorporates the bag's representation invariant. *)

Definition EnsembleBagEquivalence
           {heading : RawHeading}
           (bagplus : BagPlusProof (@RawTuple heading))
           (ens : Ensemble (@IndexedRawTuple heading))
           (store : BagTypePlus bagplus)
: Prop :=
  ens ≃ benumerate (Bag := BagPlus bagplus) store /\
  RepInvPlus bagplus store.

Instance EnsembleIndexedTreeEquivalence_AbsR
         {heading : RawHeading}
         {bagplus : BagPlusProof (@RawTuple heading)}
: @UnConstrRelationAbsRClass (@IndexedRawTuple heading) (BagTypePlus bagplus) :=
  {| UnConstrRelationAbsR := EnsembleBagEquivalence bagplus |}.

(* We now prove that [empty] is a valid abstraction of the
   empty database. *)

Lemma bempty_correct_DB :
  forall {TContainer TSearchTerm TUpdateTerm : Type}
         {db_schema : RawQueryStructureSchema}
         {index : Fin.t _}
         {store_is_bag : Bag TContainer RawTuple TSearchTerm TUpdateTerm}
         (RepInv : TContainer -> Prop)
         (ValidUpdate : TUpdateTerm -> Prop),
    CorrectBag RepInv ValidUpdate store_is_bag
    -> EnsembleIndexedListEquivalence
         (GetUnConstrRelation (imap2 rawRel (Build_EmptyRelations (qschemaSchemas db_schema))) index)
         (benumerate bempty).
Proof.
  intros.
  erewrite benumerate_empty_eq_nil by eauto.
  apply EnsembleIndexedListEquivalence_Empty.
Qed.

Corollary bemptyPlus_correct_DB :
  forall {db_schema : RawQueryStructureSchema}
         {index : Fin.t _}
         {bag_plus : BagPlusProof (@RawTuple _)},
    GetUnConstrRelation (imap2 rawRel (Build_EmptyRelations (qschemaSchemas db_schema))) index ≃
                        bempty (Bag := BagPlus bag_plus).
Proof.
  destruct bag_plus; intros; simpl; constructor.
  eapply bempty_correct_DB; eauto.
  apply bempty_RepInv.
Qed.

(* We now prove that [binsert] is a valid abstraction of the
   adding a tuple to the ensemble modeling the database. *)


Lemma binsert_correct_DB
      db_schema qs index
      (bag_plus : BagPlusProof (@RawTuple _))
:  forall (store: BagTypePlus bag_plus),
     GetUnConstrRelation qs index ≃ store
     -> forall tuple bound
               (ValidBound : UnConstrFreshIdx (GetUnConstrRelation qs index) bound),
          EnsembleIndexedListEquivalence
            (GetUnConstrRelation
               (@UpdateUnConstrRelation db_schema qs index
                                        (EnsembleInsert
                                           {| elementIndex := bound;
                                              indexedElement := tuple |}
                                           (GetUnConstrRelation qs index))) index)
            (benumerate (binsert (Bag := BagPlus bag_plus) store tuple)).
Proof.
  intros * store_eqv; destruct store_eqv as (store_eqv, store_WF).
  unfold EnsembleIndexedTreeEquivalence_AbsR, UnConstrFreshIdx,
  EnsembleBagEquivalence, EnsembleIndexedListEquivalence,
  UnIndexedEnsembleListEquivalence, EnsembleListEquivalence in *.

  setoid_rewrite get_update_unconstr_eq.
  setoid_rewrite in_ensemble_insert_iff.
  setoid_rewrite NoDup_modulo_permutation.
  split; intros.

  unfold UnConstrFreshIdx; exists (S bound); intros; intuition; subst; simpl.
  unfold EnsembleInsert in *; intuition; subst; simpl; omega.
  (* erewrite binsert_enumerate_length by eauto with typeclass_instances.
    intuition; subst;
    [ | apply lt_S];
    intuition. *)

  destruct store_eqv as (indices & [ l' (map & equiv & nodup ) ]); eauto.

  destruct (permutation_map_cons indexedElement (binsert_enumerate tuple store store_WF)
                                 {| elementIndex := bound;
                                    indexedElement := tuple |} l' eq_refl map)
    as [ l'0 (map' & perm) ].

  exists l'0.
  split; [ assumption | split ].

  setoid_rewrite perm; setoid_rewrite equiv;
  simpl; intuition eauto.

  eexists (bound :: _); split; try apply perm; eauto.

  constructor; eauto.
  unfold not; intros.
  rewrite in_map_iff in H0; destruct_ex; intuition; subst.
  apply equiv in H3; apply H in H3; destruct x; simpl in *; omega.

  setoid_rewrite perm; reflexivity.
Qed.

Corollary binsertPlus_correct_DB :
  forall {db_schema : RawQueryStructureSchema}
         qs
         (index : Fin.t _)
         (bag_plus : BagPlusProof RawTuple)
         store,
    GetUnConstrRelation qs index ≃ store
    -> forall
      tuple bound
      (ValidBound : UnConstrFreshIdx (GetUnConstrRelation qs index) bound),
      GetUnConstrRelation
        (@UpdateUnConstrRelation db_schema qs index
                                 (EnsembleInsert
                                    {| elementIndex := bound;
                                       indexedElement := tuple |}
                                    (GetUnConstrRelation qs index))) index
        ≃ binsert (Bag := BagPlus bag_plus) store tuple.
Proof.
  simpl; intros; constructor.
  - eapply binsert_correct_DB; eauto.
  - eapply binsert_RepInv; apply H.
Qed.

Lemma bdelete_correct_DB_fst {qsSchema}
: forall (qs : UnConstrQueryStructure qsSchema)
         (Ridx : Fin.t _)
         bag_plus
         bag
         (equiv_bag : EnsembleBagEquivalence bag_plus (GetUnConstrRelation qs Ridx) bag)
         (DT : Ensemble RawTuple)
         (DT_Dec : DecideableEnsemble DT)
         search_term,
    ExtensionalEq (@dec _ _ DT_Dec)
                  (bfind_matcher (Bag := BagPlus bag_plus) search_term)
    -> refine {x | QSDeletedTuples qs Ridx DT x}
              (ret (fst (bdelete bag search_term))).
Proof.
  intros; setoid_rewrite DeletedTuplesFor; auto.
  destruct equiv_bag as [ [ [bound ValidBound] [l [eq_bag [NoDup_l equiv_l] ] ] ] RepInv_bag];
    subst.
  rewrite refine_List_Query_In.
  rewrite refine_List_Query_In_Where, refine_List_For_Query_In_Return_Permutation,
  (filter_by_equiv _ _ H), map_id, <- partition_filter_eq.
  rewrite refine_pick_val.
  reflexivity.
  destruct (bdelete_correct bag search_term RepInv_bag) as [_ Perm_bdelete];
    eauto.

  unfold BagPlusProofAsBag, QSGetNRelSchemaHeading, GetNRelSchemaHeading,
  GetNRelSchema in *.
  rewrite Perm_bdelete; reflexivity.
  econstructor.
  eexists _; eauto.
  unfold UnIndexedEnsembleListEquivalence; eexists; eauto.
Qed.

Lemma bdelete_correct_DB_snd
      db_schema qs index
      (bag_plus : BagPlusProof RawTuple)
:  forall (store: BagTypePlus bag_plus),
     GetUnConstrRelation qs index ≃ store
     -> forall (DeletedRawTuples : Ensemble RawTuple)
               (DT_Dec : DecideableEnsemble DeletedRawTuples),
          EnsembleIndexedListEquivalence
            (GetUnConstrRelation
               (@UpdateUnConstrRelation db_schema qs index
                                        (EnsembleDelete (GetUnConstrRelation qs index)
                                                        DeletedRawTuples)) index)
            (snd (List.partition (@dec _ _ DT_Dec)
                                 (benumerate store))).
Proof.
  simpl; unfold EnsembleDelete, EnsembleBagEquivalence, Ensembles.In, Complement; simpl;
  unfold EnsembleIndexedListEquivalence, UnIndexedEnsembleListEquivalence,
  EnsembleListEquivalence; intros; intuition; destruct_ex; intuition; subst.
  repeat setoid_rewrite get_update_unconstr_eq; simpl; intros.
  exists x0.
  unfold UnConstrFreshIdx in *; intros; apply H; destruct H3; eauto.
  exists (snd (partition (@dec IndexedRawTuple (fun t => DeletedRawTuples (indexedElement t)) _ ) x)); intuition.
  - unfold BagPlusProofAsBag; rewrite <- H2.
    repeat rewrite partition_filter_neq.
    clear; induction x; simpl; eauto.
    unfold indexedRawTuple in *;
      find_if_inside; simpl; eauto; rewrite <- IHx; reflexivity.
  - rewrite get_update_unconstr_eq in H3.
    destruct H3; unfold In in *.
    apply H0 in H3; eapply In_partition in H3; intuition; try apply H6.
    apply In_partition_matched in H6; apply dec_decides_P in H6; exfalso; eauto.
  - rewrite get_update_unconstr_eq; constructor.
    eapply H0; eapply In_partition; eauto.
    unfold In; intros.
    apply In_partition_unmatched in H3.
    simpl in *; apply dec_decides_P in H5.
    unfold indexedRawTuple, GetNRelSchema in *;
      rewrite H3 in H5; congruence.
  - revert H4; clear; induction x; simpl; eauto.
    intros; inversion H4; subst.
    case_eq (partition (fun x0 => @dec IndexedRawTuple (fun t => DeletedRawTuples (indexedElement t)) _ x0) x); intros; simpl in *; rewrite H.
    rewrite H in IHx; apply IHx in H2;
    case_eq (@dec IndexedRawTuple (fun t => DeletedRawTuples (indexedElement t)) _ a);
    intros; simpl in *; rewrite H0; simpl; eauto.
    constructor; eauto.
    unfold not; intros; apply H1.
    generalize l l0 H H3; clear; induction x; simpl; intros.
    + injections; simpl in *; eauto.
    + case_eq (partition (fun x0 : IndexedRawTuple => dec (indexedRawTuple x0)) x).
      intros; rewrite H0 in H; find_if_inside; injections.
      eauto.
      simpl in H3; intuition.
      eauto.
Qed.

Lemma bdeletePlus_correct_DB_snd
      db_schema qs index
      bag_plus
:  forall (store: BagTypePlus bag_plus),
     EnsembleBagEquivalence bag_plus (GetUnConstrRelation qs index) store
     -> forall (DeletedRawTuples : Ensemble RawTuple)
               (DT_Dec : DecideableEnsemble DeletedRawTuples)
               search_term,
          ExtensionalEq (@dec _ _ DT_Dec)
                        (bfind_matcher (Bag := BagPlus bag_plus) search_term)
          -> EnsembleBagEquivalence
               bag_plus
               (GetUnConstrRelation
                  (@UpdateUnConstrRelation db_schema qs index
                                           (EnsembleDelete (GetUnConstrRelation qs index)
                                                           DeletedRawTuples)) index)
               (snd (bdelete store search_term)).
Proof.
  intros; unfold ExtensionalEq, EnsembleBagEquivalence in *.
  unfold EnsembleBagEquivalence.
  repeat rewrite get_update_unconstr_eq; simpl; intros.

  split;
    [
      | eapply bdelete_RepInv; intuition ].
  simpl in *;
    unfold EnsembleListEquivalence, EnsembleIndexedListEquivalence,
    UnConstrFreshIdx, EnsembleDelete, Complement in *; intuition; destruct_ex; intuition; intros.
  exists x; intros; eapply H; destruct H1; unfold List.In in *; eauto.
  unfold UnIndexedEnsembleListEquivalence, EnsembleListEquivalence in *.
  generalize (bdelete_correct store search_term H2); destruct_ex; intuition.
  rewrite partition_filter_neq in H1.
  unfold BagPlusProofAsBag in *; simpl in *; rewrite <- H4 in H1.
  clear H6 H H2 H4.
  remember (GetUnConstrRelation qs index) as u.
  generalize DeletedRawTuples DT_Dec x0 u H1 H0 H3 H7; clear.
  induction (benumerate (snd (bdelete store search_term))); intros.
  - eexists []; simpl; intuition.
    + destruct H; destruct H2; unfold In in *.
      apply H3 in H.
      apply Permutation_nil in H1.
      apply dec_decides_P; rewrite H0.
      revert H1 H; clear; induction x0; simpl; eauto.
      case_eq (bfind_matcher (Bag := BagPlus bag_plus) search_term (indexedElement a)); simpl; intros.
      intuition; subst; eauto.
      discriminate.
    + constructor.
  - assert (exists a',
              List.In a' x0 /\ indexedElement a' = a
              /\ (bfind_matcher (Bag := BagPlus bag_plus) search_term (indexedElement a') = false)).
    generalize (@Permutation_in _ _ _ a H1 (or_introl (refl_equal _))).
    rewrite filter_map; clear; induction x0; simpl;
    intuition.
    revert H;
      case_eq (bfind_matcher (Bag := BagPlus bag_plus) search_term (indexedElement a0)); simpl; intros; eauto.
    apply IHx0 in H0; destruct_ex; intuition eauto.
    subst; intuition eauto.
    destruct_ex; intuition eauto.
    destruct_ex.
    assert (exists x0',
              Permutation x0 (x :: x0') /\
              ~ List.In x x0').
    {
      intuition; subst.
      repeat rewrite filter_map; generalize x H2 H7; clear;
      induction x0; intros; simpl in *|-; intuition; subst; eauto.
      inversion H7; subst; exists x0; intuition.
      apply H1; apply in_map_iff; eexists; eauto.
      inversion H7; subst.
      destruct (IHx0 _ H H3); intuition; eexists (a :: x1).
      rewrite H1; intuition.
      constructor.
      simpl in H0; intuition; subst; eauto.
      apply H2; apply in_map_iff; eexists; eauto.
    }
    destruct_ex; intuition; subst.
    rewrite filter_map in H1; rewrite H in H1; simpl in *.
    rewrite H8 in *; simpl in *.
    destruct (IHl DeletedRawTuples DT_Dec x1
                  (fun tup => Ensembles.In _ u tup /\ tup <> x)); eauto;
    clear IHl.
    + rewrite filter_map; eapply Permutation_cons_inv; eauto.
    + intuition; intros.
      destruct H2; apply H3 in H2.
      eapply Permutation_in in H; eauto.
      simpl in *; intuition.
      constructor.
      eapply H3.
      symmetry in H; eapply Permutation_in; eauto.
      simpl; eauto.
      intros; subst; simpl; congruence.
    + assert (NoDup (map elementIndex (x :: x1))).
      eapply NoDup_Permutation_rewrite.
      eapply Permutation_map; eauto.
      eauto.
      inversion H2; subst; eauto.
    + eexists (x :: x2); simpl; intuition.
      * rewrite H5; auto.
      * unfold In in H9; inversion H9; subst; unfold In in *.
        apply H3 in H11; pose proof (Permutation_in _ H H11).
        simpl in H5; intuition.
        right; apply Permutation_cons_inv in H1.
        eapply H2; econstructor; unfold In; intuition.
        apply H3 in H11; eauto.
        subst; eauto.
      * subst; unfold In in *.
        constructor; unfold In.
        apply H3.
        eapply Permutation_in; eauto.
        rewrite <- H0 in H8; intros; apply dec_decides_P in H5; congruence.
      * unfold In; constructor.
        apply H2 in H11; inversion H11; subst; unfold In in *; intuition.
        unfold In in *.
        intros; apply dec_decides_P in H9; subst.
        apply Permutation_cons_inv in H1.
        assert (List.In (indexedElement x3) (map indexedElement x2)) as in_x2' by
              (rewrite in_map_iff; eauto);
          pose proof (Permutation_in (indexedElement x3) H1 in_x2').
        rewrite in_map_iff in H5; destruct_ex; intuition.
        rewrite filter_In in H13; intuition; subst.
        rewrite <- H0, H12, H9 in H14; discriminate.
      * constructor; eauto.
        intro In_x; subst; apply Permutation_cons_inv in H1.
        pose proof (permutation_map_base _ H1 _  (refl_equal _));
          destruct_ex; intuition.
        rewrite in_map_iff in *; destruct_ex; intuition.
        apply H2 in H13; inversion H13; subst; unfold In in *; intuition.
        apply H3 in H15.
        pose proof (Permutation_in _ H H15); simpl in *; intuition.
        assert (~ List.In (elementIndex x) (map elementIndex x1)).
        { eapply Permutation_map with (f := elementIndex) in H.
          pose proof (NoDup_Permutation_rewrite _ _ H H7).
          simpl in *; inversion H5; subst; eauto.
        }
        apply H5; rewrite in_map_iff; eexists; split; eauto.
Qed.

Arguments bdelete : simpl never.
