Require Export ADTSynthesis.QueryStructure.Refinements.Bags.BagsInterface ADTSynthesis.QueryStructure.Refinements.Bags.CountingListBags ADTSynthesis.QueryStructure.Refinements.Bags.TreeBags ADTSynthesis.QueryStructure.Tuple ADTSynthesis.QueryStructure.Heading Coq.Lists.List Coq.Program.Program ADTSynthesis.Common.ilist.
Require Import ADTSynthesis.Common.String_as_OT ADTSynthesis.QueryStructure.IndexedEnsembles ADTSynthesis.Common.DecideableEnsembles.
Require Import Coq.Bool.Bool Coq.Strings.String Coq.Structures.OrderedTypeEx Coq.NArith.BinNat Coq.ZArith.ZArith_dec Coq.Arith.Arith.

Unset Implicit Arguments.

Require Import ADTSynthesis.QueryStructure.Refinements.GeneralQueryRefinements.

Definition TSearchTermMatcher (heading: Heading) := (@Tuple heading -> bool).

Definition TupleEqualityMatcher
           {heading: Heading}
           (attr: Attributes heading)
           (value: Domain heading attr)
           {ens_dec: DecideableEnsemble (fun x : Domain heading attr => value = x)} :=
  fun tuple => dec (tuple attr).

Definition TupleDisequalityMatcher
           {heading: Heading}
           (attr: Attributes heading)
           (value: Domain heading attr)
           {ens_dec: DecideableEnsemble (fun x : Domain heading attr => value = x)} :=
  fun tuple => negb (dec (tuple attr)).

Require Import Coq.FSets.FMapAVL.

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
    | [] => @CountingList (@Tuple heading)
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
      | [] => (list (@Tuple heading -> bool))
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
: BuildSearchTermFromAttributes indices -> @Tuple heading -> bool :=
  match indices return
        BuildSearchTermFromAttributes indices -> @Tuple heading -> bool
  with
    | nil => fun f tup => MatchAgainstMany f tup
    | index :: indices' =>
      (fun (H : BuildSearchTermFromAttributes indices' -> @Tuple heading -> bool)
           (f : prod (option (ProperAttributeToFMapKey index))
                     (BuildSearchTermFromAttributes indices'))
           (tup : @Tuple heading) =>
         match f with
           | (Some k, index') => (ProperAttribute_eq index k (tup (Attribute index))) && (H index' tup)
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
           (TBagAsBag : Bag TBag (@Tuple heading) TSearchTerm TUpdateTerm)
           (pattr : @ProperAttribute heading)
: Bag (ProperAttributeToFMap pattr TBag) (@Tuple heading)
      (prod (option (ProperAttributeToFMapKey pattr)) TSearchTerm) TUpdateTerm :=
  match pattr as pattr' return
        Bag (ProperAttributeToFMap pattr' TBag) (@Tuple heading)
            (prod (option (ProperAttributeToFMapKey pattr')) TSearchTerm) TUpdateTerm with
    | {| Attribute := attr; ProperlyTyped := inleft (inleft (left cast')) |}
      => NTreeBag.IndexedBagAsBag TBagAsBag (fun x => cast cast' (x attr))
    | {| Attribute := attr; ProperlyTyped := inleft (inleft (right cast')) |}
      => ZTreeBag.IndexedBagAsBag TBagAsBag (fun x => cast cast' (x attr))
    | {| Attribute := attr; ProperlyTyped := inleft (inright cast') |}
      => NatTreeBag.IndexedBagAsBag TBagAsBag (fun x => cast cast' (x attr))
    | {| Attribute := attr; ProperlyTyped := inright cast' |}
      => StringTreeBag.IndexedBagAsBag TBagAsBag (fun x => cast cast' (x attr))
  end.

 Fixpoint NestedTreeFromAttributesAsBag
         heading
         TUpdateTerm
         (bupdate_transform : TUpdateTerm -> @Tuple heading -> @Tuple heading)
         (indices : list (@ProperAttribute heading))
: Bag (NestedTreeFromAttributes indices)
      (@Tuple heading)
      (BuildSearchTermFromAttributes indices)
      TUpdateTerm :=
   match indices return
         Bag (NestedTreeFromAttributes indices)
             (@Tuple heading)
             (BuildSearchTermFromAttributes indices)
               TUpdateTerm with
     | [] => CountingListAsBag bupdate_transform
     | idx :: indices' => ProperAttributeToBag
                            _ _ _
                            (NestedTreeFromAttributesAsBag heading _ bupdate_transform indices') idx
   end.

 Definition IndexedTreeUpdateTermType heading :=
   @Tuple heading -> @Tuple heading.

 Definition IndexedTreebupdate_transform heading
 (upd : IndexedTreeUpdateTermType heading)
 (tup : @Tuple heading)
 : @Tuple heading := upd tup.

Instance NestedTreeFromAttributesAsBag'
         {heading}
         (indices : list (@ProperAttribute heading))
: Bag (NestedTreeFromAttributes indices)
      (@Tuple heading)
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
           (TBagAsBag : Bag TBag (@Tuple heading) TSearchTerm TUpdateTerm)
           (pattr : @ProperAttribute heading)
: (@Tuple heading -> ProperAttributeToFMapKey pattr)
  -> ProperAttributeToFMap pattr TBag -> Prop  :=
  match pattr as pattr' return
        (@Tuple heading -> ProperAttributeToFMapKey pattr')
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
: @Tuple heading -> ProperAttributeToFMapKey pattr :=
  match pattr as pattr' return
        @Tuple heading -> ProperAttributeToFMapKey pattr' with
    | {| Attribute := attr; ProperlyTyped := inleft (inleft (left cast')) |}
      => fun x => cast cast' (x attr)
    | {| Attribute := attr; ProperlyTyped := inleft (inleft (right cast')) |}
      => fun x => cast cast' (x attr)
    | {| Attribute := attr; ProperlyTyped := inleft (inright cast') |}
      => fun x => cast cast' (x attr)
    | {| Attribute := attr; ProperlyTyped := inright cast' |}
      => fun x => cast cast' (x attr)
  end.

Definition ProperAttributeToValidUpdate
           {heading}
           TBag TSearchTerm TUpdateTerm
           (ValidUpdate : TUpdateTerm -> Prop)
           (TBagAsBag : Bag TBag (@Tuple heading) TSearchTerm TUpdateTerm)
           (pattr : @ProperAttribute heading)
: (@Tuple heading -> ProperAttributeToFMapKey pattr)
  -> TUpdateTerm -> Prop  :=
  match pattr as pattr' return
        (@Tuple heading -> ProperAttributeToFMapKey pattr')
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
           (TBagAsBag : Bag TBag (@Tuple heading) TSearchTerm TUpdateTerm)
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
                                         (fun x => cast cast' (x attr))
    | {| Attribute := attr; ProperlyTyped := inleft (inleft (right cast')) |}
      => ZTreeBag.IndexedBagAsCorrectBag TBagAsBag RepInv ValidUpdate TBagAsCorrectBag
                                         (fun x => cast cast' (x attr))
    | {| Attribute := attr; ProperlyTyped := inleft (inright cast') |}
      => NatTreeBag.IndexedBagAsCorrectBag TBagAsBag RepInv ValidUpdate TBagAsCorrectBag
                                         (fun x => cast cast' (x attr))
    | {| Attribute := attr; ProperlyTyped := inright cast' |}
      => StringTreeBag.IndexedBagAsCorrectBag TBagAsBag RepInv ValidUpdate TBagAsCorrectBag
                                         (fun x => cast cast' (x attr))
  end.

 Fixpoint ProperAttributesToRepInv
          {heading}
          TUpdateTerm
          (bupdate_transform : TUpdateTerm -> @Tuple heading -> @Tuple heading)
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
          (bupdate_transform : TUpdateTerm -> @Tuple heading -> @Tuple heading)
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
         (bupdate_transform : TUpdateTerm -> @Tuple heading -> @Tuple heading)
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
         (bupdate_transform' : TUpdateTerm -> @Tuple heading -> @Tuple heading)
         (indices : list (@ProperAttribute heading)),
    bupdate_transform
      (Bag := NestedTreeFromAttributesAsBag _ _ bupdate_transform' indices) =
    bupdate_transform'.
Proof.
  induction indices; simpl; eauto.
  destruct a as [attr [[[s | s] | s] | s ]]; simpl in *; eauto.
Qed.

Lemma KeyPreservingUpdateFAsUpdateTermOK {heading}
: forall (indices indices' : list (@ProperAttribute heading))
         (f : @Tuple heading -> @Tuple heading),
    (forall a, List.In a indices -> List.In a indices')
    -> (forall K tup,
          List.In K indices'
          -> f tup (@Attribute _ K) = tup (@Attribute _ K))
    -> ProperAttributesToValidUpdate (@Tuple heading -> @Tuple heading)
                                     (fun upd tup => upd tup)
                                     indices f.
Proof.
  induction indices; simpl; intuition.
  - unfold CountingList_ValidUpdate; auto.
  - destruct a as [attr [[[s | s] | s] | s ]]; simpl in *.
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
                                            (@Tuple heading -> @Tuple heading)
                                            (fun upd tup => upd tup)
                                            indices)
  := NestedTreeFromAttributesAsCorrectBag heading _ _ _ .

Definition NestedTreeFromAttributesAsCorrectBagPlusProof
           {heading}
           (indices : list (@ProperAttribute heading))
: BagPlusProof (@Tuple heading) :=
  {| CorrectBagPlus := (NestedTreeFromAttributesAsCorrectBag_UpdateF indices) |}.

Definition CheckType {heading} (attr: Attributes heading) (rightT: _) :=
  {| Attribute := attr; ProperlyTyped := rightT |}.

Require Import ADTSynthesis.QueryStructure.QueryStructureNotations ADTSynthesis.QueryStructure.Refinements.ListImplementation.
Require Import ADTSynthesis.QueryStructure.AdditionalLemmas ADTSynthesis.QueryStructure.AdditionalPermutationLemmas Coq.Arith.Arith.

(* An equivalence relation between Ensembles of Tuples and Bags
   which incorporates the bag's representation invariant. *)

Definition EnsembleBagEquivalence
           {heading : Heading}
           (bagplus : BagPlusProof (@Tuple heading))
           (ens : Ensemble (@IndexedTuple heading))
           (store : BagTypePlus bagplus)
: Prop :=
  ens ≃ benumerate (Bag := BagPlus bagplus) store /\
  RepInvPlus bagplus store.

Instance EnsembleIndexedTreeEquivalence_AbsR
           {heading : Heading}
           {bagplus : BagPlusProof (@Tuple heading)}
: @UnConstrRelationAbsRClass (@IndexedTuple heading) (BagTypePlus bagplus) :=
  {| UnConstrRelationAbsR := EnsembleBagEquivalence bagplus |}.

(* We now prove that [empty] is a valid abstraction of the
   empty database. *)

Lemma bempty_correct_DB :
  forall {TContainer TSearchTerm TUpdateTerm : Type}
         {db_schema : QueryStructureSchema}
         {index : BoundedString}
         {store_is_bag : Bag TContainer Tuple TSearchTerm TUpdateTerm}
         (RepInv : TContainer -> Prop)
         (ValidUpdate : TUpdateTerm -> Prop),
    CorrectBag RepInv ValidUpdate store_is_bag
    -> EnsembleIndexedListEquivalence
      (GetUnConstrRelation (DropQSConstraints (QSEmptySpec db_schema)) index)
      (benumerate bempty).
Proof.
  intros.
  erewrite benumerate_empty_eq_nil by eauto.
  apply EnsembleIndexedListEquivalence_Empty.
Qed.

Corollary bemptyPlus_correct_DB :
  forall {db_schema : QueryStructureSchema}
         {index : BoundedString}
         {bag_plus : BagPlusProof (@Tuple (@QSGetNRelSchemaHeading db_schema index))},
    GetUnConstrRelation (DropQSConstraints (QSEmptySpec db_schema)) index ≃
                        bempty (Bag := BagPlus bag_plus).
Proof.
  destruct bag_plus; intros; simpl; constructor.
  eapply bempty_correct_DB; eauto.
  apply bempty_RepInv.
Qed.

(* We now prove that [binsert] is a valid abstraction of the
   adding a tuple to the ensemble modeling the database. *)

Require Import ADTSynthesis.QueryStructure.Refinements.OperationRefinements.

Lemma binsert_correct_DB
      db_schema qs index
      (bag_plus : BagPlusProof (@Tuple (@QSGetNRelSchemaHeading db_schema index)))
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

  destruct store_eqv as (indices & [ l' (map & nodup & equiv) ]); eauto.


  (* destruct store_eqv as (indices & [ l' (map & nodup & equiv) ]); eauto. *)

  destruct (permutation_map_cons indexedElement (binsert_enumerate tuple store store_WF)
                                 {| elementIndex := bound;
                                    indexedElement := tuple |} l' eq_refl map)
    as [ l'0 (map' & perm) ].

  exists l'0.
  split; [ assumption | split ].

  eexists; split; try apply perm.

  constructor;
    [ rewrite <- equiv; intro abs; apply H in abs;
      simpl in abs; omega | assumption ].

  setoid_rewrite perm.
  setoid_rewrite equiv.
  setoid_rewrite eq_sym_iff at 1.
  reflexivity.
Qed.

Corollary binsertPlus_correct_DB :
  forall {db_schema : QueryStructureSchema}
         qs
         (index : BoundedString)
         (bag_plus : BagPlusProof (@Tuple (@QSGetNRelSchemaHeading db_schema index)))
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
             (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
             bag_plus
             bag
             (equiv_bag : EnsembleBagEquivalence bag_plus (GetUnConstrRelation qs Ridx) bag)
             (DT : Ensemble Tuple)
             (DT_Dec : DecideableEnsemble DT)
             search_term,
        ExtensionalEq (@dec _ _ DT_Dec)
                              (bfind_matcher (Bag := BagPlus bag_plus) search_term)
             -> refine {x | QSDeletedTuples qs Ridx DT x}
                       (ret (fst (bdelete bag search_term))).
    Proof.
      intros; setoid_rewrite DeletedTuplesFor; auto.
      destruct equiv_bag as [[[bound ValidBound] [l [eq_bag [NoDup_l equiv_l]]]] RepInv_bag];
        subst.
      rewrite refine_List_Query_In by repeat (econstructor; intuition eauto).
      rewrite refine_List_Query_In_Where, refine_List_For_Query_In_Return_Permutation,
      (filter_by_equiv _ _ H), map_id, <- partition_filter_eq.
      rewrite refine_pick_val.
      reflexivity.
      destruct (bdelete_correct bag search_term RepInv_bag) as [_ Perm_bdelete].
      unfold BagPlusProofAsBag, QSGetNRelSchemaHeading, GetNRelSchemaHeading,
      GetNRelSchema in *.
        rewrite Perm_bdelete, eq_bag; reflexivity.
    Qed.

    Lemma bdelete_correct_DB_snd
          db_schema qs index
          (bag_plus : BagPlusProof (@Tuple (@QSGetNRelSchemaHeading db_schema index)))
    :  forall (store: BagTypePlus bag_plus),
         GetUnConstrRelation qs index ≃ store
         -> forall (DeletedTuples : Ensemble (@Tuple (@QSGetNRelSchemaHeading db_schema index)))
                   (DT_Dec : DecideableEnsemble DeletedTuples),
              EnsembleIndexedListEquivalence
                (GetUnConstrRelation
                   (@UpdateUnConstrRelation db_schema qs index
                                            (EnsembleDelete (GetUnConstrRelation qs index)
                                                            DeletedTuples)) index)
                (snd (List.partition (@dec _ _ DT_Dec)
                                     (benumerate store))).
    Proof.
      simpl; unfold EnsembleDelete, EnsembleBagEquivalence, Ensembles.In, Complement; simpl;
      unfold EnsembleIndexedListEquivalence, UnIndexedEnsembleListEquivalence,
      EnsembleListEquivalence; intros; intuition; destruct_ex; intuition; subst.
      repeat setoid_rewrite get_update_unconstr_eq; simpl; intros.
      exists x0.
      unfold UnConstrFreshIdx in *; intros; apply H; destruct H3; eauto.
      exists (snd (partition (@dec IndexedTuple (fun t => DeletedTuples (indexedElement t)) _ ) x)); intuition.
      - unfold BagPlusProofAsBag; rewrite <- H2.
        repeat rewrite partition_filter_neq.
        clear; induction x; simpl; eauto.
        unfold indexedTuple in *;
        find_if_inside; simpl; eauto; rewrite <- IHx; reflexivity.
      - revert H0; clear; induction x; simpl; eauto.
        intros; inversion H0; subst.
        case_eq (partition (fun x0 => @dec IndexedTuple (fun t => DeletedTuples (indexedElement t)) _ x0) x); intros; simpl in *; rewrite H.
        rewrite H in IHx; apply IHx in H3;
        case_eq (@dec IndexedTuple (fun t => DeletedTuples (indexedElement t)) _ a);
        intros; simpl in *; rewrite H1; simpl; eauto.
        constructor; eauto.
        unfold not; intros; apply H2; eapply In_partition with
        (f := fun x0 : IndexedTuple => @dec IndexedTuple (fun t => DeletedTuples (indexedElement t)) _ x0).
        simpl in *; rewrite H; eauto.
      - rewrite get_update_unconstr_eq in H3.
        destruct H3; unfold Ensembles.In in *.
        apply H4 in H3; eapply In_partition in H3; intuition; try apply H6.
        apply In_partition_matched in H6; apply dec_decides_P in H6; exfalso; eauto.
      - rewrite get_update_unconstr_eq; constructor.
        eapply H4; eapply In_partition; eauto.
        unfold Ensembles.In; intros.
        apply In_partition_unmatched in H3.
        simpl in *; apply dec_decides_P in H5.
        unfold indexedTuple, QSGetNRelSchemaHeading, GetNRelSchemaHeading, GetNRelSchema in *;
          rewrite H3 in H5; congruence.
    Qed.

    Require Import ADTSynthesis.QueryStructure.Refinements.AdditionalMorphisms.

    Lemma bdeletePlus_correct_DB_snd
          db_schema qs index
          bag_plus
    :  forall (store: BagTypePlus bag_plus),
         EnsembleBagEquivalence bag_plus (GetUnConstrRelation qs index) store
         -> forall (DeletedTuples : Ensemble (@Tuple (@QSGetNRelSchemaHeading db_schema index)))
                   (DT_Dec : DecideableEnsemble DeletedTuples)
                   search_term,
              ExtensionalEq (@dec _ _ DT_Dec)
                            (bfind_matcher (Bag := BagPlus bag_plus) search_term)
              -> EnsembleBagEquivalence
                   bag_plus
                   (GetUnConstrRelation
                      (@UpdateUnConstrRelation db_schema qs index
                                               (EnsembleDelete (GetUnConstrRelation qs index)
                                                               DeletedTuples)) index)
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
      remember (GetUnConstrRelation qs index).
      generalize DeletedTuples DT_Dec x0 u H1 H0 H3 H7; clear.
      induction (benumerate (snd (bdelete store search_term))); intros.
      eexists []; simpl; intuition.
      constructor.
      destruct H; destruct H2; unfold Ensembles.In in *.
      apply H7 in H.
      apply Permutation_nil in H1.
      apply dec_decides_P; rewrite H0.
      revert H1 H; clear; induction x0; simpl; eauto.
      case_eq (bfind_matcher (Bag := BagPlus bag_plus) search_term (indexedElement a)); simpl; intros.
      intuition; subst; eauto.
      discriminate.
      assert (exists a',
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
        repeat rewrite filter_map; generalize x H2 H3; clear;
        induction x0; intros; simpl in *|-; intuition; subst; eauto.
        inversion H3; subst; exists x0; intuition.
        inversion H3; subst.
        destruct (IHx0 _ H H4); intuition; eexists (a :: x1).
        rewrite H1; intuition.
        constructor.
        simpl in H0; intuition; subst; eauto.
      }
      destruct_ex; intuition; subst.
      rewrite filter_map in H1; rewrite H in H1; simpl in *.
      rewrite H8 in *; simpl in *.
      destruct (IHl DeletedTuples DT_Dec x1
                    (fun tup => Ensembles.In _ u tup /\ tup <> x)); eauto;
      clear IHl.
      rewrite filter_map; eapply Permutation_cons_inv; eauto.
      apply NoDup_Permutation_rewrite in H; eauto.
      inversion H; eauto.
      intuition; intros.
      destruct H2; apply H7 in H2.
      eapply Permutation_in in H; eauto.
      simpl in *; intuition.
      constructor.
      eapply H7.
      symmetry in H; eapply Permutation_in; eauto.
      simpl; eauto.
      intros; subst.
      apply NoDup_Permutation_rewrite in H; eauto.
      eexists (x :: x2); intuition.
      simpl; congruence.
      constructor; eauto.
      unfold not; intros.
      unfold Ensembles.In in *.
      apply H10 in H9; inversion H9; subst; unfold Ensembles.In in *;
      intuition.
      unfold Ensembles.In in H9; inversion H9; subst; unfold Ensembles.In in *;
      intuition.
      generalize (Permutation_in _ H (proj1 (H7 _) H11)); intros In_x0.
      destruct In_x0; simpl; subst; eauto.
      right.
      apply H10; constructor; unfold Ensembles.In; intuition eauto.
      subst; eauto.
      constructor; intros.
      apply H7.
      simpl in *; intuition; subst; eauto.
      apply H10 in H11; unfold Ensembles.In in *; inversion H11;
      unfold Ensembles.In in *; subst; intuition eauto.
      apply H7; eauto.
      unfold Ensembles.In.
      simpl in *; intuition; subst; eauto.
      apply dec_decides_P in H11; rewrite H0 in H11;
      unfold BagPlusProofAsBag, QSGetNRelSchemaHeading,
      GetNRelSchemaHeading, GetNRelSchema in *; simpl in *;
      congruence.
      apply H10 in H12; unfold List.In in *; inversion H12;
      unfold List.In in *; subst; intuition eauto.
    Qed.

    Arguments bdelete : simpl never.
