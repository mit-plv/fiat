Require Export BagsInterface CountingListBags TreeBags Tuple Heading List Program ilist.
Require Import String_as_OT EnsembleListEquivalence.
Require Import Bool String OrderedTypeEx.

Unset Implicit Arguments.

Require Import GeneralQueryRefinements.

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

Require Import FMapAVL.

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
          In K indices'
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

Ltac autoconvert func :=
  match goal with
    | [ src := cons ?head ?tail |- list _ ] =>
      refine (func head _ :: _);
        [ solve [ eauto with * ] | clear src;
                            set (src := tail);
                            autoconvert func ]
    | [ src := nil |- list _ ] => apply []
    | _ => idtac
  end.

(* [mkIndex] builds a [BagPlusProof] record packaging an indexed
   with all its operations and proofs of correctness. *)
Ltac mkIndex heading attributes :=
  set (src := attributes);
  assert (list (@ProperAttribute heading)) as decorated_source by autoconvert (@CheckType heading);
  apply (@NestedTreeFromAttributesAsCorrectBagPlusProof heading decorated_source).

Require Import QueryStructureNotations ListImplementation.
Require Import AdditionalLemmas AdditionalPermutationLemmas Arith.

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

Require Import OperationRefinements.

Lemma binsert_correct_DB
      db_schema qs index
      (bag_plus : BagPlusProof (@Tuple (@QSGetNRelSchemaHeading db_schema index)))
:  forall (store: BagTypePlus bag_plus),
     GetUnConstrRelation qs index ≃ store
     -> forall tuple,
      EnsembleIndexedListEquivalence
        (GetUnConstrRelation
           (@UpdateUnConstrRelation db_schema qs index
                                   (EnsembleInsert
                                      {| tupleIndex := Datatypes.length (benumerate store);
                                         indexedTuple := tuple |}
                                      (GetUnConstrRelation qs index))) index)
        (benumerate (binsert (Bag := BagPlus bag_plus) store tuple)).
Proof.
  intros * store_eqv; destruct store_eqv as (store_eqv, store_WF).
  unfold EnsembleIndexedTreeEquivalence_AbsR,
  EnsembleBagEquivalence, EnsembleIndexedListEquivalence,
  UnIndexedEnsembleListEquivalence, EnsembleListEquivalence in *.

  setoid_rewrite get_update_unconstr_eq.
  setoid_rewrite in_ensemble_insert_iff.
  setoid_rewrite NoDup_modulo_permutation.
  split; intros.

  erewrite binsert_enumerate_length by eauto with typeclass_instances.
    intuition; subst;
    [ | apply lt_S];
    intuition.

  destruct store_eqv as (indices & [ l' (map & nodup & equiv) ]); eauto.

  destruct store_eqv as (indices & [ l' (map & nodup & equiv) ]); eauto.

  destruct (permutation_map_cons indexedTuple (binsert_enumerate tuple store store_WF)
                                 {| tupleIndex := Datatypes.length (benumerate store);
                                    indexedTuple := tuple |} l' eq_refl map)
    as [ l'0 (map' & perm) ].

  exists l'0.
  split; [ assumption | split ].

  eexists; split; try apply perm.

  constructor;
    [ rewrite <- equiv; intro abs;
      apply indices in abs; simpl in abs;
      eapply lt_refl_False; eauto | assumption ].

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
    -> forall tuple,
    GetUnConstrRelation
       (@UpdateUnConstrRelation db_schema qs index
                                (EnsembleInsert
                                   {| tupleIndex := Datatypes.length (benumerate store);
                                      indexedTuple := tuple |}
                                   (GetUnConstrRelation qs index))) index
      ≃ binsert (Bag := BagPlus bag_plus) store tuple.
Proof.
  simpl; intros; constructor.
  - eapply binsert_correct_DB; eauto.
  - eapply binsert_RepInv; apply H.
Qed.

Ltac binsert_correct_DB :=
  match goal with
    | [ H: EnsembleBagEquivalence ?bag_plus
                                  (GetUnConstrRelation ?qs ?index)
                                  ?store |- _ ] =>
      solve [ simpl; apply (binsertPlus_correct_DB qs index bag_plus store H) ]
  end.
