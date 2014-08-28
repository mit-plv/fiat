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
         (bid : TUpdateTerm)
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
     | [] => CountingListAsBag bid bupdate_transform
     | idx :: indices' => ProperAttributeToBag 
                            _ _ _ 
                            (NestedTreeFromAttributesAsBag heading _ bid bupdate_transform indices') idx
   end.

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
          (bid : TUpdateTerm)
          (bupdate_transform : TUpdateTerm -> @Tuple heading -> @Tuple heading)
          (indices : list (@ProperAttribute heading))
 : NestedTreeFromAttributes indices -> Prop :=
   match indices return NestedTreeFromAttributes indices -> Prop with
     | [] => CountingList_RepInv
     | idx :: indices' => 
       ProperAttributeToRepInv _ _ TUpdateTerm
         (ProperAttributesToRepInv TUpdateTerm bid bupdate_transform indices')
         (NestedTreeFromAttributesAsBag heading TUpdateTerm bid bupdate_transform indices') idx
         (ProperAttributeToProjection idx)
   end.

 Fixpoint ProperAttributesToValidUpdate
          {heading}
          TUpdateTerm
          (bid : TUpdateTerm)
          (bupdate_transform : TUpdateTerm -> @Tuple heading -> @Tuple heading)
          (indices : list (@ProperAttribute heading))
 : TUpdateTerm -> Prop :=
   match indices return TUpdateTerm -> Prop with
     | [] => CountingList_ValidUpdate
     | idx :: indices' => 
       ProperAttributeToValidUpdate _ _ TUpdateTerm
         (ProperAttributesToValidUpdate TUpdateTerm bid bupdate_transform indices')
         (NestedTreeFromAttributesAsBag heading TUpdateTerm bid bupdate_transform indices') idx
         (ProperAttributeToProjection idx)
   end.

 Program Fixpoint NestedTreeFromAttributesAsCorrectBag
         heading
         TUpdateTerm
         (bid : TUpdateTerm)
         (bupdate_transform : TUpdateTerm -> @Tuple heading -> @Tuple heading)
         (indices : list (@ProperAttribute heading))
 : CorrectBag (ProperAttributesToRepInv TUpdateTerm bid bupdate_transform indices)
              (ProperAttributesToValidUpdate TUpdateTerm bid bupdate_transform indices)
              (NestedTreeFromAttributesAsBag heading TUpdateTerm
                                             bid bupdate_transform indices) :=
   match indices return 
         CorrectBag (ProperAttributesToRepInv TUpdateTerm bid bupdate_transform indices)
                    (ProperAttributesToValidUpdate TUpdateTerm bid bupdate_transform indices)
                    (NestedTreeFromAttributesAsBag heading TUpdateTerm
                                   bid bupdate_transform indices) with
     | [] => CountingListAsCorrectBag bid bupdate_transform
     | idx :: indices' => 
       ProperAttributeToCorrectBag
         _ _ _ 
         (NestedTreeFromAttributesAsBag heading TUpdateTerm bid bupdate_transform indices')
         (ProperAttributesToRepInv TUpdateTerm bid bupdate_transform indices')
         (ProperAttributesToValidUpdate TUpdateTerm bid bupdate_transform indices')
         (NestedTreeFromAttributesAsCorrectBag heading TUpdateTerm bid bupdate_transform
                                                 indices')
           idx
   end.

Lemma bupdate_transform_NestedTree : 
  forall heading
         TUpdateTerm
         (bid : TUpdateTerm)
         (bupdate_transform' : TUpdateTerm -> @Tuple heading -> @Tuple heading)
         (indices : list (@ProperAttribute heading)),
    bupdate_transform
      (Bag := NestedTreeFromAttributesAsBag _ _ bid bupdate_transform' indices) = 
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
                                     (id)
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

Definition NestedTreeFromAttributesAsCorrectBag_UpdateF
          {heading}
          (indices : list (@ProperAttribute heading))
: CorrectBag (ProperAttributesToRepInv _ _ _ indices)
             (ProperAttributesToValidUpdate _ _ _ indices)
             (NestedTreeFromAttributesAsBag heading 
                                            (@Tuple heading -> @Tuple heading)
                                            id
                                            (fun upd tup => upd tup)
                                            indices)
  := NestedTreeFromAttributesAsCorrectBag heading _ _ _ _.

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

Ltac mkIndex heading attributes :=
  set (src := attributes);
  assert (list (@ProperAttribute heading)) as decorated_source by autoconvert (@CheckType heading);
  apply (ProperAttributeToFMap heading decorated_source).

Require Import QueryStructureNotations ListImplementation.
Require Import AdditionalLemmas AdditionalPermutationLemmas Arith.

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

Lemma binsert_correct_DB {TContainer TSearchTerm TUpdateTerm} 
      (RepInv : TContainer -> Prop)
      (ValidUpdate : TUpdateTerm -> Prop):
  forall db_schema qs index (store: TContainer)
         {store_is_bag: Bag TContainer _ TSearchTerm TUpdateTerm}
         (bag_is_valid : CorrectBag RepInv ValidUpdate store_is_bag)
         (store_is_valid : RepInv store),
    EnsembleIndexedListEquivalence
      (GetUnConstrRelation qs index)
      (benumerate (Bag := store_is_bag) store) ->
    forall tuple,
      EnsembleIndexedListEquivalence
        (GetUnConstrRelation
           (@UpdateUnConstrRelation db_schema qs index
                                   (EnsembleInsert
                                      {| tupleIndex := Datatypes.length (benumerate store);
                                         indexedTuple := tuple |}
                                      (GetUnConstrRelation qs index))) index)
        (benumerate (binsert (Bag := store_is_bag) store tuple)).
Proof.
  intros.
  unfold EnsembleIndexedListEquivalence, UnIndexedEnsembleListEquivalence, EnsembleListEquivalence in *.

  setoid_rewrite get_update_unconstr_eq.
  setoid_rewrite in_ensemble_insert_iff.
  setoid_rewrite NoDup_modulo_permutation.
  split; intros.

  erewrite binsert_enumerate_length by eauto;
    destruct H0; subst;
    [ | apply lt_S];
    intuition.

  destruct H as (indices & [ l' (map & nodup & equiv) ]).

  destruct (permutation_map_cons indexedTuple (binsert_enumerate tuple store store_is_valid)
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
(*
Ltac binsert_correct_DB :=
  match goal with
    | [ H: EnsembleIndexedListEquivalence (GetUnConstrRelation ?qs ?index)
                                          (benumerate (Bag := ?bagproof) ?store) |- _ ] =>
      solve [ simpl; apply (binsert_correct_DB (store_is_bag := bagproof) _ qs index _ H) ]
  end. *)
