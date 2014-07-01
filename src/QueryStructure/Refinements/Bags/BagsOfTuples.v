Require Export BagsInterface ListBags TreeBags Tuple Heading List Program.
Require Import String_as_OT EnsembleListEquivalence.
Require Import Bool String OrderedTypeEx.

Unset Implicit Arguments.

Definition TSearchTermMatcher (heading: Heading) := (@Tuple heading -> bool).

Definition SearchTermsCollection heading :=
  list (TSearchTermMatcher heading).

Fixpoint MatchAgainstSearchTerms
         {heading: Heading}
         (search_terms : SearchTermsCollection heading) (item: Tuple) :=
  match search_terms with
    | []                     => true
    | is_match :: more_terms => (is_match item) && MatchAgainstSearchTerms more_terms item
  end.

Require Import GeneralQueryRefinements.

Definition TupleEqualityMatcher
           {heading: Heading}
           (attr: Attributes heading)
           (value: Domain heading attr)
           {ens_dec: DecideableEnsemble (fun x : Domain heading attr => value = x)} 
: TSearchTermMatcher heading := fun tuple => dec (tuple attr).

Definition TupleDisequalityMatcher
           {heading: Heading}
           (attr: Attributes heading)
           (value: Domain heading attr)
           {ens_dec: DecideableEnsemble (fun x : Domain heading attr => value = x)} 
: TSearchTermMatcher heading := fun tuple => negb (dec (tuple attr)).

Instance TupleListAsBag (heading: Heading) :
  Bag (list (@Tuple heading)) (@Tuple heading) (SearchTermsCollection heading).
Proof.
  apply (ListAsBag [] (@MatchAgainstSearchTerms heading)); eauto.
Defined.

Definition TupleListBag {heading} :=
  {|
    BagType        := list (@Tuple heading);
    SearchTermType := (SearchTermsCollection heading)
  |}.

Require Import FMapAVL.

Module NIndexedMap := FMapAVL.Make N_as_OT.
Module ZIndexedMap := FMapAVL.Make Z_as_OT.
Module NatIndexedMap := FMapAVL.Make Nat_as_OT.
Module StringIndexedMap := FMapAVL.Make String_as_OT.

Module NTreeBag := TreeBag NIndexedMap.
Module ZTreeBag := TreeBag ZIndexedMap.
Module NatTreeBag := TreeBag NatIndexedMap.
Module StringTreeBag := TreeBag StringIndexedMap.

Definition TTreeConstructor (TKey: Type) :=
  forall TBag TItem TBagSearchTerm : Type,
    Bag TBag TItem TBagSearchTerm -> (TItem -> TKey) -> Type.

Definition mkTreeType
           (TKey: Type)
           (tree_constructor: TTreeConstructor TKey)
           TSubtree TSubtreeSearchTerm
           heading subtree_as_bag : (@Tuple heading -> TKey) -> Type :=
  tree_constructor TSubtree (@Tuple heading) TSubtreeSearchTerm subtree_as_bag.

Definition NTreeType      := mkTreeType BinNums.N (@NTreeBag.IndexedBag).
Definition ZTreeType      := mkTreeType BinNums.Z (@ZTreeBag.IndexedBag).
Definition NatTreeType    := mkTreeType nat       (@NatTreeBag.IndexedBag).
Definition StringTreeType := mkTreeType string    (@StringTreeBag.IndexedBag).

Definition cast {T1 T2: Type} (eq: T1 = T2) (x: T1) : T2.
Proof.
  subst; auto.
Defined.

Record ProperAttribute {heading} :=
  {
    Attribute: Attributes heading;
    ProperlyTyped: { Domain heading Attribute = BinNums.N } + { Domain heading Attribute = BinNums.Z } +
                   { Domain heading Attribute = nat } + { Domain heading Attribute = string }
  }.

Fixpoint NestedTreeFromAttributes'
         heading
         (indexes: list (@ProperAttribute heading))
         {struct indexes}: (@BagPlusBagProof (@Tuple heading)) :=
  match indexes with
    | [] =>
      {| BagType        := list (@Tuple heading);
         SearchTermType := SearchTermsCollection heading |}
    | proper_attr :: more_indexes =>
      let attr := @Attribute heading proper_attr in
      let (t, st, bagproof) := NestedTreeFromAttributes' heading more_indexes in
      match ProperlyTyped proper_attr with
        | inleft (inleft (left conv))  =>
          {| BagType        := NTreeType t st heading bagproof (fun x => cast conv (x attr));
             SearchTermType := option BinNums.N * st |}
        | inleft (inleft (right conv)) =>
          {| BagType        := ZTreeType t st heading bagproof (fun x => cast conv (x attr));
             SearchTermType := option BinNums.Z * st |}
        | inleft (inright conv)        =>
          {| BagType        := NatTreeType t st heading bagproof (fun x => cast conv (x attr));
             SearchTermType := option nat * st |}
        | inright conv                 =>
          {| BagType        := StringTreeType t st heading bagproof (fun x => cast conv (x attr));
             SearchTermType := option string * st |}
      end
  end.

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
  apply (NestedTreeFromAttributes' heading decorated_source).

Require Import QueryStructureNotations ListImplementation.
Require Import AdditionalLemmas AdditionalPermutationLemmas Arith.

Lemma bempty_correct_DB :
  forall {TContainer TSearchTerm : Type} {db_schema : QueryStructureSchema}
         {index : BoundedString} {store_is_bag : Bag TContainer Tuple TSearchTerm},
    EnsembleIndexedListEquivalence
      (GetUnConstrRelation (DropQSConstraints (QSEmptySpec db_schema)) index)
      (benumerate bempty).
Proof.
  intros.
  rewrite benumerate_empty_eq_nil.
  apply EnsembleIndexedListEquivalence_Empty.
Qed.

Lemma binsert_correct_DB {TContainer TSearchTerm} :
  forall db_schema qs index (store: TContainer),
  forall {store_is_bag: Bag TContainer _ TSearchTerm},
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

  rewrite binsert_enumerate_length;
    destruct H0; subst;
    [ | apply lt_S];
    intuition.

  destruct H as (indices & [ l' (map & nodup & equiv) ]).

  destruct (permutation_map_cons indexedTuple (binsert_enumerate tuple store)
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

Ltac binsert_correct_DB :=
  match goal with
    | [ H: EnsembleIndexedListEquivalence (GetUnConstrRelation ?qs ?index)
                                          (benumerate (Bag := ?bagproof) ?store) |- _ ] => 
      solve [ simpl; apply (binsert_correct_DB (store_is_bag := bagproof) _ qs index _ H) ]
  end.
