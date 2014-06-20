Require Export Bags Tuple Heading List Program.
Require Import String_as_OT.
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

Definition TupleEqualityMatcher 
           {heading: Heading} 
           (attr: Attributes heading)
           (value: Domain heading attr) 
           {eq_dec: HasDecidableEquality (Domain heading attr)} : TSearchTermMatcher heading :=
  fun tuple => 
    match eq_dec (tuple attr) value with
      | in_left  => true
      | in_right => false
    end.

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

(*
Require Import Beatles.
Local Open Scope string_scope.

Local Open Scope Tuple_scope.

Definition SampleIndex : @BagPlusBagProof (@Tuple AlbumHeading).
Proof.
  mkIndex AlbumHeading [Year; UKpeak; Name].
Defined.

Definition IndexedAlbums :=
  List.fold_left binsert FirstAlbums (@bempty _ _ _ (BagProof SampleIndex)).

(* Example use: 
Eval simpl in (SearchTermType SampleIndex).
Time Eval simpl in (bfind IndexedAlbums (Some 1963%N, (None, (None, [])))).
Time Eval simpl in (bfind IndexedAlbums (Some 1963%N, (Some 1, (None, [])))).
Time Eval simpl in (bfind IndexedAlbums (Some 1963%N, (Some 1, (Some "With the Beatles", [])))).
Time Eval simpl in (bfind IndexedAlbums (None, (None, (Some "With the Beatles", [])))).
Time Eval simpl in (bfind IndexedAlbums (None, (None, (None, [TupleEqualityMatcher (eq_dec := string_dec) Name "With the Beatles"])))).

(*Time Eval simpl in (@bfind _ _ _ (BagProof _ SampleIndex) IndexedAlbums (Some 3, (Some 1, (None, @nil (TSearchTermMatcher AlbumHeading))))).*)
*)
*)

Require Import EnsembleListEquivalence GeneralQueryRefinements ListQueryStructureRefinements QueryStructure InsertQSSpecs AdditionalLemmas AdditionalPermutationLemmas Arith.

Lemma binsert_correct_DB {TContainer TSearchTerm} :
  forall db_schema qs index (store: TContainer),
  forall {store_is_bag: Bag TContainer _ TSearchTerm},
    EnsembleIndexedListEquivalence 
      (GetUnConstrRelation qs index) 
      (benumerate (Bag := store_is_bag) store) ->
    forall tuple,
      EnsembleIndexedListEquivalence 
        (GetUnConstrRelation
           (UpdateUnConstrRelation db_schema qs index 
                                   (EnsembleInsert 
                                      {| tupleIndex := Datatypes.length (benumerate store);
                                         indexedTuple := tuple |} 
                                      (GetUnConstrRelation qs index))) index)
        (benumerate (binsert (Bag := store_is_bag) store tuple)).
Proof.
  intros.
  unfold EnsembleIndexedListEquivalence, UnIndexedEnsembleListEquivalence, EnsembleListEquivalence in *.

  setoid_rewrite get_update_unconstr_iff.
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
