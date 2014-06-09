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

Definition HasDecidableEquality (T: Type) :=
  forall (x y: T), {x = y} + {x <> y}.

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

Require Import FMapAVL.

Module NatIndexedMap := FMapAVL.Make Nat_as_OT.
Module StringIndexedMap := FMapAVL.Make String_as_OT.

Module NatTreeBag := TreeBag NatIndexedMap.
Module StringTreeBag := TreeBag StringIndexedMap.

Definition NatTreeType TSubtree TSubtreeSearchTerm heading subtree_as_bag := 
  (@NatTreeBag.IndexedBag 
     TSubtree 
     (@Tuple heading) 
     TSubtreeSearchTerm 
     subtree_as_bag).

Definition StringTreeType TSubtree TSubtreeSearchTerm heading subtree_as_bag := 
  (@StringTreeBag.IndexedBag 
     TSubtree 
     (@Tuple heading) 
     TSubtreeSearchTerm
     subtree_as_bag).

Definition cast {T1 T2: Type} (eq: T1 = T2) (x: T1) : T2.
Proof.
  subst; auto.
Defined.

Record ProperAttribute {heading} :=
  {
    Attribute: Attributes heading; 
    ProperlyTyped: { Domain heading Attribute = nat } + { Domain heading Attribute = string }
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
      match (@ProperlyTyped heading proper_attr) with
        | left  eq_nat    => 
          {| BagType        := NatTreeType    t st heading bagproof (fun x => cast eq_nat    (x attr));
             SearchTermType := option nat    * st |}
        | right eq_string => 
          {| BagType        := StringTreeType t st heading bagproof (fun x => cast eq_string (x attr));
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




(* Example use:
Require Import Beatles.

Definition SampleIndex : @BagPlusBagProof (@Tuple AlbumHeading).
Proof.
  mkIndex AlbumHeading [Year; UKpeak; Name].
Defined.

Definition IndexedAlbums :=
  List.fold_left binsert FirstAlbums (@bempty _ _ _ (BagProof SampleIndex)).

Eval simpl in (SearchTermType SampleIndex).
Time Eval simpl in (bfind IndexedAlbums (Some 3, (None, (None, [])))).
Time Eval simpl in (bfind IndexedAlbums (Some 3, (Some 1, (None, [])))).
Time Eval simpl in (bfind IndexedAlbums (Some 3, (Some 1, (Some "With the Beatles", [])))).
Time Eval simpl in (bfind IndexedAlbums (None, (None, (Some "With the Beatles", [])))).
Time Eval simpl in (bfind IndexedAlbums (None, (None, (None, [TupleEqualityMatcher (eq_dec := string_dec) Name "With the Beatles"])))).

(*Time Eval simpl in (@bfind _ _ _ (BagProof _ SampleIndex) IndexedAlbums (Some 3, (Some 1, (None, @nil (TSearchTermMatcher AlbumHeading))))).*)
*)

Require Import EnsembleListEquivalence QueryStructure InsertQSSpecs AdditionalLemmas.

Lemma binsert_correct_DB {TContainer TSearchTerm} :
  forall db_schema qs index (store: TContainer),
  forall {store_is_bag: Bag TContainer _ TSearchTerm},
    EnsembleListEquivalence 
      (GetUnConstrRelation qs index) 
      (benumerate store) ->
    forall tuple,
      EnsembleListEquivalence 
        (GetUnConstrRelation
           (UpdateUnConstrRelation db_schema qs index 
                                   (RelationInsert tuple (GetUnConstrRelation qs index))) index)
        (benumerate (binsert store tuple)).
Proof.
  intros * equiv **;
                 apply (ensemble_list_equivalence_set_eq_morphism get_update_unconstr_iff);
  unfold RelationInsert, EnsembleListEquivalence, Ensembles.In in *;
  setoid_rewrite (@binsert_enumerate _ _ _ store_is_bag _);
  setoid_rewrite <- equiv;
  tauto.
Qed.
