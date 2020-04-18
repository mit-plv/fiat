Require Export Coq.Lists.List Coq.Program.Program
        Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsInterface
        Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsProperties.
Require Import Fiat.Common.List.ListFacts.

Unset Implicit Arguments.

Section CachingBags.
(* This will need to be patched up to work with update and delete. *)
(*  Require Import SetEq.
  Require Import Morphisms.

  Context {TItem : Type}
          {TCachedValue : Type}
          (eqA: TCachedValue -> TCachedValue -> Prop)
          (updater: TItem -> TCachedValue -> TCachedValue)
          (initial_value: TCachedValue).

  Definition RecomputeCachedValue
             (items: list TItem) :=
    List.fold_right updater initial_value items.

  Definition CachedValueIsFresh
             (items: list TItem)
             (cached_value: TCachedValue) :=
    eqA (RecomputeCachedValue items) cached_value.

  Definition IsStronglyCacheable :=
    Proper (@SetEq TItem ==> eqA) RecomputeCachedValue.

  Definition IsCacheable :=
    Proper (@Permutation TItem ==> eqA) RecomputeCachedValue.

  Lemma is_cacheable_proper :
    IsCacheable ->
    Proper (eq ==> eqA ==> eqA) updater.
  Proof.
    unfold Proper, respectful.
    intros * cacheable * is_eq * is_eqA; subst.
    specialize (cacheable [y] [y]).

    simpl in cacheable. apply cacheable; trivial.
  Qed.

  Require Import Permutation.


  Record Cache
         {TBag TItem TSearchTerm TCachedValue: Type}
         {bag_bag: Bag TBag TItem TSearchTerm}
         {initial_value: TCachedValue}
         {eqA: TCachedValue -> TCachedValue -> Prop}
         {updater: TItem -> TCachedValue -> TCachedValue}
         {updater_cacheable: IsCacheable eqA updater} :=
    {
      cbag:          TBag;
      ccached_value: TCachedValue;
      cfresh_cache:  CachedValueIsFresh eqA initial_value updater (benumerate cbag) ccached_value
    }.

  (* Note: The caching interface provides the initial_value
         parameter to allow implementations to gracefully handle empty
         caches. Should an empty/non-empty distinction be needed,
         initial_value can be set to None, and TCachedValue
         replaced by an option type. *)

  Definition extract_cacheability_proof
             {TBag TItem TSearchTerm TCachedValue: Type}
             {bag_bag: Bag TBag TItem TSearchTerm}
             {initial_value: TCachedValue}
             {eqA: TCachedValue -> TCachedValue -> Prop}
             {updater: TItem -> TCachedValue -> TCachedValue}
             {updater_cacheable: IsCacheable eqA updater}
             (cache: @Cache TBag TItem TSearchTerm TCachedValue bag_bag initial_value eqA updater updater_cacheable) :=
    updater_cacheable.

  Lemma empty_caching_bag_fresh:
    forall {TBag TItem TSearchTerm TCachedValue: Type}
           {bag_bag : Bag TBag TItem TSearchTerm}
           (initial_value : TCachedValue)
           {eqA: TCachedValue -> TCachedValue -> Prop}
           {equiv: Equivalence eqA}
           (updater : TItem -> TCachedValue -> TCachedValue)
           (updater_cacheable: IsCacheable eqA updater),
      CachedValueIsFresh eqA initial_value updater (benumerate bempty) initial_value.
  Proof.
    intros; rewrite benumerate_empty_eq_nil; compute; reflexivity.
  Qed.

  Definition Cache_bempty
             {TBag TItem TSearchTerm TCachedValue: Type}
             {bag_bag : Bag TBag TItem TSearchTerm}
             (initial_value : TCachedValue)
             (eqA: TCachedValue -> TCachedValue -> Prop)
             (equiv: Equivalence eqA)
             (updater : TItem -> TCachedValue -> TCachedValue)
             (updater_cacheable: IsCacheable eqA updater) :
    (@Cache _ _ _ _ bag_bag initial_value eqA updater updater_cacheable) :=
    {|
      cbag          := @bempty _ _ _ bag_bag;
      ccached_value := initial_value;
      cfresh_cache  := empty_caching_bag_fresh initial_value
                                               updater updater_cacheable
    |}.

  Definition Cache_bstar
             {TBag TItem TSearchTerm: Type}
             {bag_bag : Bag TBag TItem TSearchTerm} :=
    bstar.

  Definition Cache_bfind_matcher
             {TBag TItem TSearchTerm TCachedValue: Type}
             {bag_bag : Bag TBag TItem TSearchTerm}
             (initial_value : TCachedValue)
             (eqA: TCachedValue -> TCachedValue -> Prop)
             (updater : TItem -> TCachedValue -> TCachedValue)
             (updater_cacheable: IsCacheable eqA updater)
             (search_term: TSearchTerm) (item: TItem) :=
    bfind_matcher search_term item.

  Definition Cache_benumerate
             {TBag TItem TSearchTerm TCachedValue: Type}
             {bag_bag: Bag TBag TItem TSearchTerm}
             (initial_value : TCachedValue)
             (eqA: TCachedValue -> TCachedValue -> Prop)
             (updater : TItem -> TCachedValue -> TCachedValue)
             (updater_cacheable: IsCacheable eqA updater)
             (container: @Cache _ _ _ _ bag_bag initial_value
                                eqA updater updater_cacheable) :=
    benumerate (cbag container).

  Definition Cache_bfind
             {TBag TItem TSearchTerm TCachedValue: Type}
             {bag_bag: Bag TBag TItem TSearchTerm}
             (initial_value : TCachedValue)
             (eqA: TCachedValue -> TCachedValue -> Prop)
             (updater : TItem -> TCachedValue -> TCachedValue)
             (updater_cacheable: IsCacheable eqA updater)
             (container: @Cache _ _ _ _ bag_bag initial_value
                                eqA updater updater_cacheable)
             (search_term: TSearchTerm) :=
    bfind (cbag container) search_term.

  Definition Cache_bcount
             {TBag TItem TSearchTerm TCachedValue: Type}
             {bag_bag: Bag TBag TItem TSearchTerm}
             (initial_value : TCachedValue)
             (eqA: TCachedValue -> TCachedValue -> Prop)
             (updater : TItem -> TCachedValue -> TCachedValue)
             (updater_cacheable: IsCacheable eqA updater)
             (container: @Cache _ _ _ _ bag_bag initial_value
                                eqA updater updater_cacheable)
             (search_term: TSearchTerm) :=
    bcount (cbag container) search_term.

  Lemma updated_cache_fresh_after_insert :
    forall {TBag TItem TSearchTerm TCachedValue: Type}
           {bag_bag: Bag TBag TItem TSearchTerm}
           (initial_value: TCachedValue)
           (eqA: TCachedValue -> TCachedValue -> Prop)
           (equiv: Equivalence eqA)
           (updater: TItem -> TCachedValue -> TCachedValue)
           (updater_cacheable: IsCacheable eqA updater)
           (container: @Cache _ _ _ _ bag_bag initial_value
                              eqA updater updater_cacheable)
           (item: TItem),
      CachedValueIsFresh eqA initial_value updater
                         (benumerate (binsert (cbag container) item))
                         (updater item (ccached_value container)).
  Proof.
    intros;
    unfold CachedValueIsFresh.
    unfold IsCacheable in updater_cacheable.
    rewrite binsert_enumerate.
    pose proof (is_cacheable_proper updater_cacheable).
    pose proof (@cfresh_cache) as fresh; unfold CachedValueIsFresh in fresh;
    simpl; rewrite fresh; reflexivity.
  Qed.

  Definition Cache_binsert
             {TBag TItem TSearchTerm TCachedValue: Type}
             {bag_bag: Bag TBag TItem TSearchTerm}
             (initial_value: TCachedValue)
             (eqA: TCachedValue -> TCachedValue -> Prop)
             (equiv: Equivalence eqA)
             (updater: TItem -> TCachedValue -> TCachedValue)
             (updater_cacheable: IsCacheable eqA updater)
             (container: @Cache TBag TItem TSearchTerm TCachedValue
                                bag_bag initial_value
                                eqA updater updater_cacheable)
             (item: TItem) : @Cache TBag TItem TSearchTerm TCachedValue
                                    bag_bag initial_value
                                    eqA updater updater_cacheable :=
    {|
      cbag          := binsert (Bag := bag_bag) (cbag container) item;
      ccached_value := updater item (ccached_value container);
      cfresh_cache  := updated_cache_fresh_after_insert _ _ _ _ _ _ _
    |}.

  (* We're just going to recompute the cached value in the interest of
   expediency. Future implementations will have more clever ways of
   doing this. *)
  Definition Cache_bdelete
             {TBag TItem TSearchTerm TCachedValue: Type}
             {bag_bag: Bag TBag TItem TSearchTerm}
             (initial_value: TCachedValue)
             (eqA: TCachedValue -> TCachedValue -> Prop)
             (equiv: Equivalence eqA)
             (updater: TItem -> TCachedValue -> TCachedValue)
             (updater_cacheable: IsCacheable eqA updater)
             (container: @Cache TBag TItem TSearchTerm TCachedValue
                                bag_bag initial_value
                                eqA updater updater_cacheable)
             (search_term : TSearchTerm) : @Cache TBag TItem TSearchTerm TCachedValue
                                                  bag_bag initial_value
                                                  eqA updater updater_cacheable :=
    let c := bdelete (Bag := bag_bag) (cbag container) search_term in
    {|
      cbag          := c;
      ccached_value := RecomputeCachedValue updater initial_value (benumerate c);
      cfresh_cache  := reflexivity _
    |}.

  (* We're just going to recompute the cached value in the interest of
   expediency. Future implementations will have more clever ways of
   doing this. *)
  Definition Cache_bupdate
             {TBag TItem TSearchTerm TCachedValue: Type}
             {bag_bag: Bag TBag TItem TSearchTerm}
             (initial_value: TCachedValue)
             (eqA: TCachedValue -> TCachedValue -> Prop)
             (equiv: Equivalence eqA)
             (updater: TItem -> TCachedValue -> TCachedValue)
             (updater_cacheable: IsCacheable eqA updater)
             (container: @Cache TBag TItem TSearchTerm TCachedValue
                                bag_bag initial_value
                                eqA updater updater_cacheable)
             (search_term : TSearchTerm)
             (update_f : TItem -> TItem)
  : @Cache TBag TItem TSearchTerm TCachedValue
           bag_bag initial_value
           eqA updater updater_cacheable :=
    let c := bupdate (Bag := bag_bag) (cbag container) search_term update_f in
    {|
      cbag          := c;
      ccached_value := RecomputeCachedValue updater initial_value (benumerate c);
      cfresh_cache  := reflexivity _
    |}.

  Ltac transparent_implementation :=
    unfold BagInsertEnumerate, BagEnumerateEmpty, BagFindStar,
    BagFindCorrect, BagCountCorrect, BagDeleteCorrect, BagUpdateCorrect;
    intros;
    first [ apply binsert_enumerate | apply benumerate_empty
            | apply bfind_correct | apply bfind_star
            | apply bcount_correct | apply bdelete_correct | apply bupdate_correct ].

  Lemma Cache_BagInsertEnumerate :
    forall {TBag TItem TSearchTerm TCachedValue: Type}
           {bag_bag: Bag TBag TItem TSearchTerm}
           (initial_value: TCachedValue)
           (eqA: TCachedValue -> TCachedValue -> Prop)
           (equiv: Equivalence eqA)
           (updater: TItem -> TCachedValue -> TCachedValue)
           (updater_cacheable: IsCacheable eqA updater),
      BagInsertEnumerate
        (Cache_benumerate initial_value eqA updater updater_cacheable)
        (Cache_binsert    initial_value eqA equiv updater updater_cacheable).
  Proof. transparent_implementation. Qed.

  Lemma Cache_BagEnumerateEmpty :
    forall {TBag TItem TSearchTerm TCachedValue: Type}
           {bag_bag: Bag TBag TItem TSearchTerm}
           (initial_value: TCachedValue)
           (eqA: TCachedValue -> TCachedValue -> Prop)
           (equiv: Equivalence eqA)
           (updater: TItem -> TCachedValue -> TCachedValue)
           (updater_cacheable: IsCacheable eqA updater),
      BagEnumerateEmpty
        (Cache_benumerate initial_value eqA updater updater_cacheable)
        (Cache_bempty     initial_value eqA equiv updater updater_cacheable).
  Proof. transparent_implementation. Qed.

  Lemma Cache_BagFindStar :
    forall {TBag TItem TSearchTerm TCachedValue: Type}
           {bag_bag: Bag TBag TItem TSearchTerm}
           (initial_value: TCachedValue)
           (eqA: TCachedValue -> TCachedValue -> Prop)
           (updater: TItem -> TCachedValue -> TCachedValue)
           (updater_cacheable: IsCacheable eqA updater),
      BagFindStar
        (Cache_bfind      initial_value eqA updater updater_cacheable)
        (Cache_benumerate initial_value eqA updater updater_cacheable)
        Cache_bstar.
  Proof. transparent_implementation. Qed.

  Lemma Cache_BagFindCorrect :
    forall {TBag TItem TSearchTerm TCachedValue: Type}
           {bag_bag: Bag TBag TItem TSearchTerm}
           (initial_value: TCachedValue)
           (eqA: TCachedValue -> TCachedValue -> Prop)
           (updater: TItem -> TCachedValue -> TCachedValue)
           (updater_cacheable: IsCacheable eqA updater),
      BagFindCorrect
        (Cache_bfind         initial_value eqA updater updater_cacheable)
        (Cache_bfind_matcher initial_value eqA updater updater_cacheable)
        (Cache_benumerate    initial_value eqA updater updater_cacheable).
  Proof. transparent_implementation. Qed.

  Lemma Cache_BagCountCorrect :
    forall {TBag TItem TSearchTerm TCachedValue: Type}
           {bag_bag: Bag TBag TItem TSearchTerm}
           (initial_value: TCachedValue)
           (eqA: TCachedValue -> TCachedValue -> Prop)
           (updater: TItem -> TCachedValue -> TCachedValue)
           (updater_cacheable: IsCacheable eqA updater),
      BagCountCorrect
        (Cache_bcount initial_value eqA updater updater_cacheable)
        (Cache_bfind  initial_value eqA updater updater_cacheable).
  Proof. transparent_implementation. Qed.

  Lemma Cache_BagDeleteCorrect :
    forall {TBag TItem TSearchTerm TCachedValue: Type}
           {bag_bag: Bag TBag TItem TSearchTerm}
           (initial_value: TCachedValue)
           (eqA: TCachedValue -> TCachedValue -> Prop)
           (equiv: Equivalence eqA)
           (updater: TItem -> TCachedValue -> TCachedValue)
           (updater_cacheable: IsCacheable eqA updater),
      BagDeleteCorrect (Cache_bfind initial_value eqA updater updater_cacheable)
                       (Cache_bfind_matcher initial_value eqA updater updater_cacheable)
                       (Cache_benumerate initial_value eqA updater updater_cacheable)
                       (Cache_bdelete initial_value eqA equiv updater updater_cacheable).
  Proof. transparent_implementation. Qed.

  Lemma Cache_BagUpdateCorrect :
    forall {TBag TItem TSearchTerm TCachedValue: Type}
           {bag_bag: Bag TBag TItem TSearchTerm}
           (initial_value: TCachedValue)
           (eqA: TCachedValue -> TCachedValue -> Prop)
           (equiv: Equivalence eqA)
           (updater: TItem -> TCachedValue -> TCachedValue)
           (updater_cacheable: IsCacheable eqA updater),
      BagUpdateCorrect (Cache_bfind initial_value eqA updater updater_cacheable)
                       (Cache_bfind_matcher initial_value eqA updater updater_cacheable)
                       (Cache_benumerate initial_value eqA updater updater_cacheable)
                       (Cache_bupdate initial_value eqA equiv updater updater_cacheable).
  Proof. transparent_implementation. Qed.

  Instance CacheAsBag
           {TBag TItem TSearchTerm TCachedValue: Type}
           {bag_bag: Bag TBag TItem TSearchTerm}
           (initial_value: TCachedValue)
           (eqA: TCachedValue -> TCachedValue -> Prop)
           (equiv: Equivalence eqA)
           (updater: TItem -> TCachedValue -> TCachedValue)
           (updater_cacheable: IsCacheable eqA updater)
  : Bag (@Cache _ _ _ _ bag_bag initial_value
                eqA updater updater_cacheable)
        TItem TSearchTerm :=
    {|
      bempty        := Cache_bempty initial_value eqA equiv updater updater_cacheable;
      bstar         := Cache_bstar;
      bfind_matcher := Cache_bfind_matcher initial_value eqA updater updater_cacheable;

      benumerate := Cache_benumerate initial_value eqA updater updater_cacheable;
      bfind      := Cache_bfind      initial_value eqA updater updater_cacheable;
      binsert    := Cache_binsert    initial_value eqA equiv updater updater_cacheable;
      bcount     := Cache_bcount     initial_value eqA updater updater_cacheable;
      bdelete    := Cache_bdelete     initial_value eqA equiv updater updater_cacheable;
      bupdate    := Cache_bupdate    initial_value eqA equiv updater updater_cacheable;

      binsert_enumerate := Cache_BagInsertEnumerate initial_value eqA equiv updater updater_cacheable;
      benumerate_empty  := Cache_BagEnumerateEmpty  initial_value eqA equiv updater updater_cacheable;
      bfind_star        := Cache_BagFindStar        initial_value eqA updater updater_cacheable;
      bfind_correct     := Cache_BagFindCorrect     initial_value eqA updater updater_cacheable;
      bcount_correct    := Cache_BagCountCorrect    initial_value eqA updater updater_cacheable;
      bdelete_correct   := Cache_BagDeleteCorrect   initial_value eqA equiv updater updater_cacheable;
      bupdate_correct   := Cache_BagUpdateCorrect   initial_value eqA equiv updater updater_cacheable
    |}.

  Section CacheableFunctions.
    Section Generalities.
      Lemma projection_cacheable :
        forall {TItem TCacheUpdaterInput TCachedValue}
               (projection: TItem -> TCacheUpdaterInput)
               (eqA: TCachedValue -> TCachedValue -> Prop)
               (updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue),
          IsCacheable eqA updater ->
          IsCacheable eqA (compose updater projection).
      Proof.
        unfold IsCacheable, Proper, respectful.
        intros * is_cacheable * is_eqA * is_perm.
        unfold RecomputeCachedValue in *.
        rewrite !foldright_compose;
          apply is_cacheable;
          try rewrite is_perm;
          eauto.
      Qed.

      Require Import SetEqProperties.
      Lemma projection_strongly_cacheable :
        forall {TItem TCacheUpdaterInput TCachedValue}
               (projection: TItem -> TCacheUpdaterInput)
               (eqA: TCachedValue -> TCachedValue -> Prop)
               (updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue),
          IsStronglyCacheable eqA updater ->
          IsStronglyCacheable eqA (compose updater projection).
      Proof.
        unfold IsStronglyCacheable, Proper, respectful.
        intros * is_cacheable * is_eqA * is_set_eq.
        unfold RecomputeCachedValue in *.
        rewrite !foldright_compose;
          apply is_cacheable;
          try rewrite is_set_eq;
          eauto using SetEq_Reflexive.
      Qed.

      Lemma strongly_cacheable_cacheable :
        forall {TItem TCachedValue} eqA f,
          @IsStronglyCacheable TItem TCachedValue eqA f -> IsCacheable eqA f.
      Proof.
        unfold IsCacheable, IsStronglyCacheable, SetEq, Proper, respectful; intros * set_eq * is_eqA * perm.
        apply set_eq; try assumption; setoid_rewrite perm; reflexivity.
      Qed.

      Definition AddCachingLayer
                 {TBag TItem TSearchTerm TCacheUpdaterInput TCachedValue: Type}
                 (bag_bag: Bag TBag TItem TSearchTerm)
                 (cache_projection: TItem -> TCacheUpdaterInput)
                 (initial_value: TCachedValue)
                 (eqA: TCachedValue -> TCachedValue -> Prop)
                 (equiv: Equivalence eqA)
                 (updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue)
                 (updater_cacheable: IsCacheable eqA updater) :=
        {|
          BagType       :=  @Cache TBag TItem TSearchTerm TCachedValue
                                   bag_bag initial_value
                                   eqA (compose updater cache_projection)
                                   (projection_cacheable cache_projection
                                                         eqA updater
                                                         updater_cacheable);
          SearchTermType := TSearchTerm;
          BagProof       := _
        |}.

      Definition CacheImplementationEnsures
                 {TCacheUpdaterInput TCachedValue}
                 (cache_property: (TCacheUpdaterInput -> TCacheUpdaterInput) ->
                                  list TCacheUpdaterInput ->
                                  TCacheUpdaterInput ->
                                  TCachedValue ->
                                  Prop)
                 (initial_value: TCachedValue)
                 (updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue) : Prop :=
        forall seq (value: TCacheUpdaterInput),
          cache_property (@id TCacheUpdaterInput) seq value
                         (RecomputeCachedValue updater initial_value seq).

      Definition ProjectedCacheImplementationEnsures_strong
                 {TItem TCacheUpdaterInput TCachedValue}
                 (cache_property : (TCacheUpdaterInput -> TCacheUpdaterInput) ->
                                   list TCacheUpdaterInput ->
                                   TCacheUpdaterInput ->
                                   TCachedValue ->
                                   Prop)
                 (initial_value: TCachedValue)
                 (updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue)
                 (projection: TItem -> TCacheUpdaterInput) :=
        forall seq (item: TItem),
          cache_property (@id TCacheUpdaterInput) (List.map projection seq) (projection item)
                         (RecomputeCachedValue (compose updater projection) initial_value seq).


      Definition ProjectedCacheImplementationEnsures
                 {TItem TCacheUpdaterInput TCachedValue}
                 (cache_property : (TItem -> TCacheUpdaterInput) ->
                                   list TItem ->
                                   TItem ->
                                   TCachedValue ->
                                   Prop)
                 (initial_value: TCachedValue)
                 (updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue)
                 (projection: TItem -> TCacheUpdaterInput) :=
        forall seq (item: TItem),
          cache_property projection seq item
                         (RecomputeCachedValue (compose updater projection) initial_value seq).

      Lemma generalize_to_projection :
        forall {TItem TCacheUpdaterInput TCachedValue}
               {updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue}
               (projection: TItem -> TCacheUpdaterInput)
               (initial_value: TCachedValue)
               (cache_property: (TCacheUpdaterInput -> TCacheUpdaterInput) ->
                                list TCacheUpdaterInput ->
                                TCacheUpdaterInput ->
                                TCachedValue ->
                                Prop),
          (CacheImplementationEnsures
             cache_property initial_value updater) ->
          (ProjectedCacheImplementationEnsures_strong
             cache_property initial_value updater projection).
      Proof.
        unfold CacheImplementationEnsures, ProjectedCacheImplementationEnsures_strong, RecomputeCachedValue;
        intros * non_projected_proof *;
        rewrite foldright_compose in *;
        apply non_projected_proof.
      Qed.

      Lemma assert_cache_property :
        forall {TItem TCacheUpdaterInput TCachedValue: Type},
        forall {updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue}
               {projection: TItem -> TCacheUpdaterInput}
               {eqA: TCachedValue -> TCachedValue -> Prop}
               {cached_value: TCachedValue}
               {cache_property},
        forall {seq: list TItem} {initial_value: TCachedValue},
          CachedValueIsFresh eqA initial_value (compose updater projection) seq cached_value ->
          ProjectedCacheImplementationEnsures cache_property initial_value updater projection ->
          Proper (eq ==> eqA ==> iff) (cache_property projection seq) ->
          forall item,
            cache_property projection seq item cached_value.
      Proof.
        intros * fresh_cache impl_ensures * proper *.
        rewrite <- fresh_cache.
        apply impl_ensures.
      Qed.

      Lemma eq_always_proper_for_cache_properties :
        forall {TCacheUpdaterInput TCachedValue} {projection} {seq}
               (cache_property: (TCacheUpdaterInput -> TCacheUpdaterInput) ->
                                list TCacheUpdaterInput ->
                                TCacheUpdaterInput ->
                                TCachedValue ->
                                Prop),
          Proper (eq ==> eq ==> iff) (cache_property projection seq).
      Proof.
        unfold Proper, respectful; intros; subst; reflexivity.
      Qed.
    End Generalities.

    Section MaxCacheable.
      Definition IsMax m seq :=
        (forall x, List.In x seq -> x <= m) /\ List.In m seq.

      Require Import Setoid.
      Add Parametric Morphism (m: nat) :
        (IsMax m)
          with signature (@SetEq nat ==> iff)
            as IsMax_morphism.
      Proof.
        firstorder.
      Qed.

      Definition ListMax default seq :=
        List.fold_right max default seq.

      Lemma ListMax_correct_nil :
        forall seq default,
          seq = nil -> ListMax default seq = default.
      Proof.
        unfold ListMax; intros; subst; intuition.
      Qed.

      Lemma ListMax_correct :
        forall seq default,
          IsMax (ListMax default seq) (default :: seq).
      Proof.
        unfold IsMax;
        induction seq as [ | head tail IH ];
        intros; simpl.

        intuition.

        specialize (IH default);
          destruct IH as (sup & in_seq).

        split.

        intros x [ eq | [ eq | in_tail ] ].

        apply le_r_le_max, sup; simpl; intuition.
        apply le_l_le_max; subst; intuition.
        apply le_r_le_max, sup; simpl; intuition.

        destruct in_seq as [ max_default | max_in_tail ].

        rewrite <- max_default, Max.max_comm;
          destruct (Max.max_spec default head);
          intuition.

        match goal with
          | [ |- context[ max ?a ?b ] ] =>
            destruct (Max.max_spec a b)
              as [ (comp & max_eq) | (comp & max_eq) ]
        end; rewrite max_eq; intuition.
      Qed.

      Lemma Max_unique :
        forall {x y} seq,
          IsMax x seq ->
          IsMax y seq ->
          x = y.
      Proof.
        unfold IsMax;
        intros x y seq (x_sup & x_in) (y_sup & y_in);
        specialize (x_sup _ y_in);
        specialize (y_sup _ x_in);
        apply Le.le_antisym; assumption.
      Qed.

      Lemma ListMax_strongly_cacheable :
        IsStronglyCacheable eq max.
      Proof.
        unfold IsStronglyCacheable.

        intros init1 init2 eq12 seq1 seq2 set_eq; subst;
        apply (Max_unique (init2 :: seq1));
        [ | setoid_rewrite (SetEq_append init2 set_eq) ];
        apply ListMax_correct.
      Qed.

      Lemma ListMax_cacheable :
        IsCacheable eq max.
      Proof.
        intros; apply strongly_cacheable_cacheable.
        apply ListMax_strongly_cacheable.
      Qed.

      Definition cached_gt_property {TItem} (projection: TItem -> nat) seq value cached :=
        List.In value seq -> S cached > projection value.

      Definition cached_neq_property {TItem} (projection: TItem -> nat) seq value cached :=
        List.In value seq -> S cached <> projection value.

      Lemma max_cached_gt :
        forall default,
          CacheImplementationEnsures cached_gt_property default max.
      Proof.
        unfold CacheImplementationEnsures, cached_gt_property;
        intros;
        destruct (ListMax_correct seq default) as (sup & _);
        apply Gt.le_gt_S, sup;
        simpl; auto.
      Qed.

      Lemma max_cached_gt_projected {TItem} {projection} {default} :
        ProjectedCacheImplementationEnsures (TItem := TItem) cached_gt_property default max projection.
      Proof.
        unfold
          ProjectedCacheImplementationEnsures_strong,
        ProjectedCacheImplementationEnsures,
        cached_gt_property in *;
        intros;
        apply (generalize_to_projection projection default cached_gt_property (max_cached_gt default));
        apply in_map_unproject;
        assumption.
      Qed.

      Lemma max_cached_neq_projected {TItem} {projection} {default} :
        ProjectedCacheImplementationEnsures (TItem := TItem) cached_neq_property default max projection.
      Proof.
        unfold
          ProjectedCacheImplementationEnsures,
        cached_neq_property in *;
        intros;
        apply gt_neq_impl, max_cached_gt_projected;
        assumption.
      Qed.
    End MaxCacheable.
  End CacheableFunctions. *)
End CachingBags.
