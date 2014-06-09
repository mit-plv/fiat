Require Export BagsInterface BagsProperties.
Require Import AdditionalLemmas.

Unset Implicit Arguments.

Definition RecomputeCachedValue
           {TItem TCachedValue}
           (updater: TItem -> TCachedValue -> TCachedValue)            
           (initial_value: TCachedValue) 
           (items: list TItem) :=
  List.fold_right updater initial_value items.

Definition CachedValueIsFresh
           {TItem TCachedValue}
           (updater: TItem -> TCachedValue -> TCachedValue)            
           (initial_value: TCachedValue) 
           (items: list TItem)
           (cached_value: TCachedValue) :=
  RecomputeCachedValue updater initial_value items = cached_value.

Definition IsCacheable
           {TItem TCachedValue}
           (updater: TItem -> TCachedValue -> TCachedValue)
           (initial_value: TCachedValue) :=
  forall seq1 seq2,
    SetEq seq1 seq2 ->
    RecomputeCachedValue updater initial_value seq1 =
    RecomputeCachedValue updater initial_value seq2.

Record Cache 
       {TBag TItem TSearchTerm TCachedValue: Type} 
       {bag_bag: Bag TBag TItem TSearchTerm}
       {initial_value: TCachedValue}
       {updater: TItem -> TCachedValue -> TCachedValue}
       {updater_cacheable: IsCacheable updater initial_value} :=
  { 
    cbag:          TBag;
    ccached_value: TCachedValue;
    cfresh_cache:  CachedValueIsFresh updater initial_value (benumerate cbag) ccached_value
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
           {updater: TItem -> TCachedValue -> TCachedValue}
           {updater_cacheable: IsCacheable updater initial_value}
           (cache: @Cache TBag TItem TSearchTerm TCachedValue bag_bag initial_value updater updater_cacheable) := 
  updater_cacheable.

Lemma empty_caching_bag_fresh:
  forall {TBag TItem TSearchTerm TCachedValue: Type}
         {bag_bag : Bag TBag TItem TSearchTerm}
         (initial_value : TCachedValue)
         (updater : TItem -> TCachedValue -> TCachedValue)
         (updater_cacheable: IsCacheable updater initial_value),
    CachedValueIsFresh updater initial_value (benumerate bempty) initial_value.
Proof.
  intros; rewrite benumerate_empty_eq_nil; reflexivity.
Qed.

Definition Cache_bempty
           {TBag TItem TSearchTerm TCachedValue: Type}
           {bag_bag : Bag TBag TItem TSearchTerm}
           (updater : TItem -> TCachedValue -> TCachedValue)
           (initial_value : TCachedValue)
           (updater_cacheable: IsCacheable updater initial_value) :
  (@Cache _ _ _ _ bag_bag initial_value updater updater_cacheable) :=
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
           (updater : TItem -> TCachedValue -> TCachedValue)
           (initial_value : TCachedValue)
           (updater_cacheable: IsCacheable updater initial_value) 
           (search_term: TSearchTerm) (item: TItem) :=
  bfind_matcher search_term item.

Definition Cache_benumerate
           {TBag TItem TSearchTerm TCachedValue: Type} 
           {bag_bag: Bag TBag TItem TSearchTerm}
           (updater: TItem -> TCachedValue -> TCachedValue)
           (initial_value: TCachedValue)
           (updater_cacheable: IsCacheable updater initial_value) 
           (container: @Cache _ _ _ _ bag_bag initial_value 
                              updater updater_cacheable) :=
  benumerate (cbag container).
         
Definition Cache_bfind
           {TBag TItem TSearchTerm TCachedValue: Type} 
           {bag_bag: Bag TBag TItem TSearchTerm}
           (updater: TItem -> TCachedValue -> TCachedValue)
           (initial_value: TCachedValue)
           (updater_cacheable: IsCacheable updater initial_value) 
           (container: @Cache _ _ _ _ bag_bag initial_value 
                              updater updater_cacheable) 
           (search_term: TSearchTerm) :=
  bfind (cbag container) search_term.
         
Lemma updated_cache_fresh_after_insert :
  forall {TBag TItem TSearchTerm TCachedValue: Type} 
         {bag_bag: Bag TBag TItem TSearchTerm}
         (updater: TItem -> TCachedValue -> TCachedValue)
         (initial_value: TCachedValue)
         (updater_cacheable: IsCacheable updater initial_value) 
         (container: @Cache _ _ _ _ bag_bag initial_value 
                            updater updater_cacheable) 
         (item: TItem),
    CachedValueIsFresh updater initial_value
                       (benumerate (binsert (cbag container) item))
                       (updater item (ccached_value container)).
  Proof.
    intros;
    unfold CachedValueIsFresh;
    setoid_rewrite (updater_cacheable _ _ (binsert_enumerate_SetEq bag_bag _ _));
    simpl; rewrite cfresh_cache; reflexivity. (* TODO: Replacing rewrite with setoid_rewrite here throws a coq bug *)
  Qed.

Definition Cache_binsert
           {TBag TItem TSearchTerm TCachedValue: Type} 
           {bag_bag: Bag TBag TItem TSearchTerm}
           (updater: TItem -> TCachedValue -> TCachedValue)
           (initial_value: TCachedValue)
           (updater_cacheable: IsCacheable updater initial_value) 
           (container: @Cache _ _ _ _ bag_bag initial_value 
                              updater updater_cacheable) 
           (item: TItem) : @Cache _ _ _ _ bag_bag initial_value 
                              updater updater_cacheable :=
  {|
    cbag          := binsert (cbag container) item;
    ccached_value := updater item (ccached_value container);
    cfresh_cache  := updated_cache_fresh_after_insert _ _ _ _ _
  |}.

Ltac transparent_implementation :=
  unfold BagInsertEnumerate, BagEnumerateEmpty, BagFindStar, BagFindCorrect;
  intros; 
  first [ apply binsert_enumerate | apply benumerate_empty | apply bfind_correct | apply bfind_star ].

Lemma Cache_BagInsertEnumerate :
  forall {TBag TItem TSearchTerm TCachedValue: Type} 
         {bag_bag: Bag TBag TItem TSearchTerm}
         (updater: TItem -> TCachedValue -> TCachedValue)
         (initial_value: TCachedValue)
         (updater_cacheable: IsCacheable updater initial_value),
   BagInsertEnumerate
     (Cache_benumerate updater initial_value updater_cacheable)
     (Cache_binsert    updater initial_value updater_cacheable).
Proof. transparent_implementation. Qed.

Lemma Cache_BagEnumerateEmpty :
  forall {TBag TItem TSearchTerm TCachedValue: Type} 
         {bag_bag: Bag TBag TItem TSearchTerm}
         (updater: TItem -> TCachedValue -> TCachedValue)
         (initial_value: TCachedValue)
         (updater_cacheable: IsCacheable updater initial_value),
 BagEnumerateEmpty
   (Cache_benumerate updater initial_value updater_cacheable)
   (Cache_bempty     updater initial_value updater_cacheable).
Proof. transparent_implementation. Qed.

Lemma Cache_BagFindStar :
  forall {TBag TItem TSearchTerm TCachedValue: Type} 
         {bag_bag: Bag TBag TItem TSearchTerm}
         (updater: TItem -> TCachedValue -> TCachedValue)
         (initial_value: TCachedValue)
         (updater_cacheable: IsCacheable updater initial_value),
 BagFindStar
   (Cache_bfind      updater initial_value updater_cacheable)
   (Cache_benumerate updater initial_value updater_cacheable)
   Cache_bstar.
Proof. transparent_implementation. Qed.

Lemma Cache_BagFindCorrect :
  forall {TBag TItem TSearchTerm TCachedValue: Type} 
         {bag_bag: Bag TBag TItem TSearchTerm}
         (updater: TItem -> TCachedValue -> TCachedValue)
         (initial_value: TCachedValue)
         (updater_cacheable: IsCacheable updater initial_value),
    BagFindCorrect
      (Cache_bfind         updater initial_value updater_cacheable)
      (Cache_bfind_matcher updater initial_value updater_cacheable)
      (Cache_benumerate    updater initial_value updater_cacheable).
Proof. transparent_implementation. Qed.

Instance CacheAsBag
         {TBag TItem TSearchTerm TCachedValue: Type} 
         {bag_bag: Bag TBag TItem TSearchTerm}
         (updater: TItem -> TCachedValue -> TCachedValue)
         (initial_value: TCachedValue)
         (updater_cacheable: IsCacheable updater initial_value)
         : Bag (@Cache _ _ _ _ bag_bag initial_value 
                       updater updater_cacheable) 
               TItem TSearchTerm :=
  {| 
    bempty        := Cache_bempty updater initial_value updater_cacheable;
    bstar         := Cache_bstar;
    bfind_matcher := Cache_bfind_matcher updater initial_value updater_cacheable;

    benumerate := Cache_benumerate updater initial_value updater_cacheable;
    bfind      := Cache_bfind      updater initial_value updater_cacheable;
    binsert    := Cache_binsert    updater initial_value updater_cacheable;

    binsert_enumerate := Cache_BagInsertEnumerate updater initial_value updater_cacheable;
    benumerate_empty  := Cache_BagEnumerateEmpty  updater initial_value updater_cacheable;
    bfind_star        := Cache_BagFindStar        updater initial_value updater_cacheable;
    bfind_correct     := Cache_BagFindCorrect     updater initial_value updater_cacheable
  |}.

Section CacheableFunctions.
  Section Generalities.
    Lemma projection_cacheable :
      forall {TItem TCacheUpdaterInput TCachedValue}
             (projection: TItem -> TCacheUpdaterInput)
             (updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue)
             (initial_value: TCachedValue),
        IsCacheable updater initial_value -> 
        IsCacheable (compose updater projection) initial_value.
      Proof.
        unfold IsCacheable.
        intros * is_cacheable * set_eq. 
        unfold RecomputeCachedValue in *.
        rewrite !foldright_compose;
          apply is_cacheable;
          rewrite set_eq;
          reflexivity.
      Qed.

      Definition AddCachingLayer
                 {TBag TItem TSearchTerm TCacheUpdaterInput TCachedValue: Type} 
                 (bag_bag: Bag TBag TItem TSearchTerm)
                 (cache_projection: TItem -> TCacheUpdaterInput) 
                 (initial_value: TCachedValue)
                 (updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue) 
                 (updater_cacheable: IsCacheable updater initial_value) :=
        {|
          BagType       :=  @Cache TBag TItem TSearchTerm TCachedValue  
                                   bag_bag initial_value 
                                   (compose updater cache_projection) 
                                   (projection_cacheable cache_projection 
                                                         updater 
                                                         initial_value 
                                                         updater_cacheable);
          SearchTermType := TSearchTerm;
          BagProof       := _
        |}.

      Definition CacheImplementationEnsures
                 {TCacheUpdaterInput TCachedValue}
                 (cache_property: (TCacheUpdaterInput -> TCacheUpdaterInput) -> list TCacheUpdaterInput -> TCacheUpdaterInput -> TCachedValue -> Prop)
                 (updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue) 
                 (initial_value: TCachedValue) : Prop :=
        forall seq (value: TCacheUpdaterInput),
          cache_property (@id TCacheUpdaterInput) seq value 
                         (RecomputeCachedValue updater initial_value seq).

      Definition ProjectedCacheImplementationEnsures_strong
                 {TItem TCacheUpdaterInput TCachedValue}
                 (cache_property : (TCacheUpdaterInput -> TCacheUpdaterInput) ->
                                   list TCacheUpdaterInput -> TCacheUpdaterInput -> TCachedValue -> Prop)
                 (updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue) 
                 (projection: TItem -> TCacheUpdaterInput)
                 (initial_value: TCachedValue) :=
        forall seq (item: TItem),
          cache_property (@id TCacheUpdaterInput) (List.map projection seq) (projection item) 
                         (RecomputeCachedValue (compose updater projection) initial_value seq).


      Definition ProjectedCacheImplementationEnsures
                 {TItem TCacheUpdaterInput TCachedValue}
                 (cache_property : (TItem -> TCacheUpdaterInput) ->
                                   list TItem -> TItem -> TCachedValue -> Prop)
                 (updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue) 
                 (projection: TItem -> TCacheUpdaterInput)
                 (initial_value: TCachedValue) :=
        forall seq (item: TItem),
          cache_property projection seq item 
                         (RecomputeCachedValue (compose updater projection) initial_value seq).

      Lemma generalize_to_projection :
        forall {TItem TCacheUpdaterInput TCachedValue} 
               {updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue}
               (projection: TItem -> TCacheUpdaterInput)
               (initial_value: TCachedValue)
               (cache_property: (TCacheUpdaterInput -> TCacheUpdaterInput) -> list TCacheUpdaterInput ->
                                TCacheUpdaterInput -> TCachedValue -> Prop),
          (CacheImplementationEnsures          
             cache_property updater initial_value) ->
          (ProjectedCacheImplementationEnsures_strong
             cache_property updater projection initial_value).
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
               {cached_value: TCachedValue}
               {cache_property},
        forall {seq: list TItem} {initial_value: TCachedValue},
          CachedValueIsFresh (compose updater projection) initial_value seq cached_value ->
          ProjectedCacheImplementationEnsures cache_property updater projection initial_value ->
          forall item,
            cache_property projection seq item cached_value.
      Proof.
        intros * fresh_cache impl_ensures *.
        rewrite <- fresh_cache.
        apply impl_ensures.
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

    (* TODO: rename SetEq_append to SetEq_cons *)

    (* TODO: find a cleaner way than destruct; discriminate *)
    (* TODO: Look at reflexive, discriminate, congruence, absurd in more details *)

    Lemma ListMax_cacheable :
      forall initial_value,
        IsCacheable max initial_value.
    Proof.
      unfold IsCacheable.

      intros init seq1 seq2 set_eq;
        apply (Max_unique (init :: seq1));
        [ | setoid_rewrite (SetEq_append init set_eq) ];
        apply ListMax_correct.
    Qed.

    Definition cached_gt_property {TItem} (projection: TItem -> nat) seq value cached :=
      List.In value seq -> S cached > projection value.

    Definition cached_neq_property {TItem} (projection: TItem -> nat) seq value cached :=
      List.In value seq -> S cached <> projection value.

    Lemma max_cached_gt :
      forall default,
        CacheImplementationEnsures cached_gt_property max default. 
    Proof.
      unfold CacheImplementationEnsures, cached_gt_property; 
      intros;
      destruct (ListMax_correct seq default) as (sup & _);
      apply Gt.le_gt_S, sup;
      simpl; auto.
    Qed.

    Lemma max_cached_gt_projected {TItem} projection : 
      forall default,
        ProjectedCacheImplementationEnsures (TItem := TItem) cached_gt_property max projection default.
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

    Lemma max_cached_neq_projected {TItem} projection : 
      forall default,
        ProjectedCacheImplementationEnsures (TItem := TItem) cached_neq_property max projection default.
    Proof.
      unfold 
        ProjectedCacheImplementationEnsures,
        cached_neq_property in *;
      intros; 
      apply gt_neq_impl, max_cached_gt_projected; 
      assumption.
    Qed.
  End MaxCacheable.
End CacheableFunctions.
