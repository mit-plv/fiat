Require Export Bags.
Require Import AdditionalLemmas.

Unset Implicit Arguments.

Definition IsCacheable
           {TItem TAcc}
           (initial_value: TAcc)
           (cache_updater: TItem -> TAcc -> TAcc) :=
  forall seq1 seq2,
    SetEq seq1 seq2 ->
    (List.fold_right cache_updater initial_value seq1 =
     List.fold_right cache_updater initial_value seq2).

Record CachingBag 
       {TBag TItem TSearchTerm: Type} 
       {bag_bag: Bag TBag TItem TSearchTerm} 
       {TCachedValue: Type}
       {initial_cached_value: TCachedValue}
       {cache_updater: TItem -> TCachedValue -> TCachedValue} 
       {cache_updater_cacheable: IsCacheable initial_cached_value cache_updater} :=
  { 
    cbag:          TBag;
    ccached_value: TCachedValue;
    
    cfresh_cache:  List.fold_right cache_updater initial_cached_value (benumerate cbag) = ccached_value
  }.

(* Note: The caching interface provides the initial_cached_value
         parameter to allow implementations to gracefully handle empty
         caches. Should an empty/non-empty distinction be needed,
         initial_cached_value can be set to None, and TCachedValue
         replaced by an option type. *)

Lemma binsert_enumerate_SetEq {TContainer TItem TSearchTerm} (bag: Bag TContainer TItem TSearchTerm):
  forall inserted container,
    SetEq 
      (benumerate (binsert container inserted))
      (inserted :: (benumerate container)).
Proof.
  unfold SetEq; intros; simpl.
  setoid_rewrite or_comm; setoid_rewrite eq_sym_iff. 
  apply binsert_enumerate. 
Qed.

Lemma benumerate_empty_eq_nil {TContainer TItem TSearchTerm} (bag: Bag TContainer TItem TSearchTerm):
  (benumerate bempty) = nil. 
Proof.
  pose proof (benumerate_empty) as not_in;
  unfold BagEnumerateEmpty in not_in.
  destruct (benumerate bempty) as [ | item ? ]; 
    simpl in *;
    [ | exfalso; apply (not_in item) ];
    eauto.
Qed.

Instance CachingBagAsBag 
         {TBag TItem TSearchTerm: Type} 
         {bag_bag: Bag TBag TItem TSearchTerm} 
         {TCachedValue: Type}
         {initial_cached_value: TCachedValue} 
         {cache_updater: TItem -> TCachedValue -> TCachedValue} 
         {cache_updater_cacheable: IsCacheable initial_cached_value cache_updater}
         : Bag (@CachingBag TBag TItem TSearchTerm bag_bag 
                            TCachedValue initial_cached_value cache_updater
                            cache_updater_cacheable) 
               TItem 
               TSearchTerm :=
  {| 
    bempty                         := {| cbag          := @bempty _ _ _ bag_bag; 
                                         ccached_value := initial_cached_value |};
    bstar                          := @bstar _ _ _ bag_bag;
    bfind_matcher search_term item := bfind_matcher search_term item;

    benumerate container        := benumerate container.(cbag);
    bfind container search_term := bfind container.(cbag) search_term; 
    binsert container item      := {| cbag          := binsert container.(cbag) item;
                                      ccached_value := cache_updater item container.(ccached_value) |} 
  |}.
Proof.    
  unfold BagInsertEnumerate; simpl; intros. apply binsert_enumerate.
  unfold BagEnumerateEmpty;  simpl; intros; apply benumerate_empty.
  unfold BagFindStar;        simpl; intros; apply bfind_star.
  unfold BagFindCorrect;     simpl; intros; apply bfind_correct.

  Grab Existential Variables.

  rewrite (cache_updater_cacheable _ _ (binsert_enumerate_SetEq bag_bag _ _));
  simpl; setoid_rewrite cfresh_cache; reflexivity.

  rewrite benumerate_empty_eq_nil; reflexivity.
Defined.

Section CacheableFunctions.
  Section Generalities.
    Lemma projection_cacheable :
      forall {TItem TCacheUpdaterInput TCachedValue} 
             (projection: TItem -> TCacheUpdaterInput)
             (cache_updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue)
             (initial_value: TCachedValue),
        IsCacheable initial_value cache_updater -> 
        IsCacheable initial_value (compose cache_updater projection).
      Proof.
        unfold IsCacheable.
        intros * is_cacheable * set_eq. 
        rewrite !foldright_compose;
          apply is_cacheable;
          rewrite set_eq;
          reflexivity.
      Qed.

      Definition AddCachingLayer
                 {TBag TItem TSearchTerm: Type} 
                 (bag: Bag TBag TItem TSearchTerm)
                 {TCacheUpdaterInput TCachedValue: Type}
                 (cache_projection: TItem -> TCacheUpdaterInput) 
                 (initial_cached_value: TCachedValue)
                 (cache_updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue) 
                 (cache_updater_cacheable: IsCacheable initial_cached_value cache_updater) :=
        {|
          BagType       :=  @CachingBag TBag TItem TSearchTerm 
                                        bag TCachedValue initial_cached_value 
                                        (compose cache_updater cache_projection) 
                                        (projection_cacheable cache_projection 
                                                              cache_updater 
                                                              initial_cached_value 
                                                              cache_updater_cacheable);
          SearchTermType := TSearchTerm;
          BagProof       := _
        |}.

      Definition CacheImplementationEnsures
                 {TCacheUpdaterInput TCachedValue}
                 cache_property
                 (cache_updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue) 
                 (initial_value: TCachedValue) :=
        forall seq (value: TCacheUpdaterInput),
          cache_property seq value (List.fold_right cache_updater initial_value seq).

      Definition ProjectedCacheImplementationEnsures
                 {TItem TCacheUpdaterInput TCachedValue}
                 cache_property
                 (cache_updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue) 
                 (projection: TItem -> TCacheUpdaterInput)
                 (initial_value: TCachedValue) :=
        forall seq (item: TItem),
          cache_property (List.map projection seq) (projection item) (List.fold_right (compose cache_updater projection) initial_value seq).

      (* Formally equivalent to ProjectedCacheImplementationEnsures cache_property id initial_value *)

      Lemma generalize_to_projection :
        forall {TItem TCacheUpdaterInput TCachedValue} 
               {cache_updater: TCacheUpdaterInput -> TCachedValue -> TCachedValue}
               (projection: TItem -> TCacheUpdaterInput)
               (initial_value: TCachedValue)
               (cache_property: list TCacheUpdaterInput ->
                                TCacheUpdaterInput -> TCachedValue -> Type),
          (CacheImplementationEnsures          
             cache_property cache_updater initial_value) ->
          (ProjectedCacheImplementationEnsures
             cache_property cache_updater projection initial_value).
      Proof.
        unfold CacheImplementationEnsures, ProjectedCacheImplementationEnsures;
        intros * non_projected_proof *;
        rewrite foldright_compose;
        apply non_projected_proof.
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
        | [ |- context[ max ?a ?b ] ] => destruct (Max.max_spec a b) as [ (comp & max_eq) | (comp & max_eq) ]
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
        IsCacheable initial_value max.
    Proof.
      unfold IsCacheable.

      intros init seq1 seq2 set_eq;
        apply (Max_unique (init :: seq1));
        [ | setoid_rewrite (SetEq_append init set_eq) ];
        apply ListMax_correct.
    Qed.

    Definition cached_max_gt_property seq value cached_max :=
      List.In value seq -> S cached_max > value.

    Lemma cached_max_gt :
      forall default,
        CacheImplementationEnsures cached_max_gt_property max default. 
    Proof.
      unfold CacheImplementationEnsures, cached_max_gt_property; 
      intros;
      destruct (ListMax_correct seq default) as (sup & _);
      apply Gt.le_gt_S, sup;
      simpl; auto.
    Qed.

    Lemma cached_max_gt_projected' {TItem} projection :
      forall default,
        ProjectedCacheImplementationEnsures (TItem := TItem) cached_max_gt_property max projection default.
    Proof.
      unfold ProjectedCacheImplementationEnsures.
      unfold cached_max_gt_property.

      intros;
      apply (generalize_to_projection projection default cached_max_gt_property (cached_max_gt default));
      trivial.
    Qed.

    Lemma cached_max_gt_projected : 
      forall {A} projection,
      forall default seq (item: A),
        List.In item seq -> S (List.fold_right (compose max projection) default seq) > (projection item).
    Proof.
      intros;
      apply (cached_max_gt_projected' projection);
      apply (in_map_unproject); trivial.
    Qed.
  End MaxCacheable.
End CacheableFunctions.
