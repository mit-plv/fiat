Require Export BagsInterface BagsProperties.
Require Import SetEqProperties FMapExtensions AdditionalLemmas.
Require Import FMapInterface Coq.FSets.FMapFacts.

Unset Implicit Arguments.

Module TreeBag (Import M: WS).
  Module Import BasicFacts := WFacts_fun E M.
  Module Import BasicProperties := WProperties_fun E M.
  Module Import MoreFacts := FMapExtensions_fun E M.

  Definition TKey := key.

  Definition IndexedTreeConsistency 
             {TBag TItem TBagSearchTerm: Type}
             {bags_bag: Bag TBag TItem TBagSearchTerm}
             projection fmap :=
    forall (key: TKey) (bag: TBag),
      MapsTo key bag fmap -> 
      forall (item: TItem),
        List.In item (benumerate bag) ->
        E.eq (projection item) key.

  Record IndexedBag 
         {TBag TItem TBagSearchTerm: Type} 
         {bags_bag: Bag TBag TItem TBagSearchTerm} 
         {projection} :=
    { 
      ifmap        : t TBag;
      iconsistency : IndexedTreeConsistency projection ifmap
    }.

  Definition KeyFilter 
             {TItem}
             (key: TKey)
             (projection: TItem -> TKey) :=
    (fun x : TItem => if E.eq_dec (projection x) key then true else false).
  
  Lemma KeyFilter_beq :
    forall {TItem} beq,
      (forall x y, reflect (E.eq x y) (beq x y)) ->
      (forall key projection (item: TItem), 
         KeyFilter key projection item = beq (projection item) key).
  Proof.
    intros TItem beq spec key projection item.
    specialize (spec (projection item) key).
    unfold KeyFilter.
    destruct spec as [ is_eq | neq ];
      destruct (F.eq_dec _ _); intuition.
  Qed.    

  Lemma iconsistency_empty :
    forall {TBag TItem TBagSearchTerm: Type} 
           {bags_bag: Bag TBag TItem TBagSearchTerm} 
           projection,
      IndexedTreeConsistency projection (empty TBag).
  Proof.
    unfold IndexedTreeConsistency; 
    intros; rewrite empty_mapsto_iff in *; exfalso; trivial.
  Qed.

  Lemma consistency_key_eq :
    forall {TBag TItem TBagSearchTerm},
    forall bags_bag (projection: TItem -> TKey),
    forall (indexed_bag: @IndexedBag TBag TItem TBagSearchTerm bags_bag projection),
    forall (key: TKey) bag item,
      MapsTo key bag (ifmap indexed_bag) ->
      List.In item (benumerate bag) ->
      E.eq (projection item) key.
  Proof.
    intros.
    destruct indexed_bag as [? consistent].
    unfold IndexedTreeConsistency in consistent.
    eapply consistent; eauto.
  Qed.

  Ltac destruct_if :=
    match goal with
        [ |- context [ if ?cond then _ else _ ] ] => destruct cond
    end.

  Lemma KeyFilter_true :
    forall {A} k projection (item: A),
      KeyFilter k projection item = true <-> E.eq (projection item) k.
  Proof.
    unfold KeyFilter; intros;
    destruct_if; intros; intuition.
  Qed.

  Lemma KeyFilter_false :
    forall {A} k projection (item: A),
      KeyFilter k projection item = false <-> ~ E.eq (projection item) k.
  Proof.
    unfold KeyFilter; intros;
    destruct_if; intros; intuition.
  Qed.

  Definition IndexedBag_bempty 
             {TBag TItem TBagSearchTerm: Type}
             {bags_bag: Bag TBag TItem TBagSearchTerm}
             (projection: TItem -> TKey) :=
    {| ifmap        := empty TBag;
       iconsistency := iconsistency_empty projection |}.

  Definition IndexedBag_bstar
             {TBag TItem TBagSearchTerm: Type}
             {bags_bag: Bag TBag TItem TBagSearchTerm} :=
    (@None TKey, @bstar _ _ _ bags_bag).

  Definition IndexedBag_bfind_matcher 
             {TBag TItem TBagSearchTerm: Type}
             {bags_bag: Bag TBag TItem TBagSearchTerm}
             (projection: TItem -> TKey)
             (key_searchterm: (option TKey) * TBagSearchTerm) (item: TItem) :=
    let (key_option, search_term) := key_searchterm in
    match key_option with
      | Some k => KeyFilter k projection item
      | None   => true 
    end && (bfind_matcher search_term item).

  Definition IndexedBag_benumerate 
             {TBag TItem TBagSearchTerm: Type}
             {bags_bag: Bag TBag TItem TBagSearchTerm}
             {projection: TItem -> TKey} 
             (container: @IndexedBag TBag TItem TBagSearchTerm bags_bag projection) :=
    flatten (List.map benumerate (Values (ifmap container))).

  Definition IndexedBag_bfind
             {TBag TItem TBagSearchTerm: Type}
             {bags_bag: Bag TBag TItem TBagSearchTerm}
             (projection: TItem -> TKey)
             (container: @IndexedBag TBag TItem TBagSearchTerm bags_bag projection) 
             (key_searchterm: (option TKey) * TBagSearchTerm) :=
    let (key_option, search_term) := key_searchterm in
    match key_option with
      | Some k =>
        match find k (ifmap container) with
          | Some bag => @bfind _ _ _ bags_bag bag search_term
          | None     => nil
        end
      | None   =>
        flatten (List.map (fun bag =>  @bfind _ _ _ bags_bag bag search_term) (Values (ifmap container)))
    end.

  Definition IndexedBag_bcount
             {TBag TItem TBagSearchTerm: Type}
             {bags_bag: Bag TBag TItem TBagSearchTerm}
             (projection: TItem -> TKey)
             (beq : HasDecidableEquality TItem)
             (container: @IndexedBag TBag TItem TBagSearchTerm bags_bag projection)
             (item: TItem) :=
    fold (fun _ bag acc => acc + bcount beq bag item) (ifmap container) 0.

  Lemma indexed_bag_insert_consistent :
    forall {TBag TItem TBagSearchTerm: Type}
           {bags_bag: Bag TBag TItem TBagSearchTerm}
           {projection: TItem -> TKey} 
           (container: @IndexedBag TBag TItem TBagSearchTerm bags_bag projection) 
           (item: TItem),
      let k := projection item in
      let fmap := ifmap container in
      let bag := FindWithDefault k bempty fmap in
      IndexedTreeConsistency projection (add k (binsert bag item) fmap).
  Proof.
    intros.

    intros k' bag' maps_to item'.

    rewrite add_mapsto_iff in maps_to;
      destruct maps_to as [(is_eq & refreshed) | (neq & maps_to)];
      subst.

    rewrite (binsert_enumerate_weak item' item bag).
    intro H; destruct H.
    apply ((iconsistency container) k' bag); trivial. (* TODO: Why are parens significant here? *)

    rewrite <- is_eq.
    unfold bag in *.

    unfold fmap in *.
    destruct (FindWithDefault_dec k (@bempty _ _ _ bags_bag) (ifmap container))
      as [ [bag' (mapsto & equality)] | (not_found & equality) ];
      rewrite equality in *; clear equality.

    subst; trivial.
    exfalso; apply (@benumerate_empty _ _ _ bags_bag) in H; trivial.
    
    subst.
    unfold k in *. 
    trivial.

    apply ((iconsistency container) k' bag' maps_to item').
  Qed.    

  Definition IndexedBag_binsert 
             {TBag TItem TBagSearchTerm: Type}
             {bags_bag: Bag TBag TItem TBagSearchTerm}
             (projection: TItem -> TKey)
             (container: @IndexedBag TBag TItem TBagSearchTerm bags_bag projection) 
             (item: TItem) : @IndexedBag TBag TItem TBagSearchTerm bags_bag projection :=
    let k := projection item in
    let fmap := ifmap container in
    let bag := FindWithDefault k bempty fmap in
    {|
      ifmap := add k (binsert bag item) fmap;
      iconsistency := indexed_bag_insert_consistent container item
    |}.

  Add Parametric Morphism {A} : (* TODO: This speeds up code in elements_fold, but does it break anything? *)
    (@cons A)
      with signature (eq ==> eq ==> eq)
        as cons_eq_eq_eq_morphism.
  Proof.
    trivial.
  Qed.

  Lemma elements_fold_eq :
    forall {TValues} (m: t TValues),
      (elements m) =
      (rev (fold (fun key val acc => cons (key, val) acc) m [])).
  Proof.
    intros.
    rewrite fold_1.

    setoid_rewrite <- surjective_pairing.
    setoid_rewrite fold_left_id.
    rewrite rev_involutive; reflexivity.
  Qed.

  Lemma elements_fold_perm :
    forall {TValues} (m: t TValues),
      Permutation
        (elements m)
        (fold (fun key val acc => cons (key, val) acc) m []).
  Proof.
    intros.
    rewrite fold_1.

    setoid_rewrite <- surjective_pairing.
    setoid_rewrite fold_left_id.
    apply Permutation_rev.
  Qed.

  Lemma fold_right_map :
    forall {A B} f seq, 
      @List.fold_right (list B) A (fun b a => f b :: a) [] seq = List.map f seq.
  Proof.
    intros; induction seq; simpl; try rewrite IHseq; reflexivity.
  Qed.      

  Lemma fold_left_map :
    forall {A B} f seq, 
      @List.fold_left (list B) A (fun a b => f b :: a) seq [] = List.map f (rev seq).
  Proof.
    intros; rewrite <- fold_left_rev_right; apply fold_right_map.
  Qed.

  Lemma Values_fold_perm :
    forall {TValues} (m: t TValues),
      Permutation
        (Values m)
        (fold (fun key val acc => cons val acc) m []).
  Proof.
    intros.
    rewrite fold_1.

    rewrite fold_left_map.
    unfold Values.

    rewrite map_rev.
    apply Permutation_rev.
  Qed.

  Lemma Values_fold_eq :
    forall {TValues} (m: t TValues),
      (Values m) =
      (rev (fold (fun key val acc => cons val acc) m [])).
  Proof.
    intros.
    rewrite fold_1.

    rewrite fold_left_map.
    unfold Values.

    rewrite map_rev.
    rewrite rev_involutive; reflexivity.
  Qed.


  Lemma map_fold :
    forall {A B TValue} f g m init,
      (@List.map A B g
                 (fold
                    (fun k (v: TValue) acc =>
                       f k v :: acc) m init)) = 
      (fold (fun k v acc => g (f k v) :: acc) m (List.map g init)).
  Proof.
    intros until m; setoid_rewrite fold_1.
    setoid_rewrite <- fold_left_rev_right; simpl.
    induction (elements m) as [ | ? ? IH ]; simpl; trivial.
    setoid_rewrite fold_right_app.
    setoid_rewrite IH; simpl.
    reflexivity.
  Qed.

  Lemma values_add_not_in :
    forall {TBag: Type} (m: t TBag),
    forall k v,
      ~ In k m ->
      Permutation
        (Values (add k v m))
        (v :: Values m).
  Proof.
    intros.
    unfold Values.
    rewrite elements_fold_eq.

    rewrite map_rev.
    rewrite map_fold; simpl.
    rewrite (fold_add (eqA := @Permutation _)).
    rewrite fold_1.
    rewrite fold_left_map.
    simpl.

    rewrite map_rev.
    rewrite rev_involutive.
    
    etransitivity.
    apply Permutation_app_comm.
    simpl; reflexivity. 

    apply Permutation_Equivalence.

    unfold Proper, respectful; intros; simpl; 
    subst; apply Permutation_cons; assumption.
    
    unfold transpose_neqkey; intros; simpl;
    constructor.

    assumption.
  Qed.


  Definition KeyBasedPartitioningFunction TBag reference :=
    fun key (_: TBag) => if E.eq_dec key reference then true else false.

  Lemma KeyBasedPartitioningFunction_Proper :
    forall TBag reference, 
      Proper (E.eq ==> eq ==> eq) (KeyBasedPartitioningFunction TBag reference).
  Proof.
    intros;
    unfold KeyBasedPartitioningFunction, Proper, respectful; intros x y E_eq **; subst;
    destruct (F.eq_dec x _), (F.eq_dec y _); rewrite E_eq in *; intuition.
  Qed.  

  Lemma eq_dec_refl :
    forall x,
      (if E.eq_dec x x then true else false) = true.
  Proof.
    intros; destruct (E.eq_dec _ _); eauto using E.eq_refl.
  Qed.

  Lemma eq_dec_comm :
    forall x y,
      (if E.eq_dec x y then true else false) = (if E.eq_dec y x then true else false).
  Proof.
    intros; destruct (E.eq_dec x y), (E.eq_dec y x); intuition. 
  Qed.

  Lemma KeyBasedPartitioningFunction_eq_true :
    forall TValue k k' v,
      E.eq k k' <->
      KeyBasedPartitioningFunction TValue k k' v = true.
  Proof.
    intros; unfold KeyBasedPartitioningFunction; destruct (E.eq_dec _ _); intuition.
  Qed.

  Lemma KeyBasedPartitioningFunction_eq_false :
    forall TValue k k' v,
      ~ E.eq k k' <->
      KeyBasedPartitioningFunction TValue k k' v = false.
  Proof.
    intros; unfold KeyBasedPartitioningFunction; destruct (E.eq_dec _ _); intuition.
  Qed.

  Lemma KeyBasedPartitioningFunction_refl :
    forall TValue k k' v,
      KeyBasedPartitioningFunction TValue k k' v = KeyBasedPartitioningFunction TValue k' k v.
  Proof. 
    intros; unfold KeyBasedPartitioningFunction; rewrite eq_dec_comm; reflexivity.
  Qed.

  (*
    Lemma fold_over_add :
      forall {TValue} k v v' (m: t TValue),
        MapsTo k v m ->
        exists l1 l2,
          Permutation (Values m) (l1 ++ v :: l2) /\
          Permutation (Values (add k v' m)) (l1 ++ v' :: l2).
    Proof.      
      intros.
      pose (partitioned := partition (KeyBasedPartitioningFunction TValue k) m).

    pose proof (KeyBasedPartitioningFunction_Proper TValue k).

    pose (modified := fst partitioned).
    pose (unmodified := snd partitioned).
    assert (partitioned = (modified, unmodified)) as partitioned' by eauto.
    apply partition_Partition in partitioned'; eauto.

    setoid_rewrite Values_fold_perm.
    eexists. eexists.
    rewrite (Partition_fold); eauto.
   *)

  Lemma KeyBasedPartition_fst_singleton :
    forall {TValue} k v (m: t TValue),
      MapsTo k v m ->
      Equal (fst (partition (KeyBasedPartitioningFunction TValue k) m)) (add k v (empty TValue)).
  Proof.
    intros.
    symmetry.
    unfold Equal; intro key.
    
    destruct (E.eq_dec key k) as [ eq_k_proj | neq_k_proj ].
    
    rewrite eq_k_proj;
      rewrite add_eq_o by eauto;
      symmetry; rewrite <- find_mapsto_iff;
      rewrite partition_iff_1 with (f := KeyBasedPartitioningFunction TValue k) (m := m);
      intuition (try rewrite <- KeyBasedPartitioningFunction_eq_true; 
                 eauto using E.eq_refl, KeyBasedPartitioningFunction_Proper).
    
    rewrite add_neq_o by eauto.
    rewrite empty_o.
    destruct (find key _) eqn:eqfind'; 
      [ exfalso | eauto ].
    rewrite <- find_mapsto_iff in eqfind'.
    rewrite partition_iff_1 with (f := KeyBasedPartitioningFunction TValue k) (m := m) in eqfind'.
    destruct eqfind' as (maps_to & kvpf_true).
    apply neq_k_proj.
    erewrite KeyBasedPartitioningFunction_eq_true. 
    rewrite KeyBasedPartitioningFunction_refl.
    eauto.
    eauto using KeyBasedPartitioningFunction_Proper.
    reflexivity.
  Qed.

  Lemma MapsTo_KeyBasedPartition_fst :
    forall {TValue} k k' v (m: t TValue),
      MapsTo k' v (fst (partition (KeyBasedPartitioningFunction TValue k) m)) ->
      E.eq k k'.
  Proof.
    intros * maps_to.
    rewrite partition_iff_1 
    with (f := KeyBasedPartitioningFunction TValue k) (m := m) 
      in maps_to; eauto using KeyBasedPartitioningFunction_Proper.
    destruct maps_to as (_ & kbpf_true).
    rewrite <- KeyBasedPartitioningFunction_eq_true in kbpf_true.
    trivial.
  Qed.

  Lemma In_KeyBasedPartition_fst :
    forall {TValue} k k' (m: t TValue),
      In k' (fst (partition (KeyBasedPartitioningFunction TValue k) m)) ->
      E.eq k k'.
  Proof.
    intros * in_singleton.
    apply In_MapsTo in in_singleton.
    destruct in_singleton as [ val (maps_to & _) ]. 
    eapply MapsTo_KeyBasedPartition_fst; eauto.
  Qed.

  Lemma MapsTo_KeyBasedPartition_snd :
    forall {TValue} k k' v (m: t TValue),
      MapsTo k' v (snd (partition (KeyBasedPartitioningFunction TValue k) m)) ->
      ~ E.eq k k'.
  Proof.
    intros * maps_to.
    rewrite partition_iff_2
    with (f := KeyBasedPartitioningFunction TValue k) (m := m) 
      in maps_to; eauto using KeyBasedPartitioningFunction_Proper.
    destruct maps_to as (_ & kbpf_false).
    rewrite <- KeyBasedPartitioningFunction_eq_false in kbpf_false.
    trivial.
  Qed.

  Lemma In_KeyBasedPartition_snd :
    forall {TValue} k k' (m: t TValue),
      In k' (snd (partition (KeyBasedPartitioningFunction TValue k) m)) ->
      ~ E.eq k k'.
  Proof.
    intros * in_falses.
    apply In_MapsTo in in_falses.
    destruct in_falses as [ val ( maps_to' & _ ) ].
    eapply MapsTo_KeyBasedPartition_snd; eauto.
  Qed.

  Lemma MapsTo_partition_fst:
    forall TValue f k v (m: t TValue),
      Proper (E.eq ==> eq ==> eq) f ->
      MapsTo k v (fst (partition f m)) -> 
      MapsTo k v m.
  Proof.
    intros * ? maps_to.
    rewrite partition_iff_1 with (f := f) (m := m) in maps_to;
      intuition.
  Qed.

  Lemma MapsTo_partition_snd:
    forall TValue f k v (m: t TValue),
      Proper (E.eq ==> eq ==> eq) f ->
      MapsTo k v (snd (partition f m)) -> 
      MapsTo k v m.
  Proof.
    intros * ? maps_to.
    rewrite partition_iff_2 with (f := f) (m := m) in maps_to;
      intuition.
  Qed.

  Lemma partition_after_KeyBasedPartition_and_add :
    forall {TValue} k v' (m: t TValue),
      Partition (add k v' m)
                (add k v' (fst (partition (KeyBasedPartitioningFunction TValue k) m)))
                (snd (partition (KeyBasedPartitioningFunction TValue k) m)).
  Proof.
    unfold Partition.
    split.

    { 
      unfold Disjoint.
      intros key (in_modified & in_unmodified).
      rewrite add_in_iff in in_modified.
      
      assert (E.eq k key) 
        by (
            destruct in_modified;
            [ assumption | eapply In_KeyBasedPartition_fst; eauto ]
          ); clear in_modified.
      
      apply In_KeyBasedPartition_snd in in_unmodified.
      
      intuition.
    }

    split; intros * maps_to'.
    rewrite add_mapsto_iff in maps_to'.
    destruct maps_to' as [ (keq & veq) | (kneq & maps_to') ]; subst.

    left; 
      apply add_1; eauto.
    right; 
      rewrite partition_iff_2 
      with (f := KeyBasedPartitioningFunction TValue k) (m := m) 
      by (eauto using KeyBasedPartitioningFunction_Proper);
      rewrite <- KeyBasedPartitioningFunction_eq_false;
      intuition.

    destruct maps_to' as [ maps_to' | maps_to' ].
    
    rewrite add_mapsto_iff in maps_to';
      destruct maps_to' as [ (keq & veq) | (kneq & maps_to') ]; 
      [ subst; apply add_1; assumption | ].
    
    exfalso.
    apply MapsTo_KeyBasedPartition_fst in maps_to'.
    intuition.

    pose proof maps_to'.
    apply MapsTo_KeyBasedPartition_snd in maps_to'.
    apply add_2;
      [ assumption | eapply MapsTo_partition_snd; eauto using KeyBasedPartitioningFunction_Proper ].
  Qed.

  Lemma partition_Partition_simple :
    forall TValue f,
      Proper (E.eq ==> eq ==> eq) f ->
      forall (m: t TValue),
        Partition m
                  (fst (partition f m))
                  (snd (partition f m)).
  Proof.
    intros.
    eapply partition_Partition; eauto.
  Qed.

  Lemma fold_Equal_simpl :
    forall {TValue TAcc} {eqA: TAcc -> TAcc -> Prop} {m1 m2: t TValue} {f} {init: TAcc},
      Equal m1 m2 ->
      Equivalence eqA ->
      Proper (E.eq ==> eq ==> eqA ==> eqA) f ->
      transpose_neqkey eqA f ->
      eqA (fold f m1 init) (fold f m2 init).
  Proof.
    intros.
    apply fold_Equal; assumption.
  Qed.

  Lemma fold_empty :
    forall {TValue TAcc} f (default: TAcc),
      fold f (empty TValue) default = default.
  Proof.
    intros;
    apply fold_Empty;
    eauto using empty_1.
  Qed.

  Lemma add_Equal_simple :
    forall {TValue} {m1 m2: t TValue},
      Equal m1 m2 ->
      forall k v,
        Equal (add k v m1) (add k v m2). 
  Proof.
    intros.
    apply add_m; eauto.
  Qed.

  Lemma multiple_adds :
    forall {TValue} k v1 v2 (m: t TValue),
      Equal (add k v2 (add k v1 m))
            (add k v2 m).
  Proof.
    intros.
    unfold Equal.
    intros k'.
    destruct (E.eq_dec k k').

    rewrite !add_eq_o; eauto.
    rewrite !add_neq_o; eauto.
  Qed.

  Lemma Values_fold_Proper :
    forall {A},
      Proper (E.eq ==> eq ==> Permutation (A:=A) ==> Permutation (A:=A))
             (fun (_ : key) (val : A) (acc : list A) => val :: acc).
  Proof.
    unfold Proper, respectful; intros.
    subst; eauto.
  Qed.

  Lemma Values_fold_transpose_neqkey :
    forall {A},
      transpose_neqkey (Permutation (A:=A))
                       (fun (_ : key) (val : A) (acc : list A) => val :: acc).
  Proof.
    unfold transpose_neqkey; intros; constructor.
  Qed.

  Lemma empty_In :
    forall {TValue} k,
      ~ In k (empty TValue).
  Proof.
    intros; rewrite empty_in_iff; tauto.
  Qed.      

  Lemma IndexedBag_BagInsertEnumerate :
    forall {TBag TItem TBagSearchTerm: Type}
           {bags_bag: Bag TBag TItem TBagSearchTerm}
           (projection: TItem -> TKey),
      BagInsertEnumerate IndexedBag_benumerate (IndexedBag_binsert projection).
  Proof.
    unfold BagInsertEnumerate, IndexedBag_benumerate.
    intros; simpl in *.

    pose proof bfind_star.
    unfold BagFindStar in H.
    
    match goal with
      | [ |- context[FindWithDefault ?a ?b ?c] ] => 
        destruct (FindWithDefault_dec a b c)
          as [ [ result (maps_to & _eq) ] | (find_none & _eq) ]; 
          rewrite _eq; clear _eq
    end.

    (* Existing key *)
    
    pose proof (partition_after_KeyBasedPartition_and_add 
                  (TValue := TBag) 
                  (projection inserted)
                  (binsert result inserted)
                  (ifmap container)) as part_add.

    pose proof (partition_Partition_simple
                  (TBag)
                  (KeyBasedPartitioningFunction TBag (projection inserted))
                  (KeyBasedPartitioningFunction_Proper _ _)
                  (ifmap container)) as part.

    rewrite !Values_fold_perm 
      by (eauto using Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey).
    
    rewrite Partition_fold at 1 
      by (eauto using part_add, Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey).
    symmetry.
    
    rewrite Partition_fold at 1 
      by (eauto using part    , Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey).
    symmetry.

    pose proof (KeyBasedPartition_fst_singleton (TValue := TBag) _ _ _ maps_to) as singleton.
    pose proof (add_Equal_simple singleton (projection inserted) (binsert result inserted)) as singleton'.

    rewrite (fold_Equal_simpl (eqA := @Permutation TBag) singleton')
      by (eauto using Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey).
    rewrite (fold_Equal_simpl (eqA := @Permutation TBag) singleton)
      by (eauto using Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey).
    rewrite (fold_Equal_simpl (multiple_adds _ _ _ _))
      by (eauto using Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey).
    rewrite !fold_add
      by (eauto using Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey, empty_In).

    rewrite fold_empty.

    simpl.
    rewrite binsert_enumerate.
    rewrite <- app_comm_cons.

    eauto.

    (* New key *)

    rewrite <- not_find_in_iff in find_none.
    rewrite values_add_not_in by assumption.
    simpl.

    rewrite binsert_enumerate.
    rewrite benumerate_empty_eq_nil.
    simpl; reflexivity.
  Qed.

    Lemma fold_map :
      forall {A B C} seq f g init,
        @List.fold_left C A (fun acc x => f acc (g x)) seq init =
        @List.fold_left C B (fun acc x => f acc (  x)) (@List.map A B g seq) init.
    Proof.
      induction seq; simpl; intros; trivial; try rewrite IHseq; intuition.
    Qed.

    Lemma fold_over_Values : 
      forall {TValue TAcc} (m: t TValue) f g (init: TAcc),
        (forall k v acc, f k v acc = g acc v) ->
        fold f m init = fold_left g (Values m) init.
    Proof.
      intros * equiv.
      rewrite fold_1.
      setoid_rewrite equiv.
      rewrite fold_map.
      reflexivity.
    Qed.

  Lemma IndexedBag_BagInsertCount :
    forall {TBag TItem TBagSearchTerm: Type}
           {bags_bag: Bag TBag TItem TBagSearchTerm}
           (projection: TItem -> TKey),
      BagInsertCount IndexedBag_benumerate (IndexedBag_binsert projection) (IndexedBag_bcount projection).
  Proof.

    unfold IndexedBag_bcount, IndexedBag_benumerate, IndexedBag_binsert, BagInsertCount;
    simpl; intros.

    assert ( Proper (E.eq ==> eq ==> eq ==> eq)
                    (fun (_ : key) (bag : TBag) (acc : nat) => acc + bcount beq bag item))
      as add_proper
        by (unfold filter, Proper, respectful; intros; subst; eauto).

    assert ( transpose_neqkey eq
                              (fun (_ : key) (bag : TBag) (acc : nat) => acc + bcount beq bag item))
      as transpose_neqkey_eq
        by (unfold transpose_neqkey; intros; omega).

    match goal with
      | [ |- context[FindWithDefault ?a ?b ?c] ] => 
        destruct (FindWithDefault_dec a b c)
          as [ [ result (maps_to & _eq) ] | (find_none & _eq) ]; 
          rewrite _eq; clear _eq
    end.

    (* Key already found *)
    pose proof (partition_after_KeyBasedPartition_and_add 
                  (TValue := TBag) 
                  (projection inserted)
                  (binsert result inserted)
                  (ifmap container)) as part_add.

    pose proof (partition_Partition_simple
                  (TBag)
                  (KeyBasedPartitioningFunction TBag (projection inserted))
                  (KeyBasedPartitioningFunction_Proper _ _)
                  (ifmap container)) as part.
    
    rewrite Partition_fold at 1 
      by (eauto using part_add, Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey).
    symmetry.
    
    rewrite Partition_fold at 1 
      by (eauto using part    , Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey).
    symmetry.

    pose proof (KeyBasedPartition_fst_singleton (TValue := TBag) _ _ _ maps_to) as singleton.
    pose proof (add_Equal_simple singleton (projection inserted) (binsert result inserted)) as singleton'.

    rewrite (fold_Equal_simpl singleton')
      by (eauto using Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey).
    rewrite (fold_Equal_simpl singleton)
      by (eauto using Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey).
    rewrite (fold_Equal_simpl (multiple_adds _ _ _ _))
      by (eauto using Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey).
    rewrite !fold_add
      by (eauto using Permutation_Equivalence, Values_fold_Proper, Values_fold_transpose_neqkey, empty_In).

    rewrite fold_empty.
    rewrite binsert_count.
    omega.

    (* Key not found *)
    rewrite <- not_find_in_iff in find_none by eauto.
    rewrite (fold_add (eqA := @eq nat)) by eauto.
    rewrite binsert_count.
    rewrite bcount_empty.
    simpl; reflexivity.
  Qed.

  Lemma IndexedBag_BagEnumerateEmpty :
    forall {TBag TItem TBagSearchTerm: Type}
           {bags_bag: Bag TBag TItem TBagSearchTerm}
           (projection: TItem -> TKey),
      BagEnumerateEmpty IndexedBag_benumerate (IndexedBag_bempty projection).
  Proof.
    intros;
    unfold BagEnumerateEmpty, IndexedBag_benumerate, flatten; simpl;
    rewrite Values_empty; tauto.
  Qed.

  Lemma IndexedBag_BagCountEmpty : 
    forall {TBag TItem TBagSearchTerm: Type}
           {bags_bag: Bag TBag TItem TBagSearchTerm}
           (projection: TItem -> TKey),
      BagCountEmpty IndexedBag_benumerate (IndexedBag_bempty projection) (IndexedBag_bcount projection).
  Proof.
    unfold BagCountEmpty, IndexedBag_benumerate, IndexedBag_bempty, IndexedBag_bcount.
    intros; simpl.
    apply fold_Empty; eauto using empty_1.
  Qed.

  Lemma IndexedBag_BagFindStar :
    forall {TBag TItem TBagSearchTerm: Type}
           {bags_bag: Bag TBag TItem TBagSearchTerm}
           (projection: TItem -> TKey),
      BagFindStar (IndexedBag_bfind projection) IndexedBag_benumerate IndexedBag_bstar.
  Proof.
    unfold BagFindStar, IndexedBag_benumerate; simpl.
    
    intros; induction (Values (ifmap container)); simpl; trivial.
    rewrite (@bfind_star _ _ _ bags_bag).
    f_equal; trivial.
  Qed.

  Lemma IndexedBag_BagFindCorrect :
    forall {TBag TItem TBagSearchTerm: Type}
           {bags_bag: Bag TBag TItem TBagSearchTerm}
           (projection: TItem -> TKey),
      BagFindCorrect (IndexedBag_bfind projection)
                     (IndexedBag_bfind_matcher projection) IndexedBag_benumerate.
  Proof.
    intros.
    destruct search_term as (option_key, search_term).
    destruct option_key as [ key | ].

    (* Key provided *)

    unfold IndexedBag_benumerate, IndexedBag_bfind_matcher.
    pose (iconsistency container).
    unfold IndexedTreeConsistency in i.

    rewrite filter_and'.

    rewrite flatten_filter.
    
    Lemma consist :
      forall 
        {TBag TItem TSearchTerm bags_bag projection} 
        (container: @IndexedBag TBag TItem TSearchTerm bags_bag projection),
      forall k,
        eq
          (flatten
             (List.map (List.filter (KeyFilter k projection))
                       (List.map benumerate (Values (ifmap container)))))
          match find k (ifmap container) with
            | Some bag => benumerate bag
            | None => nil
          end.
    Proof.          
      intros.

      pose (iconsistency container); unfold IndexedTreeConsistency in i.
      unfold Values.
      destruct (find k (ifmap container)) as [ bag | ] eqn:eqfind.

      rewrite <- find_mapsto_iff in eqfind.
      (* assert (exists k', MapsTo k' bag (ifmap container)) as eqfind' by (exists k; trivial).*)

      pose proof eqfind as maps_to.

      rewrite elements_mapsto_iff in eqfind.
      apply InA_split in eqfind.

      destruct eqfind as [ l1 [ y [ l2 (y_k_bag & decomp) ] ] ].
      rewrite decomp.
      
      rewrite (map_map snd benumerate).
      rewrite ! map_app; simpl.
      
      pose proof (elements_3w (ifmap container)) as no_dup.
      rewrite decomp in no_dup; apply NoDupA_swap in no_dup; eauto using equiv_eq_key.

      inversion no_dup as [ | ? ? y_not_in no_dup' ]; subst.
      rewrite InA_app_iff in y_not_in by eauto using equiv_eq_key.
      
      unfold eq_key_elt in y_k_bag; simpl in y_k_bag.
      destruct y_k_bag as (y_k & y_bag).

      assert (forall k' bag', InA (@eq_key_elt _) (k', bag') (l1 ++ l2) -> 
                              forall item, 
                                List.In item (benumerate bag') ->
                                ~ E.eq (projection item) k).
      {
        intros k' bag' in_app item in_bag'_items eq_k.

        rewrite InA_app_iff in in_app; eauto using equiv_eq_key_elt.
        pose proof in_app as in_app'.

        apply (InA_front_tail_InA _ _ y) in in_app.
        rewrite <- decomp, <- elements_mapsto_iff in in_app.

        pose proof (i _ _ in_app _ in_bag'_items) as eq_k'. 
        symmetry in eq_k.
        pose proof (E.eq_trans eq_k eq_k').

        assert (eq_key y (k', bag')) as y_eq by (unfold eq_key; simpl; eauto).

        destruct in_app' as [ in_seq | in_seq ];
          (apply (InA_eqke_eqk (k2 := fst y) (snd y)) in in_seq; eauto);
          rewrite <- surjective_pairing in in_seq; intuition.
      }

      Lemma In_InA :
        forall (A : Type) (l : list A) (eqA : relation A) (x : A),
          Equivalence eqA -> List.In x l -> InA eqA x l.
      Proof.
        induction l; intros; simpl in *.
        exfalso; eauto using in_nil.
        destruct H0.
        apply InA_cons_hd; subst; reflexivity.
        apply InA_cons_tl, IHl; trivial.
      Qed.

      rewrite ! map_filter_all_false;
        [ | intros subseq in_map item in_subseq;
            rewrite in_map_iff in in_map;
            destruct in_map as [ (k', bag') (benum_eq & in_seq) ];
            rewrite KeyFilter_false;
            
            simpl in benum_eq;
            subst subseq;
            apply (H k' bag'); 
            eauto;
            
            apply In_InA; eauto using equiv_eq_key_elt;
            rewrite in_app_iff;
            eauto 
              .. ].

      rewrite 
        flatten_app, 
      flatten_head, 
      !flatten_nils, 
      app_nil_l, app_nil_r, 
      <- y_bag,
      filter_all_true; trivial.

      intros;
        rewrite KeyFilter_true;
        apply (iconsistency container _ bag); eauto.

      Lemma nil_in_false :
        forall {A} seq,
          seq = nil <-> ~ exists (x: A), List.In x seq.
      Proof.
        split; intro H.
        intros [ x in_seq ]; subst; eauto using in_nil.
        destruct seq as [ | a ]; trivial.
        exfalso; apply H; exists a; simpl; intuition.
      Qed.
      
      rewrite nil_in_false.
      intros [item item_in].

      rewrite in_flatten_iff in item_in.
      do 2 setoid_rewrite in_map_iff in item_in.

      destruct item_in as 
          [ subseq 
              (in_subseq 
                 & [ subseq_prefilter 
                       ( pre_post_filter 
                           & [ bag 
                                 (eq_bag_pre_filter 
                                    & bag_in) ] ) ] ) ].

      subst subseq.
      rewrite filter_In in in_subseq.
      destruct in_subseq as (in_subseq_prefilter & key_filter).

      rewrite KeyFilter_true in key_filter.
      rewrite <- MapsTo_snd in bag_in.
      destruct bag_in as [k' maps_to].

      subst.
      rewrite <- key_filter in eqfind.
      rewrite <- (iconsistency container k' bag maps_to _ in_subseq_prefilter) in maps_to.
      rewrite find_mapsto_iff in maps_to.

      congruence.
    Qed.

    simpl.
    rewrite consist.
    destruct (find key (ifmap container)) as [ bag | ].

    apply bfind_correct.
    eauto. 

    (* No key provided *)

    simpl. unfold IndexedBag_benumerate, IndexedBag_bfind_matcher.
    rewrite flatten_filter.

    induction (Values (ifmap container)); simpl.

    eauto.

    apply Permutation_app.
    apply (bfind_correct _).

    rewrite IHl; reflexivity.
  Qed.
  
  Instance IndexedBagAsBag 
           (TBag TItem TBagSearchTerm: Type) 
           (bags_bag: Bag TBag TItem TBagSearchTerm) (projection: TItem -> TKey) 
  : Bag 
      (@IndexedBag TBag TItem TBagSearchTerm bags_bag projection) 
      TItem 
      ((option TKey) * TBagSearchTerm) :=
    {| 
      bempty        := IndexedBag_bempty projection;
      bstar         := IndexedBag_bstar;
      bfind_matcher := IndexedBag_bfind_matcher projection;

      benumerate := IndexedBag_benumerate;
      bfind      := IndexedBag_bfind projection;
      binsert    := IndexedBag_binsert projection;

      binsert_enumerate := IndexedBag_BagInsertEnumerate projection;
      binsert_count     := IndexedBag_BagInsertCount projection;
      benumerate_empty  := IndexedBag_BagEnumerateEmpty projection;
      bcount_empty      := IndexedBag_BagCountEmpty projection;
      bfind_star        := IndexedBag_BagFindStar projection;
      bfind_correct     := IndexedBag_BagFindCorrect projection
    |}. 
End TreeBag.