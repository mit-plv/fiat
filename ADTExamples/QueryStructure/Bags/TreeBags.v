Require Export Bags.
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

    rewrite (binsert_enumerate item' item bag).
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

  Lemma IndexedBag_BagInsertEnumerate :
    forall {TBag TItem TBagSearchTerm: Type}
           {bags_bag: Bag TBag TItem TBagSearchTerm}
           (projection: TItem -> TKey),
      BagInsertEnumerate IndexedBag_benumerate (IndexedBag_binsert projection).
  Proof.

    unfold BagInsertEnumerate, Values, IndexedBag_benumerate.
    intros; simpl in *.

    setoid_rewrite in_flatten_iff.
    setoid_rewrite in_map_iff.
    setoid_rewrite <- MapsTo_snd.

    split; intro H.

    destruct H as [ items ( in_seq & [ bag (bag_items & [ key maps_to ]) ] ) ].
    pose proof maps_to as maps_to'.
    rewrite add_mapsto_iff in maps_to;
      destruct maps_to as [(is_eq & refreshed) | (neq & maps_to)].

    subst.
    rewrite (binsert_enumerate _) in in_seq.
    destruct in_seq as [ in_seq | ? ]; eauto.
    left.
    
    Ltac autoexists :=
      repeat progress match goal with
                        | [ |- exists _, _ ] => eexists; autoexists
                        | [ |- ?a = ?b ]     => first [ (has_evar a; has_evar b; idtac) | eauto]
                        | [ |- E.eq _ _ ]    => eauto
                        | [ |- _ /\ _ ]      => split; autoexists
                        | [ |- _ \/ _ ]      => left; autoexists
                      end.
    
    destruct (FindWithDefault_dec (projection inserted) bempty (ifmap container)) 
      as [ [result (mapsto & equality)] | (not_found & equality) ];
      rewrite equality in *; clear equality.
    
    autoexists; eauto.
    
    exfalso; apply benumerate_empty in in_seq; tauto.

    autoexists; eauto.

    destruct H as [ [ items ( in_seq & [ bag ( bag_items & [ key maps_to ] ) ] ) ] | eq_item_inserted ].
    
    pose proof maps_to as maps_to'.
    apply (iconsistency container) in maps_to.    
    setoid_rewrite bag_items in maps_to.
    specialize (maps_to item in_seq).
    
    setoid_rewrite add_mapsto_iff.

    destruct (E.eq_dec (projection inserted) key);
      try solve [ repeat (eexists; split; eauto) ].
    
    autoexists.

    apply binsert_enumerate.

    destruct (FindWithDefault_dec (projection inserted) bempty (ifmap container))
      as [ [bag' (mapsto & equality)] | (not_found & equality) ];
      rewrite equality in *; clear equality.

    rewrite e in mapsto.
    pose proof (MapsTo_fun mapsto maps_to') as bag'_bag.
    rewrite bag'_bag.
    rewrite bag_items.
    auto.

    rewrite find_mapsto_iff in maps_to'.
    rewrite <- e in maps_to'.
    match goal with 
      | [ H: ?a = Some ?b, H': ?a = None |- _ ] => assert (Some b = None) by (transitivity a; auto); discriminate
    end.

    subst item.
    match goal with
      | [ |- context [ add ?key ?value ?container ] ] => set (k := key); set (v := value)
    end.

    exists (benumerate v).

    split.

    unfold v.
    rewrite (binsert_enumerate _); auto.

    exists v; split; trivial.
    exists k.
    apply add_1; trivial.
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
    eauto using SetEq_Reflexive.

    (* No key provided *)

    simpl. unfold IndexedBag_benumerate, IndexedBag_bfind_matcher.
    rewrite flatten_filter.

    induction (Values (ifmap container)); simpl.

    compute; tauto.

    rewrite IHl.

    Lemma SetEq_app :
      forall {A: Type} (s1 t1 s2 t2: list A),
        (SetEq s1 s2) /\ (SetEq t1 t2) -> SetEq (s1 ++ t1) (s2 ++ t2).
    Proof.
      unfold SetEq; 
      intros A s1 t1 s2 t2 (s1s2 & t1t2); 
      split;
      rewrite ! in_app_iff;
      intro inApp;
      [ rewrite s1s2, t1t2 in inApp
      | rewrite <- s1s2, <- t1t2 in inApp ];
      trivial.
    Qed.

    apply SetEq_app; split; eauto using SetEq_Reflexive.
    apply bfind_correct.
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
      benumerate_empty  := IndexedBag_BagEnumerateEmpty projection;
      bfind_star        := IndexedBag_BagFindStar projection;
      bfind_correct     := IndexedBag_BagFindCorrect projection
    |}. 
End TreeBag.