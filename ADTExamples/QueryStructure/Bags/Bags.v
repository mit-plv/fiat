Require Import Program.
Require Import FMapInterface.
Require Import FMapAVL OrderedTypeEx.
Require Import Coq.FSets.FMapFacts.
Require Import FMapExtensions.

Unset Implicit Arguments.

Definition flatten {A} :=
  @List.fold_right (list A) (list A) (@List.app A) [].

Lemma in_flatten_iff :
  forall {A} x seqs, 
    @List.In A x (flatten seqs) <-> 
    exists seq, List.In seq seqs /\ List.In x seq.
Proof.
  intros; unfold flatten.
  induction seqs; simpl. 

  firstorder.
  rewrite in_app_iff.
  rewrite IHseqs.

  split.
  intros [ in_head | [seq (in_seqs & in_seq) ] ]; eauto.
  intros [ seq ( [ eq_head | in_seqs ] & in_seq ) ]; subst; eauto.
Qed.

Require Import SetEq.

Class Bag (TContainer TItem TSearchTerm: Type) :=
  {
    bempty        : TContainer;
    bstar         : TSearchTerm;
    bfind_matcher : TSearchTerm -> TItem -> bool;

    benumerate : TContainer -> list TItem;
    bfind      : TContainer -> TSearchTerm -> list TItem;
    binsert    : TContainer -> TItem -> TContainer;
    
    binsert_enumerate : forall item inserted container,
                          List.In item (benumerate (binsert container inserted)) <->
                          List.In item (benumerate container) \/ item = inserted;
    benumerate_empty  : forall item, ~ List.In item (benumerate bempty);
    bstar_search      : forall container, bfind container bstar = benumerate container;
    bfind_correct     : forall container search_term,
                          SetEq
                            (List.filter (bfind_matcher search_term) (benumerate container))
                            (bfind container search_term)
  }.

Module IndexedTree (Import M: WS).
  Module Import BasicFacts := WFacts_fun E M.
  Module Import BasicProperties := WProperties_fun E M.
  Module Import MoreFacts := FMapExtensions_fun E M.

  Definition TKey := key.

  Definition IndexedBagConsistency 
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
      iconsistency : IndexedBagConsistency projection ifmap
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

  Definition EmptyAsIndexedBag 
             (TBag TItem TBagSearchTerm: Type) 
             (bags_bag: Bag TBag TItem TBagSearchTerm) projection 
  : @IndexedBag TBag TItem TBagSearchTerm bags_bag projection.
    refine (
        {|
          ifmap        := empty TBag;
          iconsistency := _
        |}
      ).
    Proof. 
      unfold IndexedBagConsistency; 
      intros; rewrite empty_mapsto_iff in *; exfalso; trivial.
    Defined.

    Definition FindWithDefault {A} (key: TKey) (default: A) (fmap: t A) :=
      match find key fmap with
        | Some result => result
        | None        => default
      end.

    Definition Values {A} container :=
      List.map snd (@elements A container).

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
      unfold IndexedBagConsistency in consistent.
      eapply consistent; eauto.
    Qed.      

    Lemma FindWithDefault_dec :
      forall {A : Type} (key : TKey) (default : A) (fmap : t A),
        { exists result, 
            MapsTo key result fmap /\
            @FindWithDefault A key default fmap = result } +
        { find key fmap = None /\ 
          @FindWithDefault A key default fmap = default }.
    Proof.
      unfold FindWithDefault;
      intros A key default fmap; 
      destruct (find key fmap) eqn:find;
      [ left; rewrite <- find_mapsto_iff in find | right ];
      eauto.
    Qed.

    Lemma Values_empty :
      forall {A}, Values (empty A) = []. 
    Proof.
      intros;
      unfold Values;
      rewrite elements_empty;
      reflexivity.
    Qed.

    Instance IndexedBagAsBag 
             (TBag TItem TBagSearchTerm: Type) 
             (bags_bag: Bag TBag TItem TBagSearchTerm) projection 
    : Bag 
        (@IndexedBag TBag TItem TBagSearchTerm bags_bag projection) 
        TItem 
        ((option TKey) * TBagSearchTerm) :=
      {| 
        bempty := 
          EmptyAsIndexedBag TBag TItem TBagSearchTerm bags_bag projection;

        bstar  :=
          (None, @bstar _ _ _ bags_bag);

        bfind_matcher key_searchterm item :=
          let (key_option, search_term) := key_searchterm in
          match key_option with
            | Some k => KeyFilter k projection item
            | None   => true 
          end && (bfind_matcher search_term item);

        benumerate container :=
          flatten (List.map benumerate (Values (container.(ifmap))));

        bfind container key_searchterm :=
          let (key_option, search_term) := key_searchterm in
          match key_option with
            | Some k =>
              match find k container.(ifmap) with
                | Some bag => bag.(bfind) search_term
                | None     => []
              end
            | None   =>
              flatten (List.map (fun bag => bag.(bfind) search_term) (Values container.(ifmap)))
          end;

        binsert container item :=
          let k := projection item in
          let bag := FindWithDefault k bempty container.(ifmap) in
          {|
            ifmap := add k (bag.(binsert) item) container.(ifmap);
            iconsistency := _
          |}
      |}. 
    Proof.
      intros; simpl in *.

      unfold Values.
      setoid_rewrite in_flatten_iff.
      setoid_rewrite in_map_iff.
      setoid_rewrite <- MapsTo_snd.

      split; intro H.
      
      destruct H as [ items ( in_seq & [ bag (bag_items & [ key maps_to ]) ] ) ].
      pose proof maps_to as maps_to'.
      rewrite add_mapsto_iff in maps_to;
        destruct maps_to as [(is_eq & refreshed) | (neq & maps_to)].

      subst.
      rewrite binsert_enumerate in in_seq.
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

      Focus 2.
      unfold flatten, EmptyAsIndexedBag; simpl.
      rewrite Values_empty; tauto.
 
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
      rewrite binsert_enumerate; auto.

      exists v; split; trivial.
      exists k.
      apply add_1; trivial.

      intros; induction (Values (ifmap container)); simpl; trivial.
      rewrite (@bstar_search _ _ _ bags_bag).
      f_equal; trivial.


      intros.
      destruct search_term as (option_key, search_term).
      destruct option_key as [ key | ].

      (* Key provided *)

      pose (iconsistency container).
      unfold IndexedBagConsistency in i.


      Lemma filter_and :
        forall {A} pred1 pred2,
        forall (seq: list A),
          List.filter (fun x => pred1 x && pred2 x) seq =
          List.filter pred1 (List.filter pred2 seq).
      Proof.
        intros; 
        induction seq;
        simpl;
        [ | destruct (pred1 a) eqn:eq1; 
            destruct (pred2 a) eqn:eq2];
        simpl; 
        try rewrite eq1;
        try rewrite eq2;
        trivial;
        f_equal;
        trivial.
      Qed.

      Lemma filter_and_opp :
        forall {A} pred1 pred2,
        forall (seq: list A),
          List.filter (fun x => pred1 x && pred2 x) seq =
          List.filter pred2 (List.filter pred1 seq).
      Proof.
        intros; 
        induction seq;
        simpl;
        [ | destruct (pred1 a) eqn:eq1; 
            destruct (pred2 a) eqn:eq2];
        simpl; 
        try rewrite eq1;
        try rewrite eq2;
        trivial;
        f_equal;
        trivial.
      Qed.

      rewrite filter_and_opp.

      Lemma flatten_filter :
        forall {A} (seq: list (list A)) pred, 
          List.filter pred (flatten seq) =
          flatten (List.map (List.filter pred) seq). 
      Proof.
        intros; induction seq; trivial.
        unfold flatten; simpl.
        induction a; trivial.
        simpl; 
          destruct (pred a); simpl; rewrite IHa; trivial.
      Qed.

      rewrite flatten_filter.
      

        Lemma equiv_eq_key_elt :
          forall elt,
            Equivalence (eq_key_elt (elt:=elt)).
        Proof.
          intros; unfold eq_key_elt; intuition.
          unfold Symmetric; firstorder.
          unfold Transitive; firstorder.
          transitivity (fst y); trivial.
          transitivity (snd y); trivial.
        Qed.

        Lemma equiv_eq_key :
          forall elt,
            Equivalence (eq_key (elt:=elt)).
        Proof.
          intros; unfold eq_key; intuition.
          unfold Transitive; firstorder.
          transitivity (fst y); trivial.
        Qed.


        Lemma map_map :
          forall { A B C } (proc1: A -> B) (proc2: B -> C),
            forall seq,
            List.map proc2 (List.map proc1 seq) = List.map (fun x => proc2 (proc1 x)) seq.
        Proof.            
          intros; induction seq; simpl; f_equal; trivial.
        Qed.        
   
        Lemma InA_front_InA :
          forall elt,
          forall {item} front middle tail,
            InA (eq_key_elt (elt:=elt)) item front -> InA (eq_key_elt (elt:=elt)) item (front ++ middle :: tail).
        Proof.
          intros; intuition. 
          rewrite InA_app_iff;
            [intuition | apply equiv_eq_key_elt].
        Qed.

        Lemma InA_tail_InA :
          forall elt,
          forall {item} front middle tail,
            InA (eq_key_elt (elt:=elt)) item tail -> InA (eq_key_elt (elt:=elt)) item (front ++ middle :: tail).
        Proof.
          intros; intuition. 
          rewrite InA_app_iff;
            [intuition | apply equiv_eq_key_elt].
        Qed.

        Lemma InA_front_tail_InA :
          forall elt,
          forall {item} front middle tail,
            InA (eq_key_elt (elt:=elt)) item front \/ InA (eq_key_elt (elt:=elt)) item tail -> 
            InA (eq_key_elt (elt:=elt)) item (front ++ middle :: tail).
        Proof.
          intros elt item front middle tail in_or;
          destruct in_or; eauto using InA_front_InA, InA_tail_InA.
        Qed.
        
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
              | None => []
            end.
      Proof.          
        intros.
        
        pose (iconsistency container); unfold IndexedBagConsistency in i.
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

        Lemma filter_all_true :
          forall {A} pred (seq: list A),
            (forall x, List.In x seq -> pred x = true) ->
            List.filter pred seq = seq.
        Proof.
          induction seq as [ | head tail IH ]; simpl; trivial.
          intros all_true.
          rewrite all_true by eauto.
          f_equal; intuition.
        Qed.

        Lemma filter_all_false :
          forall {A} seq pred,
            (forall item : A, List.In item seq -> pred item = false) ->
            List.filter pred seq = [].
        Proof.
          intros A seq pred all_false; induction seq as [ | head tail IH ]; simpl; trivial.
          rewrite (all_false head) by (simpl; eauto). 
          intuition.
        Qed.

        Lemma map_filter_all_false :
          forall {A} pred seq, 
            (forall subseq, List.In subseq seq -> 
                            forall (item: A), List.In item subseq -> 
                                              pred item = false) ->
            (List.map (List.filter pred) seq) = (List.map (fun x => []) seq).
        Proof.
          intros A pred seq all_false; 
          induction seq as [ | subseq subseqs IH ] ; simpl; trivial.
          
          f_equal.

          specialize (all_false subseq (or_introl eq_refl)).
          apply filter_all_false; assumption.

          apply IH; firstorder.
        Qed.

        Lemma flatten_nils :
          forall {A} (seq: list (list A)),
            flatten (List.map (fun _ => []) seq) = @nil A.
        Proof.        
          induction seq; intuition. 
        Qed.

        Lemma flatten_app :
          forall {A} (seq1 seq2: list (list A)),
            flatten (seq1 ++ seq2) = flatten seq1 ++ flatten seq2.
        Proof.
          unfold flatten; induction seq1; simpl; trivial.
          intros; rewrite IHseq1; rewrite app_assoc; trivial.
        Qed.

        Lemma flatten_head :
          forall {A} head tail,
            @flatten A (head :: tail) = head ++ flatten tail.
        Proof.
          intuition.
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
            seq = [] <-> ~ exists (x: A), List.In x seq.
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

      rewrite consist.
      destruct (find key (ifmap container)) as [ bag | ].

      apply bfind_correct.
      eauto using SetEq_Reflexive.

      (* No key provided *)

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

      Grab Existential Variables.
      intros k' bag' maps_to item'.

      rewrite add_mapsto_iff in maps_to;
        destruct maps_to as [(is_eq & refreshed) | (neq & maps_to)];
        subst.

      rewrite binsert_enumerate.
      intro H; destruct H.
      apply (iconsistency container k' bag); trivial.    

      rewrite <- is_eq.
      unfold bag in *.

      destruct (FindWithDefault_dec k bempty (ifmap container))
        as [ [bag' (mapsto & equality)] | (not_found & equality) ];
        rewrite equality in *; clear equality.

      subst; trivial.
      exfalso; apply benumerate_empty in H; trivial.
      
      subst.
      unfold k in *. 
      trivial.

      apply (iconsistency container k' bag' maps_to item').
    Defined.
End IndexedTree.

Instance ListAsBag
         {TItem TSearchTerm: Type}
         (star: TSearchTerm)
         (matcher: TSearchTerm -> TItem -> bool)
         (star_search: forall (i: TItem), matcher star i = true)
: Bag (list TItem) TItem TSearchTerm.
Proof.
  refine (
      {| 
        bempty := [];
        bstar  := star;
        benumerate := id;
        bfind container search_term := List.filter (matcher search_term) container;
        binsert container item := cons item container
      |}
    ); simpl in *; intuition.

  unfold id.
  induction container; simpl; trivial.
  rewrite star_search, IHcontainer; trivial.
Defined.

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

Lemma eq_sym_iff :
  forall {A} x y, @eq A x y <-> @eq A y x.
Proof. split; intros; symmetry; assumption. Qed.

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
  (benumerate bempty) = []. 
Proof.
  pose proof (benumerate_empty) as not_in.
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
         (caching_bag: @CachingBag TBag TItem TSearchTerm bag_bag 
                                   TCachedValue initial_cached_value cache_updater 
                                   cache_updater_cacheable)
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
  simpl; intros; apply binsert_enumerate.
  simpl; intros; apply benumerate_empty.
  simpl; intros; apply bstar_search.
  simpl; intros; apply bfind_correct.

  Grab Existential Variables.

  rewrite (cache_updater_cacheable _ _ (binsert_enumerate_SetEq bag_bag _ _));
  simpl; setoid_rewrite cfresh_cache; reflexivity.

  rewrite benumerate_empty_eq_nil; reflexivity.
Qed.

Lemma in_nil_iff :
  forall {A} (item: A),
    List.In item [] <-> False.
Proof.
  intuition.
Qed.

Lemma in_not_nil :
  forall {A} x seq,
    @List.In A x seq -> seq <> nil.
Proof.
  intros A x seq in_seq eq_nil.
  apply (@in_nil _ x).
  subst seq; assumption.
Qed.

Lemma in_seq_false_nil_iff :
   forall {A} (seq: list A),
     (forall (item: A), (List.In item seq <-> False)) <-> 
     (seq = []).
Proof.
  intros.
  destruct seq; simpl in *; try tauto.
  split; intro H.
  exfalso; specialize (H a); rewrite <- H; eauto.
  discriminate.
Qed.

Lemma seteq_nil_nil :
  forall {A} seq,
    @SetEq A seq nil <-> seq = nil.
Proof.
  unfold SetEq.
  intros; destruct seq.

  tauto.
  split; [ | discriminate ].
  intro H; specialize (H a).
  exfalso; simpl in H; rewrite <- H; eauto.
Qed.

Lemma seteq_nil_nil' :
  forall {A} seq,
    @SetEq A nil seq <-> seq = nil.
Proof.
  setoid_rewrite SetEq_Symmetric_iff.
  intro; exact seteq_nil_nil.
Qed.

Section CacheableFunctions.
  Section Generalities.
    Lemma foldright_compose :
      forall {TInf TOutf TAcc} 
             (g : TOutf -> TAcc -> TAcc) (f : TInf -> TOutf) 
             (seq : list TInf) (init : TAcc),
        List.fold_right (compose g f) init seq =
        List.fold_right g init (List.map f seq).
    Proof.
      intros; 
      induction seq; 
      simpl; 
      [  | rewrite IHseq ];
      reflexivity.
    Qed.            

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
        @CachingBag TBag TItem TSearchTerm 
                    bag TCachedValue initial_cached_value 
                    (compose cache_updater cache_projection) 
                    (projection_cacheable cache_projection cache_updater initial_cached_value cache_updater_cacheable).
  End Generalities.

  Section MaxCacheable.
    Definition IsMax m seq :=
      (forall x, List.In x seq -> x <= m) /\ List.In m seq.

    Add Parametric Morphism (m: nat) :
      (IsMax m)
        with signature (@SetEq nat ==> iff)
          as IsMax_morphism.
    Proof.
      firstorder.
    Qed.

    Definition ListMax default seq :=
      List.fold_right max default seq.

    Lemma le_r_le_max : 
      forall x y z,
        x <= z -> x <= max y z.
    Proof.
      intros x y z;
      destruct (Max.max_spec y z) as [ (comp, eq) | (comp, eq) ]; 
      rewrite eq;
      omega.
    Qed.

    Lemma le_l_le_max : 
      forall x y z,
        x <= y -> x <= max y z.
    Proof.
      intros x y z. 
      rewrite Max.max_comm.
      apply le_r_le_max.
    Qed.

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
        [ | setoid_rewrite (SetEq_append _ _ init set_eq) ];
        apply ListMax_correct.
    Qed.
  End MaxCacheable.
End CacheableFunctions.

Require Import Tuple Heading.

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

Require Import Beatles.
Require Import StringBound.
Require Import Peano_dec.
Require Import String_as_OT.

Open Scope string_scope.
Open Scope Tuple_scope.

(*
Eval simpl in (bfind FirstAlbums [ TupleEqualityMatcher (eq_dec := string_dec) Name "Please Please Me" ]).
Eval simpl in (bfind FirstAlbums [ TupleEqualityMatcher (eq_dec := eq_nat_dec) Year 3]).
Eval simpl in (bfind FirstAlbums [ TupleEqualityMatcher (eq_dec := eq_nat_dec) Year 3; TupleEqualityMatcher (eq_dec := eq_nat_dec) UKpeak 1]).
*)

Module NatIndexedMap := FMapAVL.Make Nat_as_OT.
Module StringIndexedMap := FMapAVL.Make String_as_OT.

Module NatTreeExts := IndexedTree NatIndexedMap.
Module StringTreeExts := IndexedTree StringIndexedMap.

Definition NatTreeType TSubtree TSubtreeSearchTerm heading subtree_as_bag := 
  (@NatTreeExts.IndexedBag 
     TSubtree 
     (@Tuple heading) 
     TSubtreeSearchTerm 
     subtree_as_bag).

Definition StringTreeType TSubtree TSubtreeSearchTerm heading subtree_as_bag := 
  (@StringTreeExts.IndexedBag 
     TSubtree 
     (@Tuple heading) 
     TSubtreeSearchTerm
     subtree_as_bag).

Definition cast {T1 T2: Type} (eq: T1 = T2) (x: T1) : T2.
Proof.
  subst; auto.
Defined.

Record BagPlusBagProof heading :=
  { BagType: Type; SearchTermType: Type; BagProof: Bag BagType (@Tuple heading) SearchTermType }.

Record ProperAttribute {heading} :=
  {
    Attribute: Attributes heading; 
    ProperlyTyped: { Domain heading Attribute = nat } + { Domain heading Attribute = string }
  }.

Fixpoint NestedTreeFromAttributes'
         heading 
         (indexes: list (@ProperAttribute heading)) 
         {struct indexes}: BagPlusBagProof heading :=
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

Lemma eq_attributes : forall seq (a b: @BoundedString seq),
             a = b <-> (bindex a = bindex b /\ (ibound (indexb a)) = (ibound (indexb b))).
  split; intros; 
  simpl in *;
  try (subst; tauto);
  apply idx_ibound_eq; 
    intuition (apply string_dec).
Qed.

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

Definition SampleIndex : BagPlusBagProof AlbumHeading.
Proof.
  mkIndex AlbumHeading [Year; UKpeak; Name].
Defined.

Definition IndexedAlbums :=
  List.fold_left binsert FirstAlbums (@bempty _ _ _ (BagProof _ SampleIndex)).
(*
Eval simpl in (SearchTermType AlbumHeading SampleIndex).
Time Eval simpl in (bfind IndexedAlbums (Some 3, (None, (None, [])))).
Time Eval simpl in (bfind IndexedAlbums (Some 3, (Some 1, (None, [])))).
Time Eval simpl in (bfind IndexedAlbums (Some 3, (Some 1, (Some "With the Beatles", [])))).
Time Eval simpl in (bfind IndexedAlbums (None, (None, (Some "With the Beatles", [])))).
Time Eval simpl in (bfind IndexedAlbums (None, (None, (None, [TupleEqualityMatcher (eq_dec := string_dec) Name "With the Beatles"])))).

(*Time Eval simpl in (@bfind _ _ _ (BagProof _ SampleIndex) IndexedAlbums (Some 3, (Some 1, (None, @nil (TSearchTermMatcher AlbumHeading))))).*)
*)

(*
  simpl.
  unfold bfind.
  unfold IndexedAlbums.
  unfold BagProof.
  unfold SampleIndex.
  unfold NestedTreeFromAttributes'.
  unfold right_type.
  unfold CheckType.
  unfold bempty.
  simpl attribute.
  unfold StringTreeType.
  unfold NatTreeType.
  unfold fold_left.
  unfold FirstAlbums.
  progress simpl NatTreeExts.IndexedBagAsBag.
  (*progress simpl StringTreeExts.IndexedBagAsBag.*)
  unfold NatTreeExts.IndexedBagAsBag.
  simpl.
*)
