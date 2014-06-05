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

Ltac ProveDecidability indices :=
  refine (NestedTreeFromAttributes' AlbumHeading indices _);
  intros attr in_indices; simpl in *;
  setoid_rewrite eq_attributes in in_indices;

  destruct attr as [bindex indexb];
  destruct indexb as [ibound boundi];
  simpl in *;

  repeat match goal with 
           | [ |- _ ] => 
             destruct ibound as [ | ibound ];
               [ try (exfalso; omega); solve [eauto] | try discriminate ]
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
  set (source := attributes);
  assert (list (@ProperAttribute heading)) as decorated_source;
  autoconvert (@CheckType heading);
  apply (NestedTreeFromAttributes' heading decorated_source).

Definition SampleIndex : BagPlusBagProof AlbumHeading.
Proof.
  mkIndex AlbumHeading [Year; UKpeak; Name].
Defined.

Definition SampleIndex' : BagPlusBagProof AlbumHeading.
Proof.
  refine (NestedTreeFromAttributes' AlbumHeading [CheckType Year _; CheckType UKpeak _; CheckType Name _]);   eauto.
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
