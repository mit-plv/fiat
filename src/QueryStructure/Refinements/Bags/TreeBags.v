Require Export BagsInterface BagsProperties.
Require Import SetEqProperties FMapExtensions AdditionalLemmas AdditionalPermutationLemmas.
Require Import FMapInterface Coq.FSets.FMapFacts.

Unset Implicit Arguments.


Module TreeBag (Import M: WS).
  Module Import BasicFacts := WFacts_fun E M.
  Module Import BasicProperties := WProperties_fun E M.
  Module Import MoreFacts := FMapExtensions_fun E M.

  Definition TKey := key.

  Section TreeBagDefinitions.

    Context {TBag : Type}
            {TItem : Type}
            {TBagSearchTerm : Type}
            {TBagUpdateTerm : Type}.
    Variable (projection: TItem -> TKey).

    (* A class for Bags whose update functions preserve the key *)
    Class KeyPreservingUpdateBag :=
      { KeyPreserving_bag :> Bag TBag TItem TBagSearchTerm TBagUpdateTerm;
        KeyPreserving_Proof :
          forall K item updateTerm searchTerm,
            E.eq (projection item) K
            -> bfind_matcher searchTerm item = true
            -> E.eq (projection (bupdate_transform updateTerm item)) K }.

    Variables (bags_bag: KeyPreservingUpdateBag).

    Definition IndexedTreeConsistency fmap :=
      forall (key: TKey) (bag: TBag),
        MapsTo key bag fmap ->
        forall (item: TItem),
          List.In item (benumerate bag) ->
          E.eq (projection item) key.

    Record IndexedBag :=
      { ifmap        : t TBag;
        iconsistency : IndexedTreeConsistency ifmap
      }.

    Definition KeyFilter (key: TKey) :=
      (fun x : TItem => if E.eq_dec (projection x) key then true else false).

    Lemma KeyFilter_beq :
      forall beq,
        (forall x y, reflect (E.eq x y) (beq x y)) ->
        (forall key (item: TItem),
           KeyFilter key item = beq (projection item) key).
    Proof.
      intros beq spec key item.
      specialize (spec (projection item) key).
      unfold KeyFilter.
      destruct spec as [ is_eq | neq ];
        destruct (F.eq_dec _ _); intuition.
    Qed.

    Lemma iconsistency_empty :
      IndexedTreeConsistency (empty TBag).
    Proof.
      unfold IndexedTreeConsistency;
      intros; rewrite empty_mapsto_iff in *; exfalso; trivial.
    Qed.

    Lemma consistency_key_eq :
      forall (container : IndexedBag),
      forall (key: TKey) bag item,
        MapsTo key bag (ifmap container) ->
        List.In item (benumerate bag) ->
        E.eq (projection item) key.
    Proof.
      intros.
      destruct container as [? consistent].
      unfold IndexedTreeConsistency in consistent.
      eapply consistent; eauto.
    Qed.

    Ltac destruct_if :=
      match goal with
          [ |- context [ if ?cond then _ else _ ] ] => destruct cond
      end.

    Lemma KeyFilter_true :
      forall k item,
        KeyFilter k item = true <-> E.eq (projection item) k.
    Proof.
      unfold KeyFilter; intros;
      destruct_if; intros; intuition.
    Qed.

    Lemma KeyFilter_false :
      forall k item,
        KeyFilter k item = false <-> ~ E.eq (projection item) k.
    Proof.
      unfold KeyFilter; intros;
      destruct_if; intros; intuition.
    Qed.

    Definition IndexedBag_bempty :=
      {| ifmap        := empty TBag;
         iconsistency := iconsistency_empty |}.

    Definition IndexedBag_bstar :=
      (@None TKey, bstar (Bag := KeyPreserving_bag)).

    Definition IndexedBag_bid :=
      (@None TKey, bid (Bag := KeyPreserving_bag)).

    Definition IndexedBag_bfind_matcher
               (key_searchterm: (option TKey) * TBagSearchTerm) (item: TItem) :=
      let (key_option, search_term) := key_searchterm in
      match key_option with
        | Some k => KeyFilter k item
        | None   => true
      end && (bfind_matcher search_term item).

    Definition IndexedBag_benumerate
               (container: IndexedBag) :=
      flatten (List.map benumerate (Values (ifmap container))).

    Definition IndexedBag_bfind
               (container: IndexedBag)
               (key_searchterm: (option TKey) * TBagSearchTerm) :=
      let (key_option, search_term) := key_searchterm in
      match key_option with
        | Some k =>
          match find k (ifmap container) with
            | Some bag => bfind (Bag := KeyPreserving_bag) bag search_term
            | None     => nil
          end
        | None   =>
          flatten (List.map (fun bag => bfind (Bag := KeyPreserving_bag) bag search_term) (Values (ifmap container)))
      end.

    Lemma InA_mapsto_add {Value} :
      forall bag' kv k' (v' : Value),
        InA (@eq_key_elt _) kv (elements (add k' v' bag')) ->
        eq_key_elt kv (k', v') \/
        (~ E.eq (fst kv) k' /\
         InA (@eq_key_elt _) kv (elements bag')).
    Proof.
      intros.
      destruct kv as [k v]; apply elements_2 in H.
      apply add_mapsto_iff in H; intuition; subst;
      [left; split; simpl; eauto |
       right; eauto using elements_1].
    Qed.

    Lemma InA_mapsto_add' {Value} :
      forall bag' kv k' (v' : Value),
        (eq_key_elt kv (k', v') \/
         (~ E.eq (fst kv) k' /\
          InA (@eq_key_elt _) kv (elements bag')))
        -> InA (@eq_key_elt _) kv (elements (add k' v' bag')).
    Proof.
      intros; destruct kv as [k v]; apply elements_1;
      apply add_mapsto_iff; intuition;
      [destruct H0; eauto
      | right; intuition; apply elements_2; eauto].
    Qed.

    Lemma InA_app_swap {A} eqA :
      Equivalence eqA
      -> forall (a : A) l l',
           InA eqA a (l ++ l') -> InA eqA a (l' ++ l).
    Proof.
      intros; eapply InA_app_iff;
      eapply InA_app_iff in H0; eauto; intuition.
    Qed.

    Lemma InA_app_cons_swap {A} eqA :
      Equivalence eqA
      -> forall (a a' : A) l l',
           InA eqA a (l ++ (a' :: l')) <-> InA eqA a ((a' :: l) ++ l').
    Proof.
      split; intros.
      - eapply InA_app_swap; eauto.
        intros; eapply InA_app_iff;
        eapply InA_app_iff in H0; eauto; intuition.
        inversion H; subst; eauto.
      - eapply InA_app_swap; eauto.
        intros; eapply InA_app_iff;
        eapply InA_app_iff in H0; eauto; intuition.
        inversion H; subst; eauto.
    Qed.

    Lemma Permutation_InA_cons {Value} :
      forall l (l' : list (key * Value)),
        NoDupA (@eq_key _) l
        -> NoDupA (@eq_key _) l'
        -> (forall k v,
              InA (@eq_key_elt _) (k, v) l' <->
              (InA (@eq_key_elt _) (k, v) l))
        -> Permutation (List.map snd l')
                       (List.map snd l).
    Proof.
      induction l; intros.
      destruct l'.
      constructor.
      assert (InA (eq_key_elt (elt:=Value)) (fst p, snd p) []) as H2
                                                                 by (eapply H1; left; split; reflexivity); inversion H2.
      destruct a as [k v].
      assert (InA (eq_key_elt (elt:=Value)) (k, v) l') as H2
                                                         by (eapply H1; econstructor; split; reflexivity).
      destruct (InA_split H2) as [l'1 [kv [l'2 [eq_kv eq_l]]]]; subst.
      rewrite <- Permutation_middle; simpl.
      destruct eq_kv; simpl in *; subst; constructor.
      eapply NoDupA_swap in H0; eauto using eqk_equiv.
      inversion H0; inversion H; subst; apply IHl; eauto.
      assert (forall (k0 : key) (v : Value),
                InA (eq_key_elt (elt:=Value)) (k0, v) (kv :: (l'1 ++ l'2)) <->
                InA (eq_key_elt (elt:=Value)) (k0, v) ((k, snd kv) :: l)) by
          (split; intros;
           [ eapply H1; eapply InA_app_cons_swap
           | eapply H1 in H4; eapply InA_app_cons_swap in H4 ]; eauto using eqke_equiv).
      split; intros.
      + generalize (proj1 (H4 k0 v) (InA_cons_tl _ H5)); intros.
        inversion H8; subst; eauto.
        destruct H12; simpl in *.
        elimtype False; apply H6.
        revert H5 H9 H3; clear; induction (l'1 ++ l'2); intros;
        inversion H5; subst;
        [ constructor; destruct H0; simpl in *; unfold eq_key;
          rewrite <- H3, <- H9; eauto
        | constructor 2; eauto ].
      + generalize (proj2 (H1 k0 v) (InA_cons_tl _ H5)); intros.
        eapply InA_app_cons_swap in H8; eauto using eqke_equiv.
        inversion H8; subst; eauto.
        destruct H12; simpl in *.
        elimtype False; apply H10.
        revert H5 H9 H3; clear; induction l; intros;
        inversion H5; subst;
        [ constructor; destruct H0; simpl in *; unfold eq_key;
          simpl; rewrite <- H, H9; eauto
        | constructor 2; eauto ].
    Qed.

    Lemma FMap_Insert_fold_add {Value}
    : forall (f : Value -> Value) (bag : t Value) bag',
        (forall (k : key), InA E.eq k (List.map fst (elements bag))
                           -> ~ In k bag')
        -> Permutation
             (List.map snd (elements (fold (fun k bag'' r' => add k (f bag'') r')
                                           bag bag')))
             (List.map snd ((List.map (fun kv => (fst kv, f (snd kv))) (elements bag)) ++ elements bag')).
    Proof.
      intros.
      intros; rewrite fold_1.
      generalize (elements_3w bag) as NoDupl.
      revert bag' H; induction (elements bag); simpl; intros.
      reflexivity.
      rewrite IHl, Permutation_cons_app;
        try (rewrite List.map_app; reflexivity).
      rewrite List.map_app, List.map_map.
      apply Permutation_app; try reflexivity.
      apply (Permutation_InA_cons ((fst a, f (snd a)) :: elements bag'));
        eauto using elements_3w.
      econstructor; eauto using elements_3w.
      unfold not; intros; eapply (H (fst a));
      [ constructor; reflexivity
      | eapply elements_in_iff; revert H0; clear; intro; induction H0].
      repeat econstructor; eauto.
      destruct IHInA; econstructor; econstructor 2; eauto.
      split; intros.
      apply InA_mapsto_add in H0; intuition.
      inversion H0; subst; eapply InA_mapsto_add'; intuition.
      right; intuition.
      eapply H; simpl.
      econstructor; reflexivity.
      eapply elements_in_iff; revert H2 H1; clear; intros;
      induction H2.
      destruct H; repeat econstructor; eauto.
      destruct IHInA; econstructor; econstructor 2; eauto.
      unfold not; intros.
      apply add_in_iff in H1; destruct H1.
      inversion NoDupl; subst; rewrite <- H1 in H0; eapply H4.
      revert H0; clear; induction l; intros; inversion H0; subst.
      constructor; eauto.
      econstructor 2; eauto.
      eapply H; eauto.
      inversion NoDupl; eauto.
    Qed.

    Lemma FMap_fold_add_MapsTo_NIn {Value}
    : forall (f : Value -> Value) l k v bag',
        ~ InA (@eq_key _) (k,v) (List.map (fun kv => (fst kv, f (snd kv))) l)
        -> (MapsTo k v (fold_left (fun a p => add (fst p) (f (snd p)) a) l bag')
            <-> MapsTo k v bag').
    Proof.
      unfold eq_key; intros; revert k v bag' H.
      induction l; simpl; intros; split; eauto.
      intros; assert (MapsTo k v (add (fst a) (f (snd a)) bag')).
      apply IHl;
        [unfold not; intros; apply H; constructor 2; eauto
        | eauto].
      apply add_mapsto_iff in H1; intuition; subst.
      intros; eapply IHl; eauto using add_2.
    Qed.

    Lemma FMap_fold_add_MapsTo_In {Value}
    : forall (f : Value -> Value) (bag : t Value) bag' k v,
        InA (@eq_key_elt _) (k,v) (List.map (fun kv => (fst kv, f (snd kv))) (elements bag))
        -> MapsTo k v
                  (fold (fun k bag'' r' => add k (f bag'') r') bag bag').
    Proof.
      intros; rewrite fold_1 in *; revert k v bag' H;
      generalize (elements_3w bag); induction (elements bag);
      intros; inversion H0; inversion H; subst; simpl in *; eauto.
      destruct H2; simpl in *; subst; rewrite H1.
      apply FMap_fold_add_MapsTo_NIn; eauto.
      unfold not, eq_key in *; intros; apply H6; revert H2; clear;
      induction l; simpl in *; intros; inversion H2; subst; eauto.
      apply add_1; reflexivity.
    Qed.

    Lemma FMap_Insert_fold_add_MapsTo {Value}
    : forall (f : Value -> Value) (bag : t Value) bag' k v,
        MapsTo k v
               (fold (fun k bag'' r' => add k (f bag'') r') bag bag') ->
        MapsTo k v bag' \/
        InA (@eq_key_elt _) (k,v) (List.map (fun kv => (fst kv, f (snd kv))) (elements bag)).
    Proof.
      intros; rewrite fold_1 in *; revert bag' H;
      induction (elements bag); simpl in *; eauto; intros.
      apply IHl in H; intuition.
      apply add_mapsto_iff in H0; intuition; subst.
      right; constructor; split; eauto.
    Qed.

    Lemma InA_Map {A B} eqB
    : forall (f : A -> B) (b : B) (l : list A),
        InA eqB b (List.map f l) <->
        exists a, eqB b (f a) /\ List.In a l.
    Proof.
      split; induction l; simpl; intros; inversion H; subst;
      eauto. destruct (IHl H1) as [a' [In_a eq_b]]; eauto.
      intuition.
      intuition; subst.
      constructor; eauto.
      constructor 2; eauto.
    Qed.

    Lemma FMap_Insert_fold_add_map_eq {Value}
    : forall (f : Value -> Value) (bag : t Value),
        Equal
          (fold (fun k bag'' r' => add k (f bag'') r') bag (empty _))
          (map f bag).
    Proof.
      unfold Equal.
      intros; case_eq (find y
                            (fold
                               (fun (k : key) (bag'' : Value) (r' : t Value) => add k (f bag'') r')
                               bag (empty Value)));
      intros; case_eq (find y (map f bag)); intros; eauto.
      - apply find_2 in H; apply find_2 in H0.
        apply FMap_Insert_fold_add_MapsTo in H; destruct H.
        elimtype False; apply empty_mapsto_iff in H; eauto.
        apply map_mapsto_iff in H0; destruct H0 as [a [eq_a MapsTo_y]]; subst.
        generalize (elements_3w bag); apply elements_1 in MapsTo_y;
        induction MapsTo_y; intros.
        + inversion H1; subst; destruct H0; simpl in *; subst.
          inversion H; subst;
          [destruct H3; simpl in *; subst; eauto
          | elimtype False; apply H4; revert H0 H3; clear; induction l;
            intros; inversion H3; subst; unfold eq_key in *].
          destruct H1; simpl in *; subst; constructor; eauto.
          constructor 2; eauto.
        + inversion H0; subst; eapply IHMapsTo_y; eauto.
          inversion H; subst; eauto.
          destruct H2; simpl in *; subst.
          elimtype False; apply H3; revert H1 MapsTo_y; clear; induction l;
          intros; inversion MapsTo_y; subst; unfold eq_key in *.
          destruct H0; simpl in *; subst; constructor; eauto.
          constructor 2; eauto.
      - apply find_2 in H; apply FMap_Insert_fold_add_MapsTo in H; destruct H.
        elimtype False; apply empty_mapsto_iff in H; eauto.
        apply InA_Map in H; destruct H as [[k v'] [eq_k In_k]]; simpl in *.
        destruct eq_k; simpl in *; rewrite H in H0.
        apply not_find_in_iff in H0; elimtype False; eapply H0.
        apply map_in_iff; exists v'; apply elements_2.
        apply InA_alt; eexists; repeat split; eauto.
      - apply find_2 in H0; apply not_find_in_iff in H.
        apply map_mapsto_iff in H0; destruct H0 as [k [k_eq MapsTo_k]]; subst.
        elimtype False; apply H.
        econstructor 1 with (x := f k); apply FMap_fold_add_MapsTo_In.
        apply elements_1 in MapsTo_k; revert MapsTo_k; clear;
        intro; induction MapsTo_k; simpl.
        repeat constructor; destruct H; simpl in *; subst; eauto.
        constructor 2; eauto.
    Qed.

    Definition IndexedBag_bdelete'
               (container: IndexedBag)
               (key_searchterm: (option TKey) * TBagSearchTerm)
    : (list TItem) * (t TBag) :=
      let (key_option, search_term) := key_searchterm in
      match key_option with
        | Some k => (match find k (ifmap container) with
                       | Some bag => benumerate (Bag := KeyPreserving_bag) bag
                       | None => nil
                     end, @remove TBag k (ifmap container))
        | None => fold (fun k bag (res : (list TItem) * (t TBag)) =>
                          match bdelete (Bag := KeyPreserving_bag) bag search_term with
                            | (d, r) => let (d', r') := res in
                                        (d ++ d', add k r r')
                          end) (ifmap container) ([], empty TBag)
      end.

    Lemma In_partition {A}
    : forall f (l : list A) a,
        List.In a l <-> (List.In a (fst (List.partition f l))
                         \/ List.In a (snd (List.partition f l))).
    Proof.
      split; induction l; simpl; intros; intuition; simpl; subst;
      first [destruct (f a0); destruct (List.partition f l); simpl in *; intuition
            | destruct (f a); destruct (List.partition f l); simpl; intuition].
    Qed.

    Lemma In_partition_matched {A}
    : forall f (l : list A) a,
        List.In a (fst (List.partition f l)) ->
        f a = true.
    Proof.
      induction l; simpl; intros; intuition; simpl; subst; eauto.
      case_eq (f a); destruct (List.partition f l); simpl; intuition;
      rewrite H0 in H; eauto; inversion H; subst; eauto.
    Qed.

    Lemma In_partition_unmatched {A}
    : forall f (l : list A) a,
        List.In a (snd (List.partition f l)) ->
        f a = false.
    Proof.
      induction l; simpl; intros; intuition; simpl; subst; eauto.
      case_eq (f a); destruct (List.partition f l); simpl; intuition;
      rewrite H0 in H; eauto; inversion H; subst; eauto.
    Qed.

    Lemma IndexedBag_bdelete_consistent
          (container: IndexedBag)
          (key_searchterm: (option TKey) * TBagSearchTerm)
    : IndexedTreeConsistency (snd (IndexedBag_bdelete' container key_searchterm)).
    Proof.
      intros; destruct key_searchterm; destruct o; simpl in *;
      unfold IndexedTreeConsistency; intros.
      - apply remove_3 in H; eapply iconsistency; eauto.
      - destruct container as [bag' WF_bag']; simpl in *.
        assert (forall l,
                  snd
                    (fold_left
                       (fun (a : list TItem * t TBag) (p : key * TBag) =>
                          let (d, r) := bdelete (snd p) t0 in
                          let (d', r') := a in (d ++ d', add (fst p) r r'))
                       (elements bag') l)
                  = fold_left
                      (fun (a : t TBag) (p : key * TBag) =>
                         add (fst p) (snd (bdelete (snd p) t0))a)
                      (elements bag') (snd l)).
        { induction (elements bag'); simpl in *; eauto.
          intros; rewrite IHl; destruct l0;
          destruct (bdelete (snd a) t0); simpl; reflexivity. }
        assert (MapsTo key0 bag
                       (fold
                          (fun (k : key) (bag0 : TBag) (r' : t TBag) =>
                             add k (snd (bdelete bag0 t0)) r') bag'
                          (empty TBag)))
          by (rewrite fold_1, H1 in H; simpl in H;  rewrite fold_1; eauto); clear H H1.
        rewrite FMap_Insert_fold_add_map_eq in H2.
        apply map_mapsto_iff in H2; destruct H2 as [k [k_eq MapsTo_k]]; subst.
        eapply WF_bag'; eauto.
        destruct (bdelete_correct k t0).
        eapply In_partition; right; eapply Permutation_in; eauto.
    Defined.

    Definition IndexedBag_bdelete
               (container: IndexedBag)
               (key_searchterm: (option TKey) * TBagSearchTerm)
    : ((list TItem) * IndexedBag) :=
      match IndexedBag_bdelete' container key_searchterm as l
            return IndexedTreeConsistency (snd l) -> ((list TItem) * IndexedBag) with
        | (deleted, container') =>
          fun i => (deleted, {|ifmap := container';
                               iconsistency := i |})
      end (IndexedBag_bdelete_consistent container key_searchterm).

    Definition IndexedBag_bupdate'
               (container: IndexedBag)
               (key_searchterm: (option TKey) * TBagSearchTerm)
               (updateTerm : TBagUpdateTerm)
    : (t TBag) :=
      let (key_option, search_term) := key_searchterm in
      match key_option with
        | Some k => match find k (ifmap container) with
                      | Some bag => add k (bupdate bag search_term updateTerm) (ifmap container)
                      | None => (ifmap container)
                    end
        | None => map (fun bag => bupdate bag search_term updateTerm) (ifmap container)
      end.

    Lemma IndexedBag_bupdate'_consistent
          (container : IndexedBag)
          (key_searchterm: (option TKey) * TBagSearchTerm)
          (updateTerm : TBagUpdateTerm)
    : IndexedTreeConsistency (IndexedBag_bupdate' container key_searchterm updateTerm).
    Proof.
      intros; destruct key_searchterm; destruct o; simpl in *.
      - case_eq (find t1 (ifmap container)); intros; eauto using iconsistency.
        unfold IndexedTreeConsistency; intros.
        apply add_mapsto_iff in H0; intuition.
        + pose proof (bupdate_correct t2 t0 updateTerm).
          rewrite <- H3 in H1.
          apply find_2 in H; rewrite <- H0.
          pose proof (Permutation_in _ H2 H1) as H4;
            apply in_app_or in H4; destruct H4.
          * pose proof ((proj2 (In_partition _ _ _)) (or_intror H4));
            eapply iconsistency; eauto.
          * apply in_map_iff in H4; destruct H4 as [item' [item'_eq In_item']].
            pose proof (iconsistency _ _ _ H _
                                     ((proj2 (In_partition _ _ _)) (or_introl In_item'))).
            rewrite <- H4.
            rewrite <- item'_eq.
            eapply KeyPreserving_Proof; eauto using In_partition_matched.
        + eapply iconsistency; eauto.
      - unfold IndexedTreeConsistency; intros.
        apply map_mapsto_iff in H;
          destruct H as [bag' [bag'_eq MapsTo_key0]]; subst.
        pose proof (bupdate_correct bag' t0 updateTerm).
        pose proof (Permutation_in _ H H0) as H4;
          apply in_app_or in H4; destruct H4.
        + pose proof ((proj2 (In_partition _ _ _)) (or_intror H1));
          eapply iconsistency; eauto.
        + apply in_map_iff in H1; destruct H1 as [item' [item'_eq In_item']].
          pose proof (iconsistency _ _ _ MapsTo_key0 _
                                   ((proj2 (In_partition _ _ _)) (or_introl In_item'))).
          rewrite <- H1.
          rewrite <- item'_eq.
          eapply KeyPreserving_Proof; eauto using In_partition_matched.
    Defined.

    Definition IndexedBag_bupdate
               (container: IndexedBag)
               (key_searchterm: (option TKey) * TBagSearchTerm)
               (updateTerm : TBagUpdateTerm)
    : IndexedBag :=
      {| ifmap := IndexedBag_bupdate' container key_searchterm updateTerm;
         iconsistency := IndexedBag_bupdate'_consistent container key_searchterm updateTerm |}.

    Definition IndexedBag_bcount
               (container: IndexedBag)
               (key_searchterm: (option TKey) * TBagSearchTerm) :=
      let (key_option, search_term) := key_searchterm in
      match key_option with
        | Some k =>
          match find k (ifmap container) with
            | Some bag => bcount (Bag := KeyPreserving_bag) bag search_term
            | None     => 0
          end
        | None   =>
          fold (fun _ bag acc => acc + bcount (Bag := KeyPreserving_bag) bag search_term)
               (ifmap container) 0
      end.

    Lemma indexed_bag_insert_consistent :
      forall (container: IndexedBag)
             (item: TItem),
        let k := projection item in
        let fmap := ifmap container in
        let bag := FindWithDefault k bempty fmap in
        IndexedTreeConsistency (add k (binsert bag item) fmap).
    Proof.
      intros.

      intros k' bag' maps_to item'.

      rewrite add_mapsto_iff in maps_to;
        destruct maps_to as [(is_eq & refreshed) | (neq & maps_to)];
        subst.

      rewrite (binsert_enumerate_weak item' item bag).
      intro H; destruct H.
      apply ((iconsistency container) k' bag); trivial.

      rewrite <- is_eq.
      unfold bag in *.

      unfold fmap in *.
      destruct (FindWithDefault_dec k (bempty (Bag := KeyPreserving_bag)) (ifmap container))
        as [ [bag' (mapsto & equality)] | (not_found & equality) ];
        rewrite equality in *; clear equality.

      subst; trivial.
      exfalso; apply (benumerate_empty) in H; trivial.

      subst.
      unfold k in *.
      trivial.

      apply ((iconsistency container) k' bag' maps_to item').
    Qed.

    Definition IndexedBag_binsert
               (container: IndexedBag)
               (item: TItem) : IndexedBag :=
      let k := projection item in
      let fmap := ifmap container in
      let bag := FindWithDefault k bempty fmap in
      {|
        ifmap := add k (binsert bag item) fmap;
        iconsistency := indexed_bag_insert_consistent container item
      |}.

    Add Parametric Morphism {A} :
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
      forall (m: t TBag),
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
      BagInsertEnumerate IndexedBag_benumerate IndexedBag_binsert.
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

    Lemma fold_plus_sym :
      forall (seq: list nat) (default: nat),
        List.fold_right plus default seq =
        List.fold_left plus seq default.
    Proof.
      intros; rewrite <- fold_left_rev_right.
      revert default; induction seq; simpl; eauto; intros.
      rewrite fold_right_app; simpl; rewrite <- IHseq.
      clear IHseq; revert a default; induction seq;
      simpl; intros; auto with arith.
      rewrite <- IHseq; omega.
    Qed.


    Lemma IndexedBag_BagCountCorrect :
      BagCountCorrect IndexedBag_bcount IndexedBag_bfind .
    Proof.
      unfold IndexedBag_bcount, IndexedBag_bfind, BagCountCorrect;
      simpl; intros; destruct search_term as [ [ key | ] search_term ].

      + destruct (find _ _); eauto using bcount_correct.
      + rewrite length_flatten.
        rewrite (fold_over_Values _ _ (fun acc bag => acc + bcount bag search_term)) by eauto.
        rewrite <- fold_left_rev_right.
        setoid_rewrite Plus.plus_comm at 1.
        replace (fun (y : TBag) (x : nat) => bcount y search_term + x)
        with (compose plus (fun bag => bcount bag search_term)) by reflexivity.
        rewrite !foldright_compose.

        symmetry; setoid_rewrite <- rev_involutive at 1.
        rewrite fold_left_rev_right, map_rev, rev_involutive.

        rewrite fold_plus_sym, <- !fold_map.
        setoid_rewrite bcount_correct.
        f_equal;
          repeat (apply functional_extensionality; intros);
          auto with arith.
    Qed.

    Lemma IndexedBag_BagEnumerateEmpty :
      BagEnumerateEmpty IndexedBag_benumerate IndexedBag_bempty.
    Proof.
      intros;
      unfold BagEnumerateEmpty, IndexedBag_benumerate, flatten; simpl;
      rewrite Values_empty; tauto.
    Qed.

    Lemma IndexedBag_BagFindStar :
      BagFindStar IndexedBag_bfind IndexedBag_benumerate IndexedBag_bstar.
    Proof.
      unfold BagFindStar, IndexedBag_benumerate; simpl.

      intros; induction (Values (ifmap container)); simpl; trivial.
      rewrite bfind_star.
      f_equal; trivial.
    Qed.

    Lemma IndexedBag_BagFindCorrect :
      BagFindCorrect IndexedBag_bfind IndexedBag_bfind_matcher IndexedBag_benumerate.
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
          (container: IndexedBag),
        forall k,
          eq
            (flatten
               (List.map (List.filter (KeyFilter k))
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

    (* Lemma IndexedBag_BagDeleteCorrect :
      BagDeleteCorrect IndexedBag_bfind IndexedBag_bfind_matcher
        IndexedBag_benumerate IndexedBag_bdelete.
    Proof.
      unfold BagDeleteCorrect, IndexedBag_bfind, IndexedBag_bfind_matcher,
      IndexedBag_benumerate, IndexedBag_bdelete, IndexedBag_bdelete'.
      simpl; intros; case_eq search_term; intros;  case_eq o; simpl; intros; subst.
      pose proof (bdelete_correct ).
      case_eq (find t1 (ifmap container)); intros.

      unfold BagDeleteCorrect in H.
      Check (H (ifmap
IndexedBag_bcount, IndexedBag_bfind, BagCountCorrect;
      simpl; intros; destruct search_term as [ [ key | ] search_term ].

      + destruct (find _ _); eauto using bcount_correct.
      + rewrite length_flatten.
        rewrite (fold_over_Values _ _ (fun acc bag => acc + bcount bag search_term)) by eauto.
        rewrite <- fold_left_rev_right.
        setoid_rewrite Plus.plus_comm at 1.
        replace (fun (y : TBag) (x : nat) => bcount y search_term + x)
        with (compose plus (fun bag => bcount bag search_term)) by reflexivity.
        rewrite !foldright_compose.

        symmetry; setoid_rewrite <- rev_involutive at 1.
        rewrite fold_left_rev_right, map_rev, rev_involutive.

        rewrite fold_plus_sym, <- !fold_map.
        setoid_rewrite bcount_correct.
        f_equal;
          repeat (apply functional_extensionality; intros);
          auto with arith.
    Qed. *)


  End TreeBagDefinitions.

  Instance IndexedBagAsBag
           (TBag TItem TBagSearchTerm TBagUpdateTerm: Type)
           (projection: TItem -> TKey)
           (bags_bag : @KeyPreservingUpdateBag
                         TBag TItem TBagSearchTerm
                         TBagUpdateTerm projection)
  : @KeyPreservingUpdateBag _ TItem _ TBagUpdateTerm projection :=
    {| KeyPreserving_bag :=
         {| bempty            := IndexedBag_bempty projection bags_bag;
            bstar             := IndexedBag_bstar projection bags_bag;
            bid               := bid;
            bfind_matcher     := IndexedBag_bfind_matcher projection bags_bag;
            bupdate_transform := bupdate_transform;

            benumerate := IndexedBag_benumerate projection bags_bag;
            bfind      := IndexedBag_bfind projection bags_bag;
            binsert    := IndexedBag_binsert projection bags_bag;
            bcount     := IndexedBag_bcount projection bags_bag;
            bdelete    := IndexedBag_bdelete projection bags_bag;
            bupdate    := IndexedBag_bupdate projection bags_bag;

            binsert_enumerate := IndexedBag_BagInsertEnumerate projection bags_bag;
            benumerate_empty  := IndexedBag_BagEnumerateEmpty projection bags_bag;
            bfind_star        := IndexedBag_BagFindStar projection bags_bag;
            bfind_correct     := IndexedBag_BagFindCorrect projection bags_bag;
            bcount_correct    := IndexedBag_BagCountCorrect projection bags_bag
            (* bdelete_correct   := IndexedBag_BagDeleteCorrect projection bags_bag; 
            bupdate_correct   := IndexedBag_BagUpdateCorrect projection bags_bag *)

         |} |}.
  Proof.
    simpl.
    unfold bupdate_transform.
    destruct bags_bag; destruct KeyPreserving_bag0; simpl in *; intros.
    eapply KeyPreserving_Proof0 with (searchTerm := snd searchTerm); eauto.
    unfold IndexedBag_bfind_matcher in H0; simpl in *.
    destruct searchTerm; destruct o; simpl in *; eauto.
    destruct (bfind_matcher t0 item); eauto.
    destruct (KeyFilter projection t1 item); simpl in *; discriminate.
  Abort. 
  (* Still Missing the two correctness proofs. *)

    
End TreeBag.
