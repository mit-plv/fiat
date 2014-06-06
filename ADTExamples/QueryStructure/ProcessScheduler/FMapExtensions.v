Require Import Program.

Require Export FMapInterface.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.

Require Import SetEq AdditionalLemmas.

Unset Implicit Arguments.

Module FMapExtensions_fun (E: DecidableType) (Import M: WSfun E).
  Module Export BasicFacts := WFacts_fun E M.
  Module Export BasicProperties := WProperties_fun E M.

  Definition TKey := key.
  
  Definition FindWithDefault {A} (key: TKey) (default: A) (fmap: t A) :=
    match find key fmap with
      | Some result => result
      | None        => default
    end.
  
  Definition Values {A} container :=
    List.map snd (@elements A container).
  
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
  
  (* TODO: Get rid of this *)
  Definition GetValues {A: Type} (db: t A) : list A  :=
    List.map snd (elements db).
  
  
  Definition IndexedBy {A} projection tree :=
    forall key (value: A),
      MapsTo key value tree ->
      key = projection value.

  Lemma FindWithDefault_MapsTo :
    forall {A} default key (value: A) tree,
      MapsTo key value tree -> 
      FindWithDefault key default tree = value.
  Proof.
    unfold FindWithDefault; intros ? ? ? ? ? maps_to.
    rewrite find_mapsto_iff in *.
    rewrite maps_to; trivial.
  Qed.

  Definition ValueFilter {A B: Type} (pred: B -> bool) :=
    (fun (key: A) (value: B) => pred value).

  Lemma ValueFilter_proper: 
    forall (B: Type) (pred: B->bool), 
      Proper (E.eq ==> eq ==> eq) (ValueFilter pred).
  Proof.
    unfold Proper; compute; intros; subst; trivial.
  Qed.

  Definition SameElements {A: Type} (seq: list A) (db: t A) :=
    SetEq seq (GetValues db).

  Lemma elements_iff :
    forall (elt : Type) (m : t elt) (x : key) (e : elt),
      MapsTo x e m <-> InA (eq_key_elt (elt:=elt)) (x, e) (elements (elt:=elt) m).
  Proof.
    intros; split;
    eauto using elements_1, elements_2.
  Qed.

  Lemma InA_In_snd : 
    forall {A: Type} (k: key) (e: A) (l : list (key*A)),
      InA (eq_key_elt (elt:=A)) (k, e) l -> List.In e (List.map snd l).
  Proof.
    intros ? k e ? in_a;
    rewrite InA_alt, in_map_iff in *;
    destruct in_a as [(k', e') (eq0, ?)];
    destruct eq0; simpl in *;
    exists (k', e'); intuition.
  Qed.

  Lemma equiv_eq_key_elt : 
    forall {A: Type}, Equivalence (eq_key_elt (elt := A)).
  Proof.
    unfold eq_key_elt;
    repeat constructor;
    simpl in *; 
    intuition;
    eauto using E.eq_trans, eq_trans.
  Qed.  

  Lemma equiv_eq_key :
    forall elt,
      Equivalence (eq_key (elt:=elt)).
  Proof.
    intros; unfold eq_key; intuition.
    unfold Transitive; firstorder.
    transitivity (fst y); trivial.
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

  Lemma eq_stronger_than_eq_key_elt : 
    forall {A: Type} x seq, 
      InA eq x seq -> InA (eq_key_elt (elt:=A)) x seq.
  Proof.
    intros.
    apply InA_In in H.
    apply (In_InA equiv_eq_key_elt);
      trivial.
  Qed. 

  Lemma in_elements_mapsto : 
    forall {A: Type} k (e: A) (m: t A), 
      List.In (k, e) (elements m) -> MapsTo k e m.
    intros; 
    eauto using elements_2, (In_InA equiv_eq_key_elt).
  Qed.

  Lemma in_elements_after_map : 
    forall {A B: Type} (proc: A -> B) (m: t A) (x: B),
      List.In x (List.map snd (elements (map proc m)))
      -> exists k pred, MapsTo k pred m /\ proc pred = x.  
    intros ? ? ? ? ? in_map;
    rewrite in_map_iff in in_map;
    destruct in_map as [(k, e) (is_proc, in_elements)];
    apply in_elements_mapsto in in_elements;
    rewrite map_mapsto_iff in in_elements;
    destruct in_elements as [e_pred (is_pred, maps_to)];
    exists k e_pred;
    subst; intuition.
  Qed.

  Lemma map_list_map_fmap:
    forall {A B: Type} m (proc: A -> B),
    SetEq (GetValues (map proc m)) (List.map proc (GetValues m)).  
  Proof.
    unfold GetValues; split; intros.
 
    apply in_elements_after_map in H;
    destruct H as [k [predecessor (maps_to, is_predecessor)]];
    rewrite in_map_iff;
    exists predecessor;
    subst; 
    intuition;
    apply (InA_In_snd k), elements_1;
    trivial.

    rewrite in_map_iff in H;
    destruct H as [x0 (?, H)];
    rewrite in_map_iff in H;
    destruct H as [x1 (is_pred, ?)].

    apply (InA_In_snd (fst x1));
    rewrite <- elements_mapsto_iff;
    apply map_mapsto_iff;
    exists x0;
    split;
    [ | apply in_elements_mapsto;
        rewrite <- is_pred, <- surjective_pairing ];
    subst;
    congruence.
  Qed.


  Lemma filter_list_filter_fmap :
    forall {A: Type} m pred,
      SetEq (List.filter pred (GetValues (A:=A) m)) (GetValues (filter (ValueFilter pred) m)).
  Proof. 
    intros.
    unfold SetEq; intuition.
    unfold GetValues.

    rewrite filter_In in H.
    destruct H as [inL sat].
    unfold GetValues in inL.
    apply in_map_iff in inL.
    destruct inL as [x0 (ok, inL)].
    
    destruct x0.
    apply in_elements_mapsto in inL.
    subst.
    simpl.

    apply (InA_In_snd k).
    apply elements_mapsto_iff.
    rewrite filter_iff.
    intuition.

    eauto using ValueFilter_proper.

    unfold GetValues in *.
    rewrite filter_In.

    rewrite in_map_iff in H.
    destruct H as [(k, e) (is_snd, is_in)].

    apply in_elements_mapsto in is_in.

    rewrite filter_iff in is_in; eauto using ValueFilter_proper.

    destruct is_in as [maps_to sat].
    compute in sat.
    simpl in *.
    subst.
    intuition.

    rewrite elements_mapsto_iff in maps_to.
    apply (InA_In_snd k).
    trivial.
  Qed.
  
  Lemma map_modulo_equiv : 
    forall {A B: Type} (db: t A) (seq: list A),
      SameElements seq db -> 
      forall (proc: A -> B), 
        SameElements (List.map proc seq) (map proc db).
  Proof.
    unfold SameElements; intros.
    rewrite (map_modulo_SetEq _ (GetValues db)); trivial.
    clear H; clear seq.
    unfold SetEq.
    symmetry.
    apply map_list_map_fmap.
  Qed.

  Lemma MapsTo_snd :
    forall {A: Type} val tree,
      (exists key, MapsTo key val tree)
      <-> List.In val (List.map snd (elements (elt:=A) tree)).
  Proof.
    split; 
    intro H; 
    [ 
      destruct H as [key mapsto];
      apply (InA_In_snd key);
      apply elements_1
    | 
    rewrite in_map_iff in H;
      destruct H as [(key, val') (eq_val_val', in_lst)];
      subst; simpl;
      exists key;
      apply in_elements_mapsto
    ]; trivial.
  Qed.

  Lemma MapsTo_In :
    forall {A: Type} key (val: A) tree, 
      MapsTo key val tree -> In key tree.
  Proof.
    intros.
    rewrite elements_in_iff.
    rewrite elements_mapsto_iff in *.
    eauto.
  Qed.

  Lemma in_elements_after_add:
    forall {A: Type} key (added elem: A) tree, 
      (List.In elem (GetValues (add key added tree)) 
       -> (elem = added \/ List.In elem (GetValues tree))).
  Proof.
    unfold GetValues;
    intros ? ? ? ? ? is_in;
    rewrite <- MapsTo_snd;
    rewrite <- MapsTo_snd in is_in.

    destruct is_in as [key' map_add];
      rewrite add_mapsto_iff in map_add;
      destruct map_add;
      [ left | right ]; intuition; eauto.
  Qed.
  
  Lemma in_elements_after_add':
    forall {A: Type} _key (added elem: A) tree, 
      (~ In _key tree) ->
      (elem = added \/ List.In elem (GetValues tree))
      -> (List.In elem (GetValues (add _key added tree))).
  Proof.
    unfold GetValues;
    intros ? ? ? ? ? not_in is_in;
    rewrite <- MapsTo_snd;
    rewrite <- MapsTo_snd in is_in.

    setoid_rewrite add_mapsto_iff;
      destruct is_in as [eq | [_key' _key'_map]];
      [ exists _key 
      | exists _key'; 
        right; 
        split;
        [ intro Eeq;
          apply MapsTo_In in _key'_map;
          apply not_in;
          rewrite (In_iff _ Eeq) | ]
      ]; intuition.
  Qed.

  Lemma in_elements_after_add_iff:
    forall {A: Type} key (added elem: A) tree, 
      (~ In key tree) ->
      (List.In elem (GetValues (add key added tree)) 
       <-> (elem = added \/ List.In elem (GetValues tree))).
  Proof.
    intros; 
    split; 
    eauto using in_elements_after_add, in_elements_after_add'.
  Qed.


  Lemma In_MapsTo : 
    forall A tree key,
      In key tree -> 
      exists (value: A), 
        (MapsTo key value tree /\ find key tree = Some value).
  Proof.
    intros A tree key H;
    apply in_find_iff in H;
    destruct (find key tree) as [value | ] eqn:eq_option;
    try rewrite <- find_mapsto_iff in eq_option;
    intuition eauto.
  Qed.

  Lemma EnsembleListEquivalence_fmap_add_filtered :
    forall {A: Type} (cond : A -> Prop) ensemble key tree added,
      cond added ->
      (~ In (elt:=A) key tree) ->
      EnsembleListEquivalence 
        (fun x => Ensembles.In _ ensemble x /\ cond x) 
        (GetValues tree) -> 
      EnsembleListEquivalence
        (fun x => (x = added \/ Ensembles.In _ ensemble x) /\ cond x)
        (GetValues (add key added tree)).
  Proof.
    unfold EnsembleListEquivalence;
    split; intros;
    unfold Ensembles.In in *; simpl in *.

    apply in_elements_after_add'; trivial.        
    rewrite <- H1.
    intuition.

    apply in_elements_after_add in H2.
    destruct H2; intuition.
    subst; intuition.
    rewrite <- H1 in H2; intuition.
    rewrite <- H1 in H2; intuition.
  Qed.
End FMapExtensions_fun.

Module FMapExtensions (M: WS) := FMapExtensions_fun M.E M.

Module NestedTrees (M1: WS) (M2: WS).
  Module Ext1 := FMapExtensions M1.
  Module Ext2 := FMapExtensions M2.

  Definition PartitionedEnsembleListEquivalence {A} set_db tree_db projection :=
      forall key_instance,
        EnsembleListEquivalence
          (FilteredSet set_db projection key_instance)
          (@Ext2.GetValues A (Ext1.FindWithDefault key_instance (M2.empty A) tree_db)).


  Definition ExtractRows {A: Type} db :=
    @flatten A (map Ext2.GetValues 
                    (Ext1.GetValues db)).

  Lemma FindWithDefault_NonEmpty_Found :
    forall {A} key tree,
      let subtree := Ext1.FindWithDefault key (M2.empty A) tree in
      (exists row, List.In row (Ext2.GetValues subtree)) ->
      List.In subtree (Ext1.GetValues tree).
  Proof.    
    intros.
    unfold Ext1.FindWithDefault in subtree.
    destruct (M1.find key tree) eqn:eq_find.

    rewrite <- Ext1.BasicFacts.find_mapsto_iff in eq_find.
    unfold Ext1.GetValues.
    rewrite <- Ext1.MapsTo_snd.
    eauto.

    exfalso.
    destruct H as [row row_in].
    unfold Ext2.GetValues in row_in.
    rewrite <- Ext2.MapsTo_snd in row_in. (* TODO: Embed GetValues in MapsTo_snd *)
    destruct row_in as [key2 maps_to].
    rewrite <- Ext2.BasicFacts.empty_mapsto_iff.
    eauto.
  Qed.

  Definition IndexedBy {A} projection tree :=
    forall key subtree,
      M1.MapsTo key subtree tree ->
      forall (row: A),
        List.In row (Ext2.GetValues subtree) -> projection row = key. 

  Lemma unpartition :
    forall {A} projection set_db tree_db,
      IndexedBy projection tree_db ->
      @PartitionedEnsembleListEquivalence A set_db tree_db projection ->
      EnsembleListEquivalence set_db (ExtractRows tree_db).
    Proof.
      unfold PartitionedEnsembleListEquivalence, ExtractRows; intros.
      unfold EnsembleListEquivalence; intros.

      specialize (H0 (projection x)).
      unfold FilteredSet in *.
      unfold ExtractRows.

      split; intros.
      rewrite in_flatten_iff.
      set (subtree := (Ext1.FindWithDefault (projection x) (M2.empty A) tree_db)) in *.
      exists (Ext2.GetValues subtree).
      
      specialize (H0 x); unfold Ensembles.In in *; simpl in H0.
      rewrite in_map_iff.
      split.
      
      intuition.
      exists subtree; split; trivial.
      destruct H0 as (H0 & _).

      Lemma ugh: 
        forall (P Q R: Prop),
         (P /\ Q -> R) <->  (P -> Q -> R).
      Proof.
        tauto.
      Qed.
      
      rewrite ugh in H0.
      specialize (H0 H1 (eq_refl (projection x))).
 
      apply FindWithDefault_NonEmpty_Found;
        eauto.

      specialize (H0 x).
      destruct H0 as (_ & H0).

      unfold Ensembles.In in *.

      Lemma ugh2 :
        forall (P Q R: Prop),
          (P -> (Q /\ R)) <-> ((P -> Q) /\ (P -> R)).
      Proof.
        tauto.
      Qed.

      rewrite ugh2 in H0.
      destruct H0 as (H0 & _).

      rewrite in_flatten_iff in H1.
      destruct H1 as [subtree_values (x_in_subtree_values & subtree_values_in_map)].
      rewrite in_map_iff in subtree_values_in_map.
      destruct subtree_values_in_map as [subtree (subtree_values_correct & subtree_in_tree_values)].
      unfold Ext1.GetValues in subtree_in_tree_values.
      rewrite <- Ext1.MapsTo_snd in subtree_in_tree_values.
      destruct subtree_in_tree_values as [key maps_to].
      subst.

      unfold IndexedBy in H.
      specialize (H _ _ maps_to _ x_in_subtree_values).
      subst.

      apply (Ext1.FindWithDefault_MapsTo (M2.empty A)) in maps_to.
      rewrite maps_to in H0.
      intuition.
    Qed.
End NestedTrees.
