Require Export Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapFacts
        Coq.Program.Program
        Coq.Structures.OrderedTypeEx
        Fiat.Common
        Fiat.Common.SetEq
        Fiat.Common.SetEqProperties
        Fiat.Common.List.ListFacts
        Fiat.Common.List.ListMorphisms
        Fiat.Common.LogicFacts
        Fiat.Common.SetoidClassInstances.
Require Coq.Sorting.Permutation Fiat.Common.List.PermutationFacts.

Unset Implicit Arguments.

Module FMapExtensions_fun (E: DecidableType) (Import M: WSfun E).
  Module Export BasicFacts := WFacts_fun E M.
  Module Export BasicProperties := WProperties_fun E M.

  Definition of_list {T} (ls : list (key * T)) : t T
    := List.fold_right
         (fun kv => add (fst kv) (snd kv))
         (empty _)
         ls.

  Definition TKey := key.

  (** TODO: merge with find_default *)
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

  Lemma elements_iff_find :
    forall (elt : Type) (m : t elt) (x : key) (e : elt),
      find x m = Some e <-> InA (eq_key_elt (elt:=elt)) (x, e) (elements (elt:=elt) m).
  Proof.
    intros; rewrite <- elements_iff.
    rewrite find_mapsto_iff; reflexivity.
  Qed.

  Lemma elements_iff' :
    forall (elt : Type) (m : t elt) (xe : key * elt),
      MapsTo (fst xe) (snd xe) m <-> InA (eq_key_elt (elt:=elt)) xe (elements (elt:=elt) m).
  Proof.
    intros; rewrite elements_iff; destruct xe; reflexivity.
  Qed.

  Lemma elements_iff_find' :
    forall (elt : Type) (m : t elt) (xe : key * elt),
      find (fst xe) m = Some (snd xe) <-> InA (eq_key_elt (elt:=elt)) xe (elements (elt:=elt) m).
  Proof.
    intros; rewrite elements_iff_find; destruct xe; reflexivity.
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
    intros; unfold eq_key; split; intuition.
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
      [intuition | apply equiv_eq_key_elt .. ].
  Qed.

  Lemma InA_tail_InA :
    forall elt,
    forall {item} front middle tail,
      InA (eq_key_elt (elt:=elt)) item tail -> InA (eq_key_elt (elt:=elt)) item (front ++ middle :: tail).
  Proof.
    intros; intuition.
    rewrite InA_app_iff;
      [intuition | apply equiv_eq_key_elt .. ].
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
    apply In_InA.
    apply equiv_eq_key_elt.
    induction seq; simpl in *; inversion H; subst; eauto.
  Qed.

  Lemma in_elements_mapsto :
    forall {A: Type} k (e: A) (m: t A),
      List.In (k, e) (elements m) -> MapsTo k e m.
    intros;
      eauto using elements_2, In_InA, equiv_eq_key_elt.
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
      exists k; exists e_pred;
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
    rewrite (@map_modulo_SetEq _ _ _ (GetValues db)); trivial.
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

  Import Coq.Sorting.Permutation Fiat.Common.List.PermutationFacts.

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
    repeat rewrite List.map_app; simpl.
    etransitivity.
    symmetry.
    apply Permutation_middle.
    destruct eq_kv; simpl in *; subst; constructor.
    rewrite <- List.map_app.
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

  (* Partitioning a finite map [m] with a function that respects key and value equality
       will produce a pair of maps equivalent to [m]. *)
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

  (* A restatement of the specification of the [Partition] relation. *)
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

  (* folding a function [f] which respects key, value, and accumulator
       equivalences over two equivalent maps [m1] [m2] will produce
       equivalent values. *)
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

  (* Adding the same key [k] to equivalent maps will produce equivalent maps*)
  Lemma add_Equal_simple :
    forall {TValue} {m1 m2: t TValue},
      Equal m1 m2 ->
      forall k v,
        Equal (add k v m1) (add k v m2).
  Proof.
    intros.
    apply add_m; eauto.
  Qed.

  (* Adding a key [k] overwrites previous values of [k] in a map. *)
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

  (** TODO FIXME: don't locally override other reflexive instances, but instead fix the other instances that get added. *)
  Local Instance: forall {A}, Reflexive (@eq A) | 0 := _.

  Lemma elements_fold_eq :
    forall {TValues} (m: t TValues),
      (elements m) =
      (rev (fold (fun key val acc => cons (key, val) acc) m [])).
  Proof.
    intros.
    rewrite fold_1.

    assert ((fold_left
               (fun (a : list (key * TValues)) (p : key * TValues) =>
                  (fst p, snd p) :: a) (elements m) [])
            = (fold_left
                 (fun (a : list (key * TValues)) (p : key * TValues) =>
                    p :: a) (elements m) []))
      by (f_equal; repeat (apply functional_extensionality; intros);
          rewrite <- surjective_pairing; reflexivity).

    rewrite H, fold_left_id, rev_involutive; reflexivity.
  Qed.

  Lemma elements_fold_perm :
    forall {TValues} (m: t TValues),
      Permutation
        (elements m)
        (fold (fun key val acc => cons (key, val) acc) m []).
  Proof.
    intros.
    rewrite fold_1.

    assert ((fold_left
               (fun (a : list (key * TValues)) (p : key * TValues) =>
                  (fst p, snd p) :: a) (elements m) [])
            = (fold_left
                 (fun (a : list (key * TValues)) (p : key * TValues) =>
                    p :: a) (elements m) []))
      by (f_equal; repeat (apply functional_extensionality; intros);
          rewrite <- surjective_pairing; reflexivity).

    rewrite H.

    rewrite fold_left_id.
    apply Permutation_rev.
  Qed.

  Lemma values_add_not_in {A : Type} :
    forall (m: t A),
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
    etransitivity.
    symmetry.
    etransitivity; [ | apply Permutation_rev].
    symmetry.
    apply (fold_add (elt := A) (eqA := @Permutation A )); eauto.

    apply Permutation_Equivalence.

    unfold Proper, respectful; intros; simpl;
      subst; apply Permutation_cons; try reflexivity; assumption.

    unfold transpose_neqkey; intros; simpl;
      constructor.

    rewrite fold_1.
    rewrite fold_left_map.
    econstructor.
    rewrite Permutation_rev.

    rewrite map_rev.
    rewrite rev_involutive.
    reflexivity.
  Qed.



  (* This should be simplified by the switch to Permutations.

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
    repeat split; intros;
    unfold Ensembles.In in *; simpl in *; intuition.



    apply in_elements_after_add'; trivial.
    rewrite <- H1.
    intuition.

    apply in_elements_after_add in H2.
    destruct H2; intuition.
    subst; intuition.
    rewrite <- H1 in H2; intuition.
    rewrite <- H1 in H2; intuition.
  Qed. *)

  Lemma fold_pair {A B A' B' V} :
    forall (m : t V) (ab : A * B) (f : TKey -> V -> (A' * B')) fa fb,
      @fold V (A * B) (fun k (v : V) (ab : A * B) =>
                         let (a, b) := f k v in
                         let (a', b') := ab in
                         (fa k a a', fb k b b'))
            m ab
      = (fold (fun k m (a' : A) =>
                 fa k (fst (f k m)) a') m (fst ab),
         fold (fun k m (b' : B) =>
                 fb k (snd (f k m)) b')
              m (snd ab)).
  Proof.
    intros; repeat rewrite fold_1; revert ab; induction (elements m);
      destruct ab; simpl; eauto.
    destruct a; simpl; destruct (f k v);
      rewrite IHl; reflexivity.
  Qed.

  Lemma fold_over_Values :
    forall {TValue TAcc} (m: t TValue) f g (init: TAcc),
      (forall k v acc, f k v acc = g acc v) ->
      fold f m init = fold_left g (Values m) init.
  Proof.
    intros * equiv.
    rewrite fold_1.
    unfold Values.
    rewrite <- fold_map.
    revert init; induction (elements m); simpl; eauto.
    intros; rewrite IHl, equiv; reflexivity.
  Qed.

  Lemma Permutation_map_Values {A B} :
    forall (f : A -> B) m,
      Permutation
        (List.map f (Values m))
        (Values (map f m)).
  Proof.
    unfold Values; intros.
    rewrite map_snd.
    apply Permutation_InA_cons; eauto using elements_3w.
    - pose proof (elements_3w m) as NoDupM.
      induction NoDupM; simpl in *; simpl; constructor; eauto.
      unfold not; intros; apply H; clear NoDupM IHNoDupM H;
        induction l; simpl in *; inversion H0; subst; eauto.
    - split; intros.
      apply elements_1.
      rewrite InA_Map in H; destruct H as [[k' v'] [eq_k In_k]];
        destruct eq_k; simpl in *; subst.
      rewrite H; eauto using elements_2, map_1, In_InA, equiv_eq_key_elt.
      rewrite InA_Map.
      apply elements_2 in H.
      apply map_mapsto_iff in H; destruct H as [a [a_eq MapsTo_k]]; subst.
      apply elements_1 in MapsTo_k.
      rewrite InA_alt in MapsTo_k.
      destruct MapsTo_k as [[k' a'] [eq_k In_k]].
      eexists; split; eauto.
      destruct eq_k; simpl in *; subst; constructor; eauto.
  Qed.

  Lemma Permutation_filter_Values {B} :
    forall (f : key -> B -> bool) m
           (Proper_f : Proper (E.eq ==> eq ==> eq) f),
      Permutation
        (Values (filter f m))
        (List.map snd (List.filter (fun kv => f (fst kv) (snd kv)) (elements m))).
  Proof.
    unfold Values; intros.
    apply Permutation_InA_cons; eauto using elements_3w.
    - pose proof (elements_3w m) as NoDupM.
      induction NoDupM; simpl in *; simpl; try constructor.
      case_eq (f (fst x) (snd x)); simpl; eauto.
      intros; constructor; eauto.
      unfold not; intros; apply H; clear NoDupM IHNoDupM H;
        induction l; simpl in *.
      inversion H0; subst; eauto.
      case_eq (f (fst a) (snd a)); intros; rewrite H in *; eauto.
      inversion H1; subst.
      constructor; eauto.
      constructor 2; eauto.
    - intros; rewrite <- elements_mapsto_iff, filter_iff; eauto;
        intuition.
      + rewrite elements_mapsto_iff in H0; induction H0.
        * simpl; destruct H; rewrite Proper_f in H1; eauto;
            rewrite H1; repeat constructor; eauto.
        * simpl; destruct (f (fst y) (snd y)); simpl; eauto.
      + rewrite elements_mapsto_iff; induction (elements m);
          simpl in *.
        * inversion H.
        * case_eq (f (fst a) (snd a)); intros; rewrite H0 in H.
          inversion H; subst.
          constructor; eauto.
          constructor 2; eauto.
          constructor 2; eauto.
      + induction (elements m); simpl in *.
        * inversion H.
        * case_eq (f (fst a) (snd a)); intros; rewrite H0 in H; eauto.
          inversion H; subst.
          destruct H2; rewrite Proper_f in H0; eauto.
          eauto.
  Qed.

  Lemma Permutation_Partition_App {Value}:
    forall (m m1 m2 : t Value),
      Partition m m1 m2 ->
      Permutation (Values m) (Values m1 ++ Values m2).
  Proof.
    unfold Partition; intros; intuition.
    unfold Values; rewrite <- List.map_app.
    eapply Permutation_InA_cons; eauto using elements_3w.
    eapply NoDupA_app; eauto using elements_3w, equiv_eq_key.
    intros; destruct x as [k v]; eapply (H0 k).
    apply InA_alt in H; destruct H; apply InA_alt in H2; destruct H2;
      intuition; unfold eq_key in *; simpl in *.
    destruct x; simpl in *; rewrite H3; econstructor;
      apply elements_2; eauto; apply In_InA; eauto using equiv_eq_key_elt.
    destruct x0; simpl in *; rewrite H; econstructor;
      apply elements_2; eauto; apply In_InA; eauto using equiv_eq_key_elt.
    intros; rewrite InA_app_iff by eauto using equiv_eq_key_elt;
      intuition.
    apply elements_2 in H; rewrite H1 in H; intuition;
      eauto using elements_1.
    apply elements_1; rewrite H1; eauto using elements_2.
    apply elements_1; rewrite H1; eauto using elements_2.
  Qed.

  Corollary Permutation_partition {Value}:
    forall f (m : t Value),
      (Proper (E.eq ==> eq ==> eq) f)
      -> Permutation (Values m)
                     (Values (fst (partition f m)) ++ Values (snd (partition f m))).
  Proof.
    intros; eauto using Permutation_Partition_App,
            partition_Partition_simple.
  Qed.

  Lemma map_add {A B}:
    forall (f : A -> B) m k v,
      Equal (map f (add k v m))
            (add k (f v) (map f m)).
  Proof.
    unfold Equal; intros; case_eq (find y (add k (f v) (map f m)));
      case_eq (find y (map f (add k v m))); intros; eauto.
    - rewrite <- find_mapsto_iff in H, H0.
      rewrite map_mapsto_iff in H; destruct H as [a [b_eq In_b]]; subst.
      rewrite add_mapsto_iff in H0, In_b; intuition; subst; eauto.
      rewrite map_mapsto_iff in H3; destruct H3 as [a' [b_eq' In_b']]; subst.
      rewrite find_mapsto_iff in In_b', H2; congruence.
    - rewrite <- find_mapsto_iff in H0.
      rewrite <- not_find_in_iff in H; exfalso; apply H.
      rewrite add_mapsto_iff in H0; intuition; subst; eauto.
      rewrite H0, map_in_iff, add_in_iff; eauto.
      rewrite map_mapsto_iff in H2; destruct H2 as [a [b_eq In_b]]; subst.
      rewrite map_in_iff, add_in_iff; right; econstructor; eauto.
    - rewrite <- find_mapsto_iff in H.
      rewrite <- not_find_in_iff in H0; exfalso; apply H0.
      rewrite map_mapsto_iff in H; destruct H as [a [b_eq In_b]]; subst.
      rewrite add_mapsto_iff in In_b; intuition; subst; eauto.
      rewrite H1, add_in_iff; eauto.
      rewrite add_in_iff, map_in_iff; right; econstructor; eauto.
  Qed.

  Lemma Equal_elements {A} :
    forall m1 m2,
      Equal m1 m2
      -> forall k (a : A), (InA (@eq_key_elt _) (k, a) (elements m1)
                            <-> InA (@eq_key_elt _) (k, a) (elements m2)).
  Proof.
    unfold Equal; split; intros;
      rewrite <- elements_mapsto_iff, find_mapsto_iff in H0;
      rewrite <- elements_mapsto_iff, find_mapsto_iff; congruence.
  Qed.

  Add Parametric Morphism {A} :
    (@Values A)
      with signature (Equal ==> @Permutation A)
        as Permutation_Equal_Values.
  Proof.
    intros; unfold Values.
    eapply Permutation_InA_cons; eauto using elements_3w, Equal_elements.
  Qed.

  Lemma elements_in_iff' :
    forall (elt : Type) (m : t elt) x,
      In x m <->
      exists v, InA (eq_key (elt:=elt)) (x, v) (elements m) .
  Proof.
    split; rewrite elements_in_iff; intros.
    destruct H; induction H.
    destruct H; eexists x0; econstructor; eauto.
    destruct IHInA; econstructor; econstructor 2; eassumption.
    destruct H; induction H.
    eexists; repeat econstructor; simpl; eauto.
    destruct IHInA; eexists; econstructor 2; eauto.
  Qed.

  Corollary elements_in_if' :
    forall (elt : Type) (m : t elt) x v,
      InA (eq_key (elt:=elt)) (x, v) (elements m) ->
      In x m.
  Proof.
    intros; eapply elements_in_iff'; eauto.
  Qed.

  Definition KeyBasedPartitioningFunction BagType reference :=
    fun key (_: BagType) => if E.eq_dec key reference then true else false.

  Lemma KeyBasedPartitioningFunction_Proper :
    forall BagType reference,
      Proper (E.eq ==> eq ==> eq) (KeyBasedPartitioningFunction BagType reference).
  Proof.
    intros;
      unfold KeyBasedPartitioningFunction, Proper, respectful; intros x y E_eq **; subst;
        destruct (F.eq_dec x _), (F.eq_dec y _); rewrite E_eq in *; intuition.
  Qed.

  Lemma negb_KeyBasedPartitioningFunction_Proper :
    forall BagType reference,
      Proper (E.eq ==> eq ==> eq)
             (fun k e => negb (KeyBasedPartitioningFunction BagType reference k e)).
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

  (* The value [v] mapped to by [k] is the unique value [k] maps to. *)
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

  Lemma KeyBasedPartition_fst_singleton_None :
    forall {TValue} k (m: t TValue),
      ~ In k m ->
      Equal (fst (partition (KeyBasedPartitioningFunction TValue k) m)) (empty TValue).
  Proof.

    intros.
    symmetry.
    unfold Equal; intro key.
    rewrite empty_o; symmetry.
    rewrite <- not_find_in_iff; unfold not; intros.
    apply H.
    destruct H0 as [v H0]; exists v.
    unfold partition in H0; simpl in H0.
    apply filter_iff in H0; eauto.
    intuition eauto.
    unfold KeyBasedPartitioningFunction in H2;
      find_if_inside; try discriminate.
    rewrite <- e; eauto.
    eapply KeyBasedPartitioningFunction_Proper.
  Qed.

  (* If [k'] maps to a value in the first half of a map partitioned on [k],
       it is equivalent to [k]. *)
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

  (* If [k'] maps to a value in the second half of a map partitioned on [k],
       it is *not* equivalent to [k]. *)
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

  (* Paritioning a finite map [m] augmented with a key [k] over [k]
       will produce a map containing just [k] and a map equivalent to [m]. *)
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

  Lemma filter_false_eq_empty
    : forall m,
      Equal (filter
               (fun (_ : key) (_ : list nat) => false) m)
            (empty _).
  Proof.
    unfold filter; simpl.
    intros; rewrite fold_1;
      induction (elements m); simpl; eauto.
    reflexivity.
  Qed.

  Lemma fold_Equal_acc_ :
    forall {TValue TAcc} {eqA: TAcc -> TAcc -> Prop} {m1 : t TValue} {f} {init init': TAcc},
      eqA init init' ->
      Equivalence eqA ->
      Proper (E.eq ==> eq ==> eqA ==> eqA) f ->
      transpose_neqkey eqA f ->
      eqA (fold f m1 init) (fold f m1 init').
  Proof.
    intros.
    rewrite (@fold_Equal _ _ eqA); eauto; try reflexivity; [].
    rewrite !fold_1.
    generalize H1 H2 init init' H; clear.
    induction (elements m1); simpl; intros; eauto.
    eapply IHl; eauto.
    eapply H1; eauto.
  Qed.

  Lemma Proper_add
        elt
    : Proper (E.eq ==> eq ==> Equal ==> Equal)
             (add (elt:=elt)).
  Proof.
    unfold Proper, respectful; intros; eauto using add_m.
  Qed.

  Lemma add_transpose_neqkey
        elt
    : transpose_neqkey (@Equal elt)
                       (@add elt )
  .
  Proof.
    unfold transpose_neqkey; intros.
    eapply Equal_mapsto_iff; split; intros.
    - rewrite add_mapsto_iff in *; intuition; subst.
      destruct (E.eq_dec k0 k'); intuition; eauto.
      rewrite e in H0; intuition.
      rewrite add_mapsto_iff in H2; intuition.
    - rewrite add_mapsto_iff in *; intuition; subst.
      destruct (E.eq_dec k0 k); intuition; eauto.
      rewrite e1 in H0; intuition.
      rewrite add_mapsto_iff in H2; intuition.
  Qed.

  Lemma map_empty
    : forall elt elt' f,
      Equal (map f (empty elt))
            (empty elt').
  Proof.
    intros; eapply Equal_mapsto_iff; split; intros.
    - destruct (map_2 (elt' := elt') (m := empty elt) (x := k)
                      (f := f)).
      + eexists; eauto.
      + apply empty_1 in H0; intuition.
    - apply empty_1 in H; intuition.
  Qed.

  Lemma Permutation_filter_elements {B} :
    forall (f : key -> B -> bool) m
           (Proper_f : Proper (E.eq ==> eq ==> eq) f),
      Permutation
        (List.map snd (elements (filter f m)))
        (List.map snd  (List.filter (fun kv => f (fst kv) (snd kv)) (elements m))).
  Proof.
    intros; apply Permutation_InA_cons; eauto using elements_3w.
    - pose proof (elements_3w m) as NoDupM.
      induction NoDupM; simpl in *; simpl; try constructor.
      case_eq (f (fst x) (snd x)); simpl; eauto.
      intros; constructor; eauto.
      unfold not; intros; apply H; clear NoDupM IHNoDupM H;
        induction l; simpl in *.
      inversion H0; subst; eauto.
      case_eq (f (fst a) (snd a)); intros; rewrite H in *; eauto.
      inversion H1; subst.
      constructor; eauto.
      constructor 2; eauto.
    - intros; rewrite <- elements_mapsto_iff, filter_iff; eauto;
        intuition.
      + rewrite elements_mapsto_iff in H0; induction H0.
        * simpl; destruct H; rewrite Proper_f in H1; eauto;
            rewrite H1; repeat constructor; eauto.
        * simpl; destruct (f (fst y) (snd y)); simpl; eauto.
      + rewrite elements_mapsto_iff; induction (elements m);
          simpl in *.
        * inversion H.
        * case_eq (f (fst a) (snd a)); intros; rewrite H0 in H.
          inversion H; subst.
          constructor; eauto.
          constructor 2; eauto.
          constructor 2; eauto.
      + induction (elements m); simpl in *.
        * inversion H.
        * case_eq (f (fst a) (snd a)); intros; rewrite H0 in H; eauto.
          inversion H; subst.
          destruct H2; rewrite Proper_f in H0; eauto.
          eauto.
  Qed.

  Global Instance eq_key_elt_Equivalence {elt} : Equivalence (@eq_key_elt elt) | 100.
  Proof.
    split; unfold eq_key_elt; repeat (intros [] || intro); simpl in *; intuition.
    etransitivity; eassumption.
  Qed.

  Local Hint Extern 1 (eq_key_elt _ _) => reflexivity.

  Lemma forall_in_eq_key_elt_snd {A} ls (P : _ -> Prop)
    : (forall x : key * A, List.In x ls -> P (snd x))
      <-> (forall x : key * A, InA (@eq_key_elt A) x ls -> P (snd x)).
  Proof.
    split; intros H x H'.
    { rewrite InA_alt in H'.
      destruct H' as [y [[H'0 ?] H'1]].
      specialize (H y); destruct y; simpl in *; subst.
      eauto. }
    { apply H.
      apply InA_In; [ exact _ | ].
      assumption. }
  Qed.

  Lemma forall_in_map_snd_eq_key_elt {A} ls (P : _ -> Prop)
    : (forall x : A, List.In x (List.map (@snd _ _) ls) -> P x)
      <-> (forall x : key * A, InA (@eq_key_elt A) x ls -> P (snd x)).
  Proof.
    rewrite <- forall_in_eq_key_elt_snd.
    setoid_rewrite in_map_iff.
    setoid_rewrite ex_eq_snd_and.
    setoid_rewrite ex_ind_iff.
    split; intro H; [ intros [k x]; specialize (H x k) | intros x k; specialize (H (k, x)) ];
      assumption.
  Qed.

  Lemma elements_mapsto_iff'
    : forall (elt : Type) (m : t elt) (xe : key * elt),
    MapsTo (fst xe) (snd xe) m <-> InA (eq_key_elt (elt:=elt)) xe (elements m).
  Proof.
    intros; rewrite elements_mapsto_iff; destruct xe; reflexivity.
  Qed.

  Definition map2_1bis_for_rewrite (* no metavariables deep inside the beta-iota normal form *)
             elt elt' elt'' f H m m' x
    := @BasicFacts.map2_1bis elt elt' elt'' m m' x f H.

  Definition lift_relation_gen_hetero {A B P}
             (and : P -> P -> P) (True : P)
             (R : A -> B -> P) (defaultA : A) (defaultB : B)
    : t A -> t B -> P
    := fun m1 m2
       => fold
            (fun _ => and)
            (map2
               (fun x1 x2
                => match x1, x2 with
                   | Some x1, Some x2 => Some (R x1 x2)
                   | Some x, None => Some (R x defaultB)
                   | None, Some x => Some (R defaultA x)
                   | None, None => None
                   end)
               m1 m2)
            True.

  Definition lift_relation_hetero {A B} := @lift_relation_gen_hetero A B Prop and True.

  Definition lift_relation {A} (R : A -> A -> Prop) (default : A) : t A -> t A -> Prop
    := lift_relation_hetero R default default.

  Definition lift_brelation_hetero {A B} := @lift_relation_gen_hetero A B bool andb true.

  Definition lift_brelation {A} (R : A -> A -> bool) (default : A) : t A -> t A -> bool
    := lift_brelation_hetero R default default.

  Tactic Notation "setoid_rewrite_in_all" "guarded" tactic3(guard_tac) open_constr(lem) :=
    idtac;
    match goal with
    | [ |- ?G ] => guard_tac G; rewrite !lem
    | [ H : ?T |- _ ] => guard_tac T; rewrite !lem in H
    | [ |- ?G ] => guard_tac G; setoid_rewrite lem
    | [ H : ?T |- _ ] => guard_tac T; setoid_rewrite lem in H
    end.
  Tactic Notation "setoid_rewrite_in_all" open_constr(lem) := setoid_rewrite_in_all guarded(fun T => idtac) lem.

  Tactic Notation "setoid_rewrite_in_all" "guarded" tactic3(guard_tac) "<-" open_constr(lem) :=
    idtac;
    match goal with
    | [ |- ?G ] => guard_tac G; rewrite <- !lem
    | [ H : ?T |- _ ] => guard_tac T; rewrite <- !lem in H
    | [ |- ?G ] => guard_tac G; setoid_rewrite <- lem
    | [ H : ?T |- _ ] => guard_tac T; setoid_rewrite <- lem in H
    end.
  Tactic Notation "setoid_rewrite_in_all" "<-" open_constr(lem) := setoid_rewrite_in_all guarded(fun T => idtac) <- lem.

  Ltac FMap_convert_step_extra_internal should_convert_from_to := fail.

  Ltac FMap_convert_step should_convert_from_to :=
    idtac;
    first [ setoid_rewrite_in_all guarded(fun T => match T with context[List.In _ (rev _)] => idtac end)
                                  <- in_rev
          | setoid_rewrite_in_all guarded(fun T => match T with context[List.In _ (List.map _ (rev _))] => idtac end)
                                  in_map_rev
          | setoid_rewrite_in_all guarded(fun T => match T with context[fold_right andb false _] => idtac end)
                                  fold_right_andb_false
          | should_convert_from_to (@find) (@MapsTo);
            setoid_rewrite_in_all guarded(fun T => match T with context[find _ _ = Some _] => idtac end)
                                  <- find_mapsto_iff
          | should_convert_from_to (@MapsTo) (@find);
            setoid_rewrite_in_all guarded(fun T => match T with context[MapsTo _ _ _] => idtac end)
                                  find_mapsto_iff
          | should_convert_from_to (@InA) (@MapsTo);
            setoid_rewrite_in_all guarded(fun T => match T with context[InA (eq_key_elt (elt:=_)) (_, _) (elements _)] => idtac end)
                                  <- elements_mapsto_iff
          | should_convert_from_to (@MapsTo) (@InA);
            setoid_rewrite_in_all guarded(fun T => match T with context[MapsTo (fst _) (snd _) _] => idtac end)
                                  elements_mapsto_iff'
          | should_convert_from_to (@InA) (@MapsTo);
            setoid_rewrite_in_all guarded(fun T => match T with context[InA (eq_key_elt (elt:=_)) _ (elements _)] => idtac end)
                                  <- elements_mapsto_iff'
          | should_convert_from_to (@MapsTo) (@InA);
            setoid_rewrite_in_all guarded(fun T => match T with context[MapsTo _ _ _] => idtac end)
                                  elements_mapsto_iff
          | should_convert_from_to (@find) (@add);
            setoid_rewrite_in_all guarded(fun T => match T with context[find _ (add _ _ _)] => idtac end)
                                  add_o
          | should_convert_from_to (@add) (@find);
            setoid_rewrite_in_all guarded(fun T => match T with context[if F.eq_dec _ _ then Some _ else find _ _] => idtac end)
                                  <- add_o
          | should_convert_from_to (@find) (@map2);
            setoid_rewrite_in_all guarded(fun T => match T with context[find _ (map2 _ _ _)] => idtac end)
                                  (@map2_1bis_for_rewrite _ _ _ _ eq_refl)
          | should_convert_from_to (@find) (@map2);
            setoid_rewrite_in_all guarded(fun T => match T with context[find _ (map2 _ _ _)] => idtac end)
                                  map2_1bis_for_rewrite; [ | (reflexivity || assumption).. ]
          | should_convert_from_to (@find) (@In);
            setoid_rewrite_in_all guarded(fun T => match T with context[find _ _ = None] => idtac end)
                                  <- not_find_in_iff
          | should_convert_from_to (@In) (@find);
            setoid_rewrite_in_all guarded(fun T => match T with context[~In _ _] => idtac end)
                                  not_find_in_iff
          | should_convert_from_to (@InA) (@In);
            setoid_rewrite_in_all guarded(fun T => match T with context[exists e, InA (eq_key_elt (elt:=_)) (_, _) (elements _)] => idtac end)
                                  <- elements_in_iff
          | should_convert_from_to (@In) (@InA);
            setoid_rewrite_in_all guarded(fun T => match T with context[In _ _] => idtac end)
                                  elements_in_iff
          | should_convert_from_to (@fold) (@fold_left);
            setoid_rewrite_in_all guarded(fun T => match T with context[fold _ _ _] => idtac end)
                                  fold_1
          | should_convert_from_to (@fold_left) (@fold);
            setoid_rewrite_in_all guarded(fun T => match T with context[fold_left _ (elements _) _] => idtac end)
                                  <- fold_1
          | should_convert_from_to (@fold_left) (@fold_right);
            match goal with
            | [ |- appcontext[fold_left (fun a b => ?g (@?f b) a)] ]
              => rewrite (@ListFacts.fold_map _ _ _ _ (fun a b => g b a) f), <- fold_left_rev_right, <- map_rev
            | [ H : appcontext[fold_left (fun a b => ?g (@?f b) a)] |- _ ]
              => rewrite (@ListFacts.fold_map _ _ _ _ (fun a b => g b a) f), <- fold_left_rev_right, <- map_rev in H
            end
          | should_convert_from_to (@fold_right) (@List.In);
              setoid_rewrite_in_all guarded(fun T => match T with
                                                  | context[fold_right andb true (List.map _ _) = true] => idtac
                                                  | context[is_true (fold_right andb true (List.map _ _))] => idtac
                                                  end)
                                  fold_right_andb_map_in_iff
          | should_convert_from_to (@fold_right) (@List.In);
              setoid_rewrite_in_all guarded(fun T => match T with
                                                  | context[fold_right and True _] => idtac
                                                  end)
                                  fold_right_and_True
          | should_convert_from_to (@List.In) (@InA);
            setoid_rewrite_in_all guarded(fun T => match T with context[forall x, List.In x _ -> _] => idtac end)
                                  forall_in_eq_key_elt_snd
          | should_convert_from_to (@List.In) (@InA);
            setoid_rewrite_in_all guarded(fun T => match T with context[forall x, List.In x _ -> _] => idtac end)
                                  (@forall_in_eq_key_elt_snd _ _ (fun k => _ k _))
          | should_convert_from_to (@List.In) (@InA);
            setoid_rewrite_in_all guarded(fun T => match T with context[forall x, List.In x (List.map _ _) -> _] => idtac end)
                                  forall_in_map_snd_eq_key_elt
          | should_convert_from_to (@List.In) (@InA);
            setoid_rewrite_in_all guarded(fun T => match T with context[forall x, List.In x (List.map _ _) -> _] => idtac end)
                                  (@forall_in_map_snd_eq_key_elt _ _ (fun k => _ k _))
          | should_convert_from_to false true;
            setoid_rewrite_in_all guarded(fun T => match T with context[_ = false] => idtac end)
                                  <- not_true_iff_false
          | setoid_rewrite_in_all guarded(fun T => match T with context[find _ (empty _)] => idtac end)
                                  empty_o
          | progress FMap_convert_step_extra_internal should_convert_from_to
          | match goal with H : _ |- _ => revert H end;
            FMap_convert_step should_convert_from_to;
            intros ].

  Ltac FMap_convert' should_convert_from_to :=
    intros; repeat (intros; FMap_convert_step should_convert_from_to).

  Ltac default_should_convert_from_to from to :=
    match from with
    | @find
      => match to with
         | @MapsTo => idtac
         | @InA => idtac
         | @add => idtac
         | @In => idtac
         | @map2 => idtac
         | @lift_relation_gen_hetero => idtac
         | @lift_relation_hetero => idtac
         | @lift_brelation_hetero => idtac
         | @lift_relation => idtac
         | @lift_brelation => idtac
         end
    | @MapsTo
      => match to with
         | @InA => idtac
         end
    | @In
      => match to with
         | @InA => idtac
         end
    | @List.In
      => match to with
         | @InA => idtac
         end
    | @fold
      => match to with
         | @fold_left => idtac
         end
    | @fold_left
      => match to with
         | @fold_right => idtac
         end
    | @fold_right
      => match to with
         | @List.In => idtac
         end
    | @map2
      => match to with
         | @find => idtac
         end
    | @lift_brelation
      => match to with
         | @lift_relation_gen_hetero => idtac
         | @lift_relation_hetero => idtac
         | @lift_relation => idtac
         end
    | false
      => match to with
         | true => idtac
         end
    end.

  Ltac default_should_convert_from_to_find from to :=
    match from with
    | @MapsTo
      => match to with
         | @find => idtac
         end
    | @InA
      => match to with
         | @MapsTo => idtac
         | @find => idtac
         | @In => idtac
         end
    | @In
      => match to with
         | @find => idtac
         end
    | @List.In
      => match to with
         | @InA => idtac
         end
    | @find
      => match to with
         | @add => idtac
         | @map2 => idtac
         end
    | @fold
      => match to with
         | @fold_left => idtac
         end
    | @fold_left
      => match to with
         | @fold_right => idtac
         end
    | @fold_right
      => match to with
         | @List.In => idtac
         end
    | @lift_relation_gen_hetero
      => match to with
         | @find => idtac
         end
    | @lift_relation_hetero
      => match to with
         | @find => idtac
         end
    | @lift_brelation_hetero
      => match to with
         | @find => idtac
         end
    | @lift_relation
      => match to with
         | @find => idtac
         end
    | @lift_brelation
      => match to with
         | @find => idtac
         end
    | false
      => match to with
         | true => idtac
         end
    end.

  Ltac FMap_convert := FMap_convert' default_should_convert_from_to.
  Ltac FMap_convert_to_find := FMap_convert' default_should_convert_from_to_find.

  Ltac setoid_subst_E_eq :=
    repeat match goal with
           | [ H : E.eq ?x ?y |- _ ]
             => is_var x;
                move H at top;
                revert dependent x;
                intros x H;
                setoid_rewrite H;
                clear x H;
                intros
           | [ H : E.eq ?x ?y |- _ ]
             => is_var y;
                move H at top;
                revert dependent y;
                intros y H;
                setoid_rewrite <- H;
                clear y H;
                intros
           | [ H : eq_key_elt _ _ |- _ ] => destruct H
           end.

  Ltac saturate_E_eq :=
    repeat match goal with
           | [ H : E.eq ?x ?y |- _ ]
             => lazymatch goal with
                | [ _ : E.eq y x |- _ ] => fail
                | _ => pose proof (symmetry H)
                end
           | [ H : E.eq ?x ?y, H' : E.eq ?y ?z |- _ ]
             => lazymatch goal with
                | [ _ : E.eq x z |- _ ] => fail
                | _ => pose proof (transitivity H H')
                end
           end.

  Lemma elements_correct {A} (m : t A) (i : key) (v : A)
        (H : find i m = Some v)
    : InA (eq_key_elt (elt:=A)) (i, v) (elements m).
  Proof.
    FMap_convert; assumption.
  Qed.

  Global Instance eq_key_elt_pair_Proper {elt}
    : Proper (E.eq ==> eq ==> @eq_key_elt elt) pair | 10.
  Proof.
    repeat intro; subst.
    hnf; intuition.
  Qed.

  Global Hint Extern 0 (Proper (E.eq ==> _) pair) => eapply eq_key_elt_pair_Proper : typeclass_instances.

  Lemma of_list_elements {T} (v : t T)
    : Equal (of_list (elements v)) v.
  Proof.
    unfold of_list, Equal; intro y.
    destruct (find y v) eqn:H;
      FMap_convert;
      revert H;
      generalize (elements_3w v);
      induction (elements v) as [|x xs IHxs]; clear v.
    { simpl; intros; invlist InA. }
    { intros; invlist InA; invlist NoDupA; simpl in *; specialize_by assumption;
        FMap_convert_to_find;
        edestruct F.eq_dec; setoid_subst_E_eq; simpl in *; intuition (subst; setoid_subst_E_eq; eauto using (@reflexivity _ E.eq)).
      { exfalso; eauto using (@reflexivity _ E.eq). }
      { exfalso; destruct_head prod; eauto using InA_eqke_eqk. } }
    { simpl; intros; invlist InA.
      FMap_convert_to_find.
      intro; destruct_head ex; congruence. }
    { intros; invlist InA; invlist NoDupA; simpl in *;
      FMap_convert_to_find;
      edestruct F.eq_dec; setoid_subst_E_eq; simpl in *; intuition (subst; setoid_subst_E_eq; eauto using (@reflexivity _ E.eq));
      destruct_head prod;
      repeat match goal with
             | [ H : (ex _) -> _ |- _ ] => specialize (fun x pf => H (ex_intro _ x pf))
             | [ H : ((ex _) -> _) -> _ |- _ ] => specialize (fun f => H (fun xpf => match xpf with ex_intro x pf => f x pf end))
             | [ H : ?A -> ?B -> ?C, H' : ?B |- _ ] => specialize (fun pf => H pf H')
             | _ => progress simpl in *
             end;
      eauto using (@reflexivity _ (@eq_key_elt T)), InA_cons_hd. }
  Qed.

  Lemma empty_length_elements {A} (ls : t A)
        (H : Empty ls)
    : List.length (elements ls) = 0.
  Proof.
    rewrite <- M.cardinal_1.
    apply cardinal_Empty; assumption.
  Qed.

  Lemma fold_andb_true v
    : fold (fun _ => andb) v true <-> forall k, find k v <> Some false.
  Proof.
    FMap_convert.
    split; intro H; [ specialize (fun k v => H (k, v)) | ];
      simpl in *;
      intuition eauto using diff_false_true.
    destruct_head prod.
    destruct_head bool; eauto.
  Qed.

  Local Ltac instance_t :=
    repeat match goal with
           | _ => congruence
           | _ => progress destruct_head prod
           | _ => progress destruct_head bool
           | _ => progress simpl in *
           | _ => progress subst
           | _ => solve [ trivial ]
           | [ H : context[match ?e with _ => _ end] |- _ ] => destruct e eqn:?
           | _ => progress specialize_by assumption
           | _ => progress specialize_by (exact eq_refl)
           | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
           | [ H : Some _ = Some _ -> _ |- _ ] => specialize (fun H' => H (f_equal (@Some _) H'))
           | [ H : forall x, Some ?v = Some x -> _ |- _ ] => specialize (H _ eq_refl)
           | [ H : forall x, Some x = Some ?v -> _ |- _ ] => specialize (H _ eq_refl)
           | [ H : ?x = false -> false = true |- _ ]
             => destruct x eqn:?; [ clear H | specialize (H eq_refl); congruence ]
           | _ => progress unfold is_true in *
           end;
    repeat match goal with
           | _ => congruence
           | _ => progress specialize_by assumption
           | _ => progress specialize_by (exact eq_refl)
           | _ => solve [ trivial ]
           | [ H : forall x, ?R x ?y = ?v -> _, H' : ?R ?x' ?y = ?v |- _ ]
             => unique pose proof (H _ H')
           | [ H : forall y, ?R ?x y = ?v -> _, H' : ?R ?x ?y' = ?v |- _ ]
             => unique pose proof (H _ H')
           | [ H : forall x y, ?R x y = ?v -> _, H' : ?R ?x' ?y' = ?v |- _ ]
             => unique pose proof (H _ _ H')
           | [ H : forall x y z, ?R x y = ?v -> _, H' : ?R ?x' ?y' = ?v |- _ ]
             => unique pose proof (fun z => H _ _ z H')
           | [ H : forall x : ?T, ?R x x = true, x' : ?T |- _ ]
             => unique pose proof (H x')
           end.

  Lemma lift_relation_gen_hetero_iff {A B P} and True' (Q : P -> Prop) R defaultA defaultB (m1 : t A) (m2 : t B)
        (QTrue_or_key : Q True' \/ exists k, find k m1 = None /\ find k m2 = None)
        (Qand : forall x y, Q (and x y) <-> Q x /\ Q y)
    : Q (lift_relation_gen_hetero and True' R defaultA defaultB m1 m2)
      <-> forall k, Q (match find k m1, find k m2 with
                       | Some x1, Some x2 => R x1 x2
                       | Some x, None => R x defaultB
                       | None, Some x => R defaultA x
                       | None, None => True'
                       end).
  Proof.
    unfold lift_relation_gen_hetero.
    FMap_convert_to_find.
    rewrite fold_right_push_iff, fold_right_and_iff by (eassumption || exact _).
    FMap_convert_to_find.
    rewrite (forall_In_map Q); FMap_convert_to_find.
    split;
      [ intros [H QTrue'] k; specialize (fun P => H (k, P))
      | intro H; split;
        [ intros [k ?]; specialize (H k)
        | destruct QTrue_or_key as [?| [k [? ?] ] ]; [ | specialize (H k) ] ] ];
      simpl in *;
      break_match;
      repeat intuition (congruence || eauto || destruct_head' ex);
      instance_t.
  Qed.

  Definition lift_relation_hetero_iff {A B} R defaultA defaultB (m1 : t A) (m2 : t B)
    : lift_relation_hetero R defaultA defaultB m1 m2
      <-> forall k, match find k m1, find k m2 with
                    | Some x1, Some x2 => R x1 x2
                    | Some x, None => R x defaultB
                    | None, Some x => R defaultA x
                    | None, None => True
                    end
    := lift_relation_gen_hetero_iff and True (fun x => x) R defaultA defaultB m1 m2
                                    (or_introl I) (fun x y => reflexivity _).

  Definition lift_brelation_hetero_iff {A B} R defaultA defaultB (m1 : t A) (m2 : t B)
    : lift_brelation_hetero R defaultA defaultB m1 m2
      <-> forall k, match find k m1, find k m2 return bool with
                    | Some x1, Some x2 => R x1 x2
                    | Some x, None => R x defaultB
                    | None, Some x => R defaultA x
                    | None, None => true
                    end
    := lift_relation_gen_hetero_iff andb true is_true R defaultA defaultB m1 m2
                                    (or_introl (reflexivity _)) andb_true_iff.

  Definition lift_relation_iff {A} R (default : A) := lift_relation_hetero_iff R default default.
  Definition lift_brelation_iff {A} R (default : A) := lift_brelation_hetero_iff R default default.

  Lemma lift_relation_gen_hetero_impl
        {A B P1 P2 and1 and2 True1 True2 R1 R2}
        {Q1 : _ -> Prop}
        {Q2 : _ -> Prop}
        {defaultA defaultB x y}
        (HTrue1 : Q1 True1)
        (HTrue2 : Q2 True2)
        (Hand1 : forall x y, Q1 (and1 x y) <-> Q1 x /\ Q1 y)
        (Hand2 : forall x y, Q2 (and2 x y) <-> Q2 x /\ Q2 y)
        (HR : forall x y, Q1 (R1 x y) -> Q2 (R2 x y))
    : Q1 (@lift_relation_gen_hetero A B P1 and1 True1 R1 defaultA defaultB x y)
      -> Q2 (@lift_relation_gen_hetero A B P2 and2 True2 R2 defaultA defaultB x y).
  Proof.
    erewrite !lift_relation_gen_hetero_iff by tauto.
    intros H k; specialize (H k); break_match; auto.
  Qed.

  Lemma lift_relation_gen_hetero_iff2
        {A B P1 P2 and1 and2 True1 True2 R1 R2}
        {Q1 : _ -> Prop}
        {Q2 : _ -> Prop}
        {defaultA defaultB x y}
        (HTrue1 : Q1 True1)
        (HTrue2 : Q2 True2)
        (Hand1 : forall x y, Q1 (and1 x y) <-> Q1 x /\ Q1 y)
        (Hand2 : forall x y, Q2 (and2 x y) <-> Q2 x /\ Q2 y)
        (HR : forall x y, Q1 (R1 x y) <-> Q2 (R2 x y))
    : Q1 (@lift_relation_gen_hetero A B P1 and1 True1 R1 defaultA defaultB x y)
      <-> Q2 (@lift_relation_gen_hetero A B P2 and2 True2 R2 defaultA defaultB x y).
  Proof.
    split; apply lift_relation_gen_hetero_impl; firstorder.
  Qed.

  Lemma lift_brelation_hetero_true
        {A B R defaultA defaultB x y}
    : @lift_brelation_hetero A B R defaultA defaultB x y
      <-> @lift_relation_hetero A B R defaultA defaultB x y.
  Proof.
    unfold lift_brelation_hetero, lift_relation_hetero.
    apply (lift_relation_gen_hetero_iff2 (Q1 := is_true) (Q2 := fun x => x));
      try tauto; try reflexivity; apply andb_true_iff.
  Qed.

  Definition lift_brelation_true {A R default x y}
    : @lift_brelation A R default x y <-> @lift_relation A R default x y
    := lift_brelation_hetero_true.

  Ltac FMap_convert_step_extra_internal should_convert_from_to ::=
    first [ should_convert_from_to (@lift_relation) (@lift_brelation);
            setoid_rewrite_in_all guarded(fun T => match T with
                                                   | context[lift_relation (fun x y => _ = true) _ _ _] => idtac
                                                   | context[lift_relation (fun x y => is_true _) _ _ _] => idtac
                                                   end)
                                  <- lift_brelation_true
          | should_convert_from_to (@lift_relation_hetero) (@lift_brelation_hetero);
            setoid_rewrite_in_all guarded(fun T => match T with
                                                   | context[lift_relation_hetero (fun x y => _ = true) _ _ _ _] => idtac
                                                   | context[lift_relation_hetero (fun x y => is_true _) _ _ _ _] => idtac
                                                   end)
                                  <- lift_brelation_hetero_true
          | should_convert_from_to (@lift_brelation) (@lift_relation);
            setoid_rewrite_in_all guarded(fun T => match T with
                                                   | context[is_true (lift_brelation _ _ _ _)] => idtac
                                                   | context[lift_brelation _ _ _ _ = true] => idtac
                                                   end)
                                  lift_brelation_true
          | should_convert_from_to (@lift_brelation_hetero) (@lift_relation_hetero);
            setoid_rewrite_in_all guarded(fun T => match T with
                                                   | context[is_true (lift_brelation_hetero _ _ _ _ _)] => idtac
                                                   | context[lift_brelation_hetero _ _ _ _ _ = true] => idtac
                                                   end)
                                  lift_brelation_hetero_true
          | should_convert_from_to (@lift_relation) (@find);
            setoid_rewrite_in_all guarded(fun T => match T with context[lift_relation _ _ _ _] => idtac end)
                                  lift_relation_iff
          | should_convert_from_to (@lift_brelation) (@find);
            setoid_rewrite_in_all guarded(fun T => match T with context[lift_brelation _ _ _ _] => idtac end)
                                  lift_brelation_iff
          | should_convert_from_to (@lift_relation_hetero) (@find);
            setoid_rewrite_in_all guarded(fun T => match T with context[lift_relation_hetero _ _ _ _ _] => idtac end)
                                  lift_relation_hetero_iff
          | should_convert_from_to (@lift_brelation_hetero) (@find);
            setoid_rewrite_in_all guarded(fun T => match T with context[lift_brelation_hetero _ _ _ _ _] => idtac end)
                                  lift_brelation_hetero_iff ].

  Global Instance map2_Proper_Equal {A B C} f (Hf : f None None = None)
    : Proper (Equal ==> Equal ==> Equal) (@map2 A B C f).
  Proof.
    intros ?? H' ?? H''.
    rewrite Equal_mapsto_iff.
    FMap_convert_to_find.
    setoid_subst_rel (@Equal A).
    setoid_subst_rel (@Equal B).
    reflexivity.
  Qed.

  Global Hint Extern 1 (Proper _ (@map2 ?A ?B ?C ?f))
  => refine (@map2_Proper_Equal A B C f eq_refl) : typeclass_instances.

  Global Instance fold_andb_true_Proper_Equal
    : Proper (@Equal _ ==> eq ==> eq) (fold (fun _ => andb)).
  Proof.
    intros ?? H [] ??; subst;
      match goal with
      | [ |- ?x = ?y ] => destruct x eqn:?; destruct y eqn:?; trivial
      end;
      FMap_convert_to_find;
      setoid_subst_rel (@Equal bool);
      try tauto.
  Qed.

  (** TODO: merge with FindWithDefault *)
  Definition find_default {elt} (default : elt) (k : key) (m : t elt) : elt
    := option_rect (fun _ => elt)
                   (fun v => v)
                   default
                   (find k m).

  Lemma find_default_map2 {elt elt' elt''} f (H : f None None = None)
        default default' default''
        (Hfl : forall v, f None (Some v) = f (Some default) (Some v))
        (Hfr : forall v, f (Some v) None = f (Some v) (Some default'))
        (Hfd : f (Some default) (Some default') = Some default'')
        (m : t elt) (m' : t elt')
        k
    : find_default default'' k (map2 f m m')
      = option_rect (fun _ => elt'')
                    (fun v => v)
                    default''
                    (f (Some (find_default default k m)) (Some (find_default default' k m'))).
  Proof.
    unfold find_default.
    rewrite map2_1bis by assumption.
    do 2 edestruct find; simpl;
      rewrite ?Hfl, ?Hfr, ?Hfd, ?H;
      try reflexivity.
  Qed.

  Definition defaulted_f {elt elt' elt''} (default : elt) (default' : elt') f
    := fun x y => match x, y return option elt'' with
                  | Some x, Some y => Some (f x y)
                  | Some x, None => Some (f x default')
                  | None, Some y => Some (f default y)
                  | None, None => None
                  end.

  Lemma find_default_map2_defaulted {elt elt' elt''} (f : elt -> elt' -> elt'')
        default default' default''
        (Hdefault'' : f default default' = default'')
        (m : t elt) (m' : t elt')
        k
    : find_default default'' k (map2 (defaulted_f default default' f) m m')
      = f (find_default default k m) (find_default default' k m').
  Proof.
    subst.
    erewrite find_default_map2 by reflexivity; reflexivity.
  Qed.

  Global Instance map2_defaulted_Proper_lift_brelation {elt elt' elt''} {default : elt} {default' : elt'} {f}
         {R1 : elt -> elt -> bool}
         {R2 : elt' -> elt' -> bool}
         {R : elt'' -> elt'' -> bool}
         {R1_Reflexive : Reflexive R1}
         {R2_Reflexive : Reflexive R2}
         {f_Proper : Proper (R1 ==> R2 ==> R) f}
    : Proper (lift_brelation R1 default ==> lift_brelation R2 default' ==> lift_brelation R (f default default'))
             (map2 (defaulted_f default default' f)).
  Proof.
    repeat intro; FMap_convert_to_find.
    repeat match goal with
           | [ H : forall x : ?T, _, H' : ?T |- _ ] => specialize (H H')
           end.
    unfold defaulted_f in *.
    unfold Proper, respectful, Reflexive in *.
    instance_t.
  Qed.

  Lemma lift_brelation_iff_false_elements {A} (R : A -> A -> bool) (default : A) (m1 m2 : t A)
        (elms := (elements (map2 (fun x1 x2 => match x1, x2 with
                                               | Some x1, Some x2 => Some (R x1 x2)
                                               | Some x, None => Some (R x default)
                                               | None, Some x => Some (R default x)
                                               | None, None => None
                                               end)
                                 m1 m2)))
    : lift_brelation R default m1 m2 = false
      <-> (exists x, InA (@eq_key_elt _) x elms /\ snd x = false).
  Proof.
    unfold lift_brelation, lift_brelation_hetero, lift_relation_gen_hetero; FMap_convert.
    setoid_rewrite InA_alt.
    subst elms.
    let ls := match goal with |- context[elements ?m] => constr:(elements m) end in
    induction ls as [|x xs IHxs].
    { simpl.
      split; intro H; [ exfalso; apply H | ];
        repeat intuition (tauto || congruence || simpl in * || destruct_head ex || eauto). }
    { simpl.
      setoid_rewrite_logic.
      setoid_rewrite <- IHxs; clear IHxs.
      setoid_rewrite <- InA_alt.
      repeat setoid_rewrite (and_comm _ (_ = _)).
      setoid_rewrite_logic.
      destruct x as [k []]; simpl;
        setoid_rewrite_logic.
      { reflexivity. }
      { setoid_rewrite (True_iff (ex_intro (fun y => E.eq y k) k (reflexivity _))).
        setoid_rewrite (forall_iff_nondep (ex_intro (fun y => E.eq y k) k (reflexivity _))).
        tauto. } }
  Qed.

  Lemma lift_brelation_iff_false {A} (R : A -> A -> bool) (default : A) (m1 m2 : t A)
    : lift_brelation R default m1 m2 = false <-> exists k, match find k m1, find k m2 return bool with
                                                           | Some x1, Some x2 => negb (R x1 x2)
                                                           | Some x, None => negb (R x default)
                                                           | None, Some x => negb (R default x)
                                                           | None, None => false
                                                           end.
  Proof.
    rewrite lift_brelation_iff_false_elements.
    FMap_convert_to_find.
    split;
      [ intros [[k v] H]; exists k; simpl in *
      | intros [k H]; exists (k, false); split; simpl in *; [ | congruence ] ];
      do 2 edestruct find;
      repeat match goal with
             | [ H : and _ _ |- _ ] => destruct H
             | [ H : _ <> true |- _ ] => apply not_true_iff_false in H
             | _ => progress subst
             | _ => setoid_rewrite negb_true_iff
             | [ H : context[negb _] |- _ ] => setoid_rewrite negb_true_iff in H
             | _ => congruence
             end.
  Qed.

  Global Existing Instance eq_Reflexive. (* make [Reflexive _] resolve to [eq_Reflexive] *)
End FMapExtensions_fun.

Module FMapExtensions (M: WS) := FMapExtensions_fun M.E M.
