Require Export Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsInterface
        Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsProperties.
Require Import
        Coq.FSets.FMapInterface
        Coq.FSets.FMapFacts
        Coq.FSets.FMapAVL
        Coq.omega.Omega
        Fiat.Common
        Fiat.Common.List.ListFacts
        Fiat.Common.List.FlattenList
        Fiat.Common.SetEqProperties
        Fiat.Common.FMapExtensions
        Fiat.Common.List.PermutationFacts
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix.

Module TrieBag (X:OrderedType).

  Module XMap := FMapAVL.Make X.
  Module Import XMapFacts := WFacts_fun X XMap.
  Module Import MoreXMapFacts := FMapExtensions_fun X XMap.

  Section TrieBagDefinitions.

    Definition SearchTerm := option (list X.t).

    Context {BagType TItem SearchTermType UpdateTermType : Type}
            (TBag : Bag BagType TItem SearchTermType UpdateTermType)
            (RepInv : BagType -> Prop)
            (ValidUpdate : UpdateTermType -> Prop)
            (TBagCorrect : CorrectBag RepInv ValidUpdate TBag)
            (projection: TItem -> list X.t).

    Import XMap.Raw.
    Import XMap.Raw.Proofs.

    Definition Map := t.

    Inductive Trie :=
    | Node : BagType -> Map Trie -> Trie.

    Definition TrieNode (trie : Trie) :=
      match trie with
        | Node bag tries => bag
      end.

    Definition SubTries (trie : Trie) :=
      match trie with
        | Node bag tries => tries
      end.

    (* Emptiness *)

    Definition TrieBag_bempty := Node bempty (empty Trie).

    Definition IsPrefix l (st : list X.t) : bool :=
      if Prefix_dec X.eq_dec l st then true else false.

    Arguments IsPrefix _ _  / .

    Definition TrieBag_bfind_matcher
               (search_term: SearchTerm * SearchTermType) (item: TItem) :=
      match fst search_term with
        | Some st =>
          IsPrefix (projection item) st
        | None => true
      end && (bfind_matcher (snd search_term) item).

    Definition XMapfold
               (A : Type) (f : X.t -> Trie -> A -> A) :=
      fix XMapfold (m : tree Trie) (a : A) {struct m} : A :=
      match m with
        | XMap.Raw.Leaf => a
        | XMap.Raw.Node l x d r _ => XMapfold r (f x d (XMapfold l a))
      end.

    Lemma XMapfold_eq A f
    : forall m acc,
        @XMapfold A f m acc =
        @XMap.Raw.fold _ A f m acc.
    Proof.
      unfold XMapfold, XMap.Raw.fold; simpl.
      induction m; eauto.
      intros; rewrite IHm1, IHm2; reflexivity.
    Qed.

    Fixpoint Trie_enumerate
             (t : Trie)
             {struct t}
    : list BagType :=
      match t with
        | Node bag tries =>
          XMapfold (fun _ tries bags =>
                      Trie_enumerate tries ++ bags) tries [bag]
      end.

    Definition TrieBag_benumerate
               (container: Trie)
      := flatten (List.map benumerate (Trie_enumerate container)).

    Fixpoint Trie_find
             (trie : Trie)
             (st : list X.t)
    : list BagType :=
      (TrieNode trie) :: match st with
                           | nil => [ ]
                           | key :: st' =>
                             match find key (SubTries trie) with
                               | Some subtrie => Trie_find subtrie st'
                               | None => [ ]
                             end
                         end.

    Fixpoint Trie_find'
             (trie : Trie)
             (st : list X.t)
      : list BagType :=
      (TrieNode trie) ::
                      XMapfold (fun k tries found =>
                                  (Trie_find' tries st) ++ found) (SubTries trie) [ ].

    Definition TrieBag_bcount
               (trie : Trie)
               (key_searchterm: SearchTerm * SearchTermType)
    : nat :=
      match key_searchterm with
        | (Some st, search_term) =>
          fold_left plus (List.map (fun bag : BagType => bcount bag search_term)
                                   (Trie_find trie st)) 0
        | (None, search_term) =>
          fold_left plus (List.map (fun bag : BagType => bcount bag search_term)
                                   (Trie_enumerate trie)) 0
      end.

    Definition TrieBag_bfind
               (trie : Trie)
               (key_searchterm: SearchTerm * SearchTermType)
    : list TItem :=
      match key_searchterm with
      | (Some st, search_term) =>
        flatten (List.map (fun bag : BagType => bfind bag search_term)
                                 (Trie_find trie st))
      | (None, search_term) =>
        flatten (List.map (fun bag : BagType => bfind bag search_term)
                                 (Trie_enumerate trie))
      end.

    Fixpoint Trie_add
             (trie : Trie)
             (st : list X.t)
             (item : TItem) : Trie :=
      match st with
        | [ ] =>
          Node (binsert (TrieNode trie) item) (SubTries trie)
        | key :: st' =>
          match find key (SubTries trie) with
            | Some subtrie =>
              Node (TrieNode trie)
                   (add key (Trie_add subtrie st' item)
                        (SubTries trie))
            | None =>
              Node (TrieNode trie)
                   (add key (Trie_add TrieBag_bempty st' item)
                        (SubTries trie))
          end
      end.

    Definition TrieBag_binsert
               (trie : Trie)
               (item: TItem) : Trie :=
      Trie_add trie (projection item) item.

    Fixpoint Trie_delete
             (trie : Trie)
             (st : list X.t)
             (search_term : SearchTermType)
    : (list TItem) * Trie :=
      match st with
        | nil =>
          let (deletedItems, bag') :=
              bdelete (TrieNode trie) search_term in
          (deletedItems, Node bag' (SubTries trie))
        | key :: st' =>
          let (deletedItems, bag') :=
              bdelete (TrieNode trie) search_term in
          match find key (SubTries trie) with
            | Some subtrie =>
              let (deletedSubItems, bag'') :=
                  Trie_delete subtrie st' search_term in
              (deletedItems ++ deletedSubItems,
               Node bag' (add key bag'' (SubTries trie)))
            | None =>
              (deletedItems, Node bag' (SubTries trie))
          end
      end.

    Fixpoint Trie_delete'
             (trie : Trie)
             (search_term : SearchTermType)
             {struct trie}
    : (list TItem) * Trie :=
      match trie with
      | Node bag tries =>
        let (deletedItems, bag') :=
            bdelete (TrieNode trie) search_term in
        let tries' :=
            XMapfold (fun k tries (deleted : (list TItem) * _)  =>
                        let (deletedItems', bag') := Trie_delete' tries search_term in
                        let (deletedItems'', bags') := deleted in
                        (deletedItems' ++ deletedItems'', XMap.add k bag' bags'))
                     tries ([ ], XMap.empty _) in
        (deletedItems ++ fst tries', Node bag' (XMap.this (snd tries')))
      end.

    Definition TrieBag_bdelete
               (trie : Trie)
               (key_searchterm : SearchTerm * SearchTermType)
      : (list TItem) * Trie :=
      match key_searchterm with
      | (Some st, search_term) => Trie_delete trie st search_term
      | (None, search_term) => Trie_delete' trie search_term
      end.

    Fixpoint Trie_update
             (trie : Trie)
             (st : list _)
             (search_term : SearchTermType)
             (updateTerm : UpdateTermType)
    : (list TItem) * Trie :=
      match st with
        | nil =>
          let (updatedItems, bag') :=
              bupdate (TrieNode trie) search_term updateTerm in
          (updatedItems, Node bag' (SubTries trie))
        | key :: st' =>
          let (updatedItems, bag') :=
              bupdate (TrieNode trie) search_term updateTerm in
          match find key (SubTries trie) with
            | Some subtrie =>
              let (updatedSubItems, bag'') :=
                  Trie_update subtrie st' search_term updateTerm in
              (updatedItems ++ updatedSubItems,
               Node bag' (add key bag'' (SubTries trie)))
            | None =>
              (updatedItems, Node bag' (SubTries trie))
          end
      end.

    Fixpoint Trie_update'
             (trie : Trie)
             (search_term : SearchTermType)
             (updateTerm : UpdateTermType)
             {struct trie}
    : (list TItem) * Trie :=
      match trie with
      | Node bag tries =>
        let (updatedItems, bag') :=
            bupdate (TrieNode trie) search_term updateTerm in
        let tries' :=
            XMapfold (fun k tries (updated : (list TItem) * _)  =>
                        let (updatedItems', bag') := Trie_update' tries search_term updateTerm in
                        let (updatedItems'', bags') := updated in
                        (updatedItems' ++ updatedItems'', XMap.add k bag' bags'))
                     tries ([ ], XMap.empty _) in
        (updatedItems ++ fst tries', Node bag' (XMap.this (snd tries')))
      end.

    Definition TrieBag_bupdate
               (trie : Trie)
               (key_searchterm : SearchTerm * SearchTermType)
               (updateTerm : UpdateTermType)
      : (list TItem) * Trie :=
      match key_searchterm with
      | (Some st, search_term) => Trie_update trie st search_term updateTerm
      | (None, search_term) => Trie_update' trie search_term updateTerm
      end.

    Definition WFMap := bst.

    Definition Prefix (s s' : list X.t) :=
      exists s'', eqlistA X.eq (s ++ s'') s'.

    Lemma IsPrefix_iff_Prefix :
      forall (s s' : list X.t),
        IsPrefix s s' = true <-> Prefix s s'.
    Proof.
      unfold Prefix; split; revert s'; induction s; intros s' H.
      - eexists s'; reflexivity.
      - destruct s'; simpl in H.
        + discriminate.
        + destruct (F.eq_dec a t); [subst | discriminate].
          unfold IsPrefix in IHs.
          destruct (IHs s').
          destruct (Prefix_dec F.eq_dec s s'); try discriminate; eauto.
          eexists; subst; eauto.
          simpl; econstructor; eauto.
      - simpl; reflexivity.
      - destruct s'; simpl in *; destruct H.
        + inversion H.
        + inversion H; subst; destruct (F.eq_dec a t).
          destruct (Prefix_dec F.eq_dec s s'); eauto.
          elimtype False; apply n; eexists; eauto.
          congruence.
    Qed.

    Inductive TrieOK : Trie -> list X.t -> Prop :=
    | NodeSomeOK :
        forall bag subtries st,
          RepInv bag
          -> bst subtries
          -> (forall (item: TItem),
                List.In item (benumerate bag) ->
                eqlistA X.eq (projection item) st)
          -> (forall k subtrie,
                MapsTo k subtrie subtries
                -> TrieOK subtrie (st ++ [k]))
          -> TrieOK (Node bag subtries) st.

    Lemma SubTrieMapBST
    : forall bag subtries st,
        TrieOK (Node bag subtries) st
        -> bst subtries.
    Proof.
      inversion 1; eauto.
    Qed.

    Lemma SubTrieMapBST'
    : forall trie st,
        TrieOK trie st -> bst (SubTries trie).
    Proof.
      inversion 1; eauto.
    Qed.

    Hint Resolve SubTrieMapBST SubTrieMapBST'.

    Lemma TrieNode_RepInv
    : forall bag subtries st,
        TrieOK (Node bag subtries) st
        -> RepInv bag.
    Proof.
      inversion 1; eauto.
    Qed.

    Lemma TrieNode_RepInv'
    : forall trie st,
        TrieOK trie st -> RepInv (TrieNode trie).
    Proof.
      inversion 1; eauto.
    Qed.

    Hint Resolve TrieNode_RepInv TrieNode_RepInv'.

    Lemma SubTrieOK
    : forall trie k subtrie st,
        TrieOK trie st
        -> find k (SubTries trie) = Some subtrie
        -> TrieOK subtrie (st ++ [k]).
    Proof.
      destruct trie; simpl.
      induction m; simpl in *; intros.
      - discriminate.
      - inversion H; subst.
        case_eq (X.compare k0 k); intros; rewrite H1 in H0.
        + eapply IHm1; eauto.
          econstructor; simpl in *; eauto.
          inversion H4; subst; eauto.
        + injections; simpl in *.
          eapply (H7 k0 _); eauto.
        + eapply IHm2; eauto.
          econstructor; simpl in *; eauto.
          inversion H4; subst; eauto.
    Qed.

    Hint Resolve SubTrieOK.

    Definition TrieBagRepInv (trie : Trie) := TrieOK trie [ ].

    Definition TrieBag_ValidUpdate (update_term : UpdateTermType) :=
      ValidUpdate update_term /\
      forall K item,
        eqlistA X.eq (projection item) K
        -> eqlistA X.eq (projection (bupdate_transform update_term item)) K.

    Lemma Trie_Empty_RepInv :
      TrieBagRepInv (TrieBag_bempty).
    Proof.
      unfold TrieBagRepInv; intros; econstructor; simpl in *.
      apply bempty_RepInv.
      econstructor.
      intros; elimtype False; eapply benumerate_empty; eauto.
      intros; elimtype False; eapply empty_1; eauto.
    Qed.

    Functional Scheme Trie_add_ind := Induction for Trie_add Sort Prop.
    Functional Scheme Trie_delete_ind := Induction for Trie_delete Sort Prop.
    Functional Scheme Trie_update_ind := Induction for Trie_update Sort Prop.
    Functional Scheme Trie_find_ind := Induction for Trie_find Sort Prop.

    Hint Resolve add_bst.
    Hint Constructors eqlistA.

    Lemma Trie_add_Preserves_TreeOK
    : forall trie item st1 st2,
        eqlistA X.eq (projection item) (st2 ++ st1)
        -> TrieOK trie st2
        -> TrieOK (Trie_add trie st1 item) st2.
    Proof.
      intros trie item st1; eapply Trie_add_ind; intros; subst.
      - econstructor; inversion H0; subst; eauto.
        + eapply binsert_RepInv; eauto.
        + intros; rewrite binsert_enumerate in H5 by eauto.
          simpl in *; intuition; subst.
          rewrite H, app_nil_r; reflexivity.
      - econstructor; inversion H1; subst; simpl; eauto.
        intros; destruct (X.eq_dec k key0).
        apply find_1 in H6; eauto.
        pose proof (add_1 subtries (Trie_add subtrie st' item0) (X.eq_sym e)) as H7; apply find_1 in H7; eauto.
        rewrite H6 in H7; injections; intros; subst.
        eapply H; eauto.
        rewrite <- app_assoc.
        rewrite H0.
        apply eqlistA_app;
          repeat first [econstructor; eauto
                       | try reflexivity ].
        apply H5.
        apply MapsTo_1 with (x := key0).
        symmetry; eauto.
        apply find_2; eassumption.
        apply H5.
        eapply add_3 in H6; eauto.
      - econstructor; inversion H1; subst; simpl; eauto.
        + intros; destruct (X.eq_dec k key0).
          apply find_1 in H6; eauto.
          pose proof (add_1 subtries (Trie_add TrieBag_bempty st' item0) (X.eq_sym e)) as H7; apply find_1 in H7; eauto.
          rewrite H6 in H7; injections; intros; subst.
          eapply H; eauto.
          rewrite <- app_assoc.
          rewrite H0.
          apply eqlistA_app;
            repeat first [econstructor; eauto
                         | try reflexivity ].
          unfold TrieBagRepInv; intros; econstructor; simpl in *.
          apply bempty_RepInv.
          econstructor.
          intros; elimtype False; eapply benumerate_empty; eauto.
          intros; elimtype False; eapply empty_1; eauto.
          apply H5.
          eapply add_3 in H6; eauto.
    Qed.

    Corollary TrieBag_binsert_Preserves_RepInv :
      binsert_Preserves_RepInv TrieBagRepInv TrieBag_binsert.
    Proof.
      unfold binsert_Preserves_RepInv; intros.
      eapply Trie_add_Preserves_TreeOK; simpl.
      reflexivity.
      apply containerCorrect.
    Qed.

    Lemma Trie_ind'
          (P : Trie -> list key -> Prop)
          (IH : forall (b : BagType) (m : Map Trie) l,
              (forall k trie l, MapsTo k trie m -> P trie (l ++ [k]))
              -> P (Node b m) l)
          (trie : Trie)
      : forall l, P trie l.
          refine ((fix Trie_ind trie :=
                    match trie return forall l, P trie l with
                    | Node b tries => fun l => IH _ _ _ ((fun f0 =>
                                                fix F (t : t Trie) : (forall k trie l, MapsTo k trie t -> P trie (l ++ [k])) :=
                                                match t as t0 return ((forall k trie l, MapsTo k trie t0 -> P trie (l ++ [k]))) with
                                                | Leaf =>  _
                                                | XMap.Raw.Node t0 k e t1 t2 => f0 t0 (F t0) k e t1 (F t1) t2
                                                end) _ tries)
                    end) trie).
          - intros; inversion H.
          - intros; inversion H; subst.
            + let Trie_ind0 := match goal with Trie_ind0 : forall (trie : Trie) (l : list key), ?P trie l |- _ => constr:(Trie_ind0) end in
              apply Trie_ind0.
            + eapply x0; eauto.
            + eapply x4; eauto.
    Qed.

    Definition XMapfold_ind
               (P : Trie -> list BagType -> list X.t-> Prop)
               (f : forall trie st, P trie (Trie_enumerate trie) st)
               (m : tree Trie) (is_bst : bst m) :
      forall k trie st , MapsTo k trie m ->
                         P trie (Trie_enumerate trie) (st ++ [k]).
    Proof.
      refine ((fix XMapfold (m : tree Trie) {struct m} :
                 bst m ->
                 forall k trie st, MapsTo k trie m ->
                                   P trie (Trie_enumerate trie) (st ++ [k]) :=
                 match m with
                   | XMap.Raw.Leaf => _
                   | XMap.Raw.Node l x d r _ => _
                 end) m is_bst).
      - intros; apply find_1 in H0; simpl in H0;
        [ discriminate | eauto ].
      - intros; apply find_1 in H0; simpl in H0;
        [ destruct (X.compare k x)
        | eassumption ].
        + apply find_2 in H0.
          let XMapfold0 := match goal with XMapfold0 : forall m : XMap.Raw.t Trie, _ -> forall (k : key) (trie : Trie) (st : list key), _ -> _ |- _ => constr:(XMapfold0) end in
          eapply (XMapfold0 l); eauto.
          inversion H; subst; eauto.
        + pose proof (f d (st ++ [k])).
          injections; eassumption.
        + apply find_2 in H0.
          let XMapfold0 := match goal with XMapfold0 : forall m : XMap.Raw.t Trie, _ -> forall (k : key) (trie : Trie) (st : list key), _ -> _ |- _ => constr:(XMapfold0) end in
          eapply (XMapfold0 r); eauto.
          inversion H; subst; eauto.
    Defined.

    Lemma TrieBag_bdelete_Preserves_RepInv :
      bdelete_Preserves_RepInv TrieBagRepInv TrieBag_bdelete.
    Proof.
      unfold bdelete_Preserves_RepInv, TrieBagRepInv;
      intros trie search_term; remember []; clear Heql; revert l.
      unfold TrieBag_bdelete.
      destruct search_term as [ [l | ] s].
      { eapply Trie_delete_ind; intros; subst.
        - econstructor; inversion containerCorrect; subst; eauto.
          + pose proof (bdelete_RepInv bag search_term) as e'; simpl in *;
            rewrite e0 in e'; eapply e'.
            inversion containerCorrect; eauto.
          + intros; eapply H1.
            destruct (bdelete_correct bag search_term); eauto.
            simpl in *; rewrite e0 in *; simpl in *.
            rewrite H4 in H3.
            rewrite In_partition; eauto.
        - econstructor; inversion containerCorrect; subst; eauto.
          + pose proof (bdelete_RepInv bag search_term) as e'; simpl in *;
            rewrite e0 in e'; eapply e'; eauto.
          + intros; eapply H2.
            destruct (bdelete_correct bag search_term); eauto.
            simpl in *; rewrite e0 in *; simpl in *.
            rewrite H5 in H4.
            rewrite In_partition; eauto.
          + intros; destruct (X.eq_dec k key0).
            * apply find_1 in H4; eauto.
              simpl in *.
              pose proof (add_1 subtries bag'' (X.eq_sym e)) as H7; apply find_1 in H7; eauto.
              rewrite H4 in H7; injections; intros; subst.
              rewrite e2 in H; eapply H.
              eapply H3.
              apply MapsTo_1 with (x := key0).
              symmetry; eauto.
              apply find_2; eauto.
            * apply H3.
              eapply add_3; eauto.
        - simpl; econstructor; inversion containerCorrect; subst; eauto.
          + pose proof (bdelete_RepInv bag search_term) as e'; simpl in *;
            rewrite e0 in e'; eapply e'.
            inversion containerCorrect; eauto.
          + intros; eapply H1.
            destruct (bdelete_correct bag search_term); eauto.
            simpl in *; rewrite e0 in *; simpl in *.
            rewrite H4 in H3.
            rewrite In_partition; eauto.
      }
      { intro; pattern trie, l; apply Trie_ind'; simpl; intros.
        intros; inversion containerCorrect; subst.
        case_eq (bdelete b s); simpl; intros.
        econstructor.
        + pose proof (bdelete_RepInv b s) as e'; simpl in *.
          rewrite H0 in e'; eapply e'; eauto.
        + apply XMap.is_bst.
        + intros; eapply H4.
          destruct (bdelete_correct b s); eauto.
          simpl in *; rewrite H0 in *; simpl in *.
          rewrite H5 in H1.
          rewrite In_partition; eauto.
        + intros; rewrite XMapfold_eq in H1.
          setoid_rewrite (fold_pair (XMap.Bst H3)) in H1; simpl in H1.
          assert (XMap.MapsTo k subtrie
                              (XMap.fold
                                 (fun (k0 : XMap.key) (m0 : Trie) (b' : XMap.t Trie) =>
                                    XMap.add k0 (snd (Trie_delete' m0 s)) b')
                                 {| XMap.this := m; XMap.is_bst := H3 |}
                                 (XMap.empty Trie))) by apply H1; clear H1.
          setoid_rewrite FMap_Insert_fold_add_map_eq in H5.
          rewrite map_mapsto_iff in H5; destruct_ex; intuition; subst.
          eapply H; eauto.
      }
    Qed.

    Lemma ValidUpdate_TrieBag_ValidUpdate :
      forall updateTerm,
        TrieBag_ValidUpdate updateTerm
        -> ValidUpdate updateTerm.
    Proof.
      inversion 1; subst; eauto.
    Qed.

    Hint Resolve ValidUpdate_TrieBag_ValidUpdate.

    Lemma TrieBag_bupdate_Preserves_RepInv :
      bupdate_Preserves_RepInv
        TrieBagRepInv
        TrieBag_ValidUpdate
        TrieBag_bupdate.
    Proof.
      unfold bupdate_Preserves_RepInv, TrieBagRepInv;
      intros trie search_term update_term; remember [];
      clear Heql; revert l.
      unfold TrieBag_bupdate.
      destruct search_term as [ [l | ] s].
      {
        eapply Trie_update_ind; intros; subst.
      - econstructor; inversion containerCorrect; subst; eauto.
        + pose proof (bupdate_RepInv bag search_term updateTerm) as e'; simpl in *;  rewrite e0 in e'; eapply e'; eauto.
        + intros; destruct (bupdate_correct bag search_term updateTerm);
          eauto.
          simpl in *; rewrite e0 in *; simpl in *.
          rewrite H4 in H3.
          apply in_app_or in H3; intuition.
          * eapply H1; erewrite In_partition; eauto.
          * rewrite in_map_iff in H6; destruct_ex; intuition.
            inversion valid_update; subst.
            apply H8; apply H1; rewrite In_partition; eauto.
      - econstructor; inversion containerCorrect; subst; eauto.
        + pose proof (bupdate_RepInv bag search_term updateTerm) as e'; simpl in *;  rewrite e0 in e'; eapply e'; eauto.
        + intros; destruct (bupdate_correct bag search_term updateTerm);
          eauto.
          simpl in *; rewrite e0 in *; simpl in *.
          rewrite H5 in H4.
          apply in_app_or in H4; intuition.
          * eapply H2; erewrite In_partition; eauto.
          * rewrite in_map_iff in H7; destruct_ex; intuition.
            inversion valid_update; subst.
            apply H9; apply H2; rewrite In_partition; eauto.
        + intros; destruct (X.eq_dec k key0).
          * apply find_1 in H4; eauto.
            simpl in *.
            pose proof (add_1 subtries bag'' (X.eq_sym e)) as H7; apply find_1 in H7; eauto.
            rewrite H4 in H7; injections; intros; subst.
            rewrite e2 in H; eapply H; eauto.
            eapply H3.
            apply MapsTo_1 with (x := key0).
            symmetry; eauto.
            apply find_2; eauto.
          * apply H3.
            eapply add_3; eauto.
      - simpl; econstructor; inversion containerCorrect; subst; eauto.
        + pose proof (bupdate_RepInv bag search_term updateTerm) as e'; simpl in *;  rewrite e0 in e'; eapply e'; eauto.
        + intros; destruct (bupdate_correct bag search_term updateTerm);
          eauto.
          simpl in *; rewrite e0 in *; simpl in *.
          rewrite H4 in H3.
          apply in_app_or in H3; intuition.
          * eapply H1; erewrite In_partition; eauto.
          * rewrite in_map_iff in H6; destruct_ex; intuition.
            inversion valid_update; subst.
            apply H8; apply H1; rewrite In_partition; eauto.
      }
      { intro; pattern trie, l; apply Trie_ind'; simpl; intros.
        intros; inversion containerCorrect; subst.
        case_eq (bupdate b s update_term); simpl; intros.
        econstructor.
        + pose proof (bupdate_RepInv b s update_term) as e'; simpl in *.
          rewrite H0 in e'; eapply e'; eauto.
        + apply XMap.is_bst.
        + intros; destruct (bupdate_correct b s update_term); eauto.
          simpl in *; rewrite H0 in *; simpl in *.
          intros; rewrite H5 in H1.
          apply in_app_or in H1; destruct H1.
          * intros; eapply H4.
            rewrite In_partition; eauto.
          * rewrite in_map_iff in H1; destruct H1 as [item' [item'_eq In_item'] ].
            rewrite <- item'_eq in *.
            destruct valid_update as [valid_update valid_update'].
            eapply valid_update'.
            eapply H4.
            rewrite In_partition; eauto.
        + intros; rewrite XMapfold_eq in H1.
          setoid_rewrite (fold_pair (XMap.Bst H3)) in H1; simpl in H1.
          assert (XMap.MapsTo k subtrie
                              (XMap.fold
                                 (fun (k0 : XMap.key) (m0 : Trie) (b' : XMap.t Trie) =>
                                    XMap.add k0 (snd (Trie_update' m0 s update_term)) b')
                                 {| XMap.this := m; XMap.is_bst := H3 |}
                                 (XMap.empty Trie))) by apply H1; clear H1.
          setoid_rewrite FMap_Insert_fold_add_map_eq in H5.
          rewrite map_mapsto_iff in H5; destruct_ex; intuition; subst.
          eapply H; eauto.
      }
    Qed.

    Lemma Permutation_app_fold_left
    : forall l bags,
        Permutation ((fold_left
                        (fun (a : list BagType) (p : key * Trie) =>
                           Trie_enumerate (snd p) ++ a) l
                        bags))
                    (bags ++
                          (fold_left
                             (fun (a : list BagType) (p : key * Trie) =>
                                Trie_enumerate (snd p) ++ a) l
                             [ ])).
    Proof.
      induction l; simpl; intros.
      - rewrite app_nil_r; reflexivity.
      - rewrite IHl, <- app_assoc,
        Permutation_app_comm, <- app_assoc.
        f_equiv.
        rewrite Permutation_app_comm, <- IHl, app_nil_r; reflexivity.
    Qed.

    Lemma Permutation_benumerate_fold_left
    : forall l bags,
        Permutation (List.map benumerate
                              (fold_left
                                 (fun (a : list BagType) (p : key * Trie) =>
                                    Trie_enumerate (snd p) ++ a) l
                                 bags))
                    ((List.map benumerate bags) ++
                                                (List.map benumerate (fold_left
                                                                        (fun (a : list BagType) (p : key * Trie) =>
                                                                           Trie_enumerate (snd p) ++ a) l
                                                                        [ ]))).
    Proof.
      intros; rewrite Permutation_app_fold_left, map_app; eauto.
    Qed.

    Lemma XMapfoldBst A :
      forall f m (acc : A) (WFm : bst m),
        XMapfold f m acc =
        XMap.fold f (XMap.Bst WFm) acc.
    Proof.
      intros; rewrite XMapfold_eq; reflexivity.
    Qed.

    Ltac replaceXMapfold :=
      match goal with
          |- context [XMapfold ?f ?m ?acc] =>
          let Bst_m := fresh in
          assert (bst m) as Bst_m;
            [ eauto | setoid_rewrite (XMapfoldBst f acc Bst_m)]
      end.

    Lemma XMapfindBst elt :
      forall k (m : Map elt) (WFm : bst m),
        find k m = XMap.find k (XMap.Bst WFm).
    Proof.
      reflexivity.
    Qed.

    Lemma Tries_enumerate_app_Proper
    : Proper
        (X.eq ==> eq ==> Permutation (A:=BagType) ==> Permutation (A:=BagType))
        (fun (_ : X.t) (tries : Trie) (bags : list BagType) =>
           Trie_enumerate tries ++ bags).
    Proof.
      unfold Proper, respectful; intros.
      subst; rewrite H1; reflexivity.
    Qed.

    Lemma Tries_enumerate_app_transpose_neqkey
    : transpose_neqkey (Permutation (A:=BagType))
                       (fun (_ : X.t) (tries : Trie) (bags : list BagType) =>
                          Trie_enumerate tries ++ bags).
    Proof.
      unfold transpose_neqkey; intros; rewrite Permutation_app_swap, <- app_assoc; f_equiv; apply Permutation_app_swap.
    Qed.

    Lemma benumerate_bempty_nil :
      benumerate bempty = nil.
      pose proof benumerate_empty; unfold BagEnumerateEmpty in *.
      induction (benumerate bempty); eauto.
      simpl in *; elimtype False; eapply H; eauto.
    Qed.

    Lemma Proper_KeyBasedPartitioningFunction
    : forall key, Proper (X.eq ==> eq ==> eq) (KeyBasedPartitioningFunction Trie key).
      unfold Proper, respectful; intros; subst.
      unfold KeyBasedPartitioningFunction.
      repeat find_if_inside; eauto.
      rewrite H in e; intuition.
    Qed.

    Lemma TrieBag_BagEnumerateEmpty :
      BagEnumerateEmpty TrieBag_benumerate TrieBag_bempty.
    Proof.
      intros;
      unfold BagEnumerateEmpty, TrieBag_benumerate, flatten; simpl.
      rewrite app_nil_r; apply benumerate_empty.
    Qed.

    Lemma Trie_find_TreeOK
    : forall trie st2 st1,
        TrieOK trie st1
        -> forall bag,
             List.In bag (Trie_find trie st2)
             -> RepInv bag.
    Proof.
      intros trie st2; eapply Trie_find_ind; intros; subst.
      - inversion H; subst; eauto.
        simpl in H0; intuition eauto; subst; eauto.
      - simpl in H1; intuition; subst.
        + inversion H0; subst; eauto.
        + eapply (H (st1 ++ [key0])); eauto.
      - simpl in H0; intuition; subst; eauto.
    Qed.

    Fixpoint Trie_enumerate_ind
             (P : Trie -> list BagType -> list X.t -> Prop)
             (H : forall trie st,
                    (bst (SubTries trie)
                     -> forall (k : key) (trie' : Trie),
                          MapsTo k trie' (SubTries trie) -> P trie' (Trie_enumerate trie') (st ++ [k])) -> P trie (Trie_enumerate trie) st)
             (trie : Trie)
             (st : list X.t)
             {struct trie}
    : P trie (Trie_enumerate trie) st.
    Proof.
      refine (match trie with
                | Node bag tries => _
              end).
      pose proof (@XMapfold_ind P (Trie_enumerate_ind P H) tries).
      clear Trie_enumerate_ind.
      eauto.
    Qed.

    Lemma Permute_XMapfold_cons
      : forall m l,
        XMapfold
          (fun (_ : X.t) (tries : Trie) (bags : list BagType) =>
             Trie_enumerate tries ++ bags) m l =
        (XMapfold (fun (_ : X.t) (tries : Trie) (bags : list BagType) =>
                     Trie_enumerate tries ++ bags) m []) ++ l.
    Proof.
      induction m; simpl; eauto.
      intros.
      rewrite IHm2; symmetry; rewrite IHm2.
      rewrite <- !app_assoc; f_equiv; f_equiv.
      symmetry; eauto.
    Qed.

    Lemma Trie_enumerate_RepInv
      : forall trie l,
        TrieOK trie l
        -> forall item,
          List.In item (Trie_enumerate trie)
          -> RepInv item.
    Proof.
      intros trie l; pattern trie, l; eapply Trie_ind'; simpl; intros.
      inversion H0; subst; clear H0.
      rewrite Permute_XMapfold_cons in H1; apply List.in_app_or in H1; intuition.
      - rewrite XMapfold_eq in H0.
        pose fold_spec_right as e; unfold XMap.fold in e; rewrite (e _ (XMap.Bst H5)) in H0;
        clear e.
        assert (exists k trie, List.In (k, trie)
                                       (XMap.elements (elt := Trie)
                                       {| XMap.this := m;
                                          XMap.is_bst := H5 |})
                               /\ List.In item (Trie_enumerate trie)).
        { revert H0; clear.
          induction
            (XMap.elements (elt := Trie)
                           {| XMap.this := m;
                              XMap.is_bst := H5 |}); simpl; intros; intuition.
          rewrite fold_right_app in H0; simpl in H0.
          rewrite fold_left_rev_right in H0; simpl in H0.
          unfold uncurry in *.
          rewrite Permutation_app_fold_left in H0; apply in_app_or in H0; intuition.
          apply in_app_or in H; intuition.
          destruct a; eauto.
          destruct IHl as [k [trie' [In_k In_trie] ] ].
          rewrite fold_left_rev_right; eauto.
          eexists; eauto.
          }
        destruct H1 as [k [trie' [In_k In_trie'] ] ].
        eapply (H k trie' l0); eauto.
        eapply elements_mapsto_iff with (m := XMap.Bst H5).
        eapply InA_In; eauto.
        econstructor; reflexivity.
        apply H8.
        eapply elements_mapsto_iff with (m := XMap.Bst H5).
        eapply InA_In; eauto.
        econstructor; reflexivity.
      - simpl in H0; intuition; subst; eauto.
    Qed.

    Lemma TrieBag_BagCountCorrect :
      BagCountCorrect TrieBagRepInv TrieBag_bcount TrieBag_bfind .
    Proof.
      unfold TrieBagRepInv, TrieBag_bcount, TrieBag_bfind, BagCountCorrect.
      simpl; intros; destruct search_term as [ [key | ] search_term ].
      - rewrite length_flatten.
        rewrite !foldright_compose.
        rewrite <- !fold_left_rev_right.
        rewrite map_map.
        generalize (Trie_find_TreeOK key containerCorrect).
        remember 0 as n; clear Heqn; revert n.
        induction (Trie_find container key); simpl; eauto.
        intros.
        intros; rewrite IHl by eauto.
        rewrite fold_right_app; simpl.
        rewrite bcount_correct by eauto.
        rewrite !fold_left_rev_right; simpl.
        clear; revert n; induction l; simpl; eauto with arith.
        intros; rewrite IHl; f_equal; omega.
      - rewrite length_flatten.
        remember [] as l; replace 0 with (length l) by (subst; eauto).
        clear Heql; generalize (Trie_enumerate_RepInv containerCorrect).
        induction (Trie_enumerate container); simpl; eauto.
        rewrite !foldright_compose, <- !fold_left_rev_right, map_map.
        intros; unfold compose in *; rewrite bcount_correct by eauto.
        rewrite !fold_left_rev_right.
        rewrite <- map_map, <- foldright_compose.
        unfold compose; rewrite IHl0 by eauto.
        remember (length l) as n; clear Heqn; generalize n.
        clear; induction l0; simpl; eauto with arith; intros.
        rewrite IHl0; f_equal; omega.
    Qed.

    Lemma Permutation_KeyBasedPartition
    : forall key m bst_m b,
        Permutation
          (fold
             (fun (_ : XMap.Raw.key) (trie : Trie) (a : list BagType) =>
                Trie_enumerate trie ++ a) m b)
          (XMap.fold
             (fun (_ : XMap.key) (trie : Trie) (a : list BagType) =>
                Trie_enumerate trie ++ a)
             (fst
                (partition (KeyBasedPartitioningFunction Trie key)
                           {|
                             XMap.this := m;
                             XMap.is_bst := bst_m |}))
             (XMap.fold
                (fun (_ : XMap.key) (trie : Trie) (a : list BagType) =>
                   Trie_enumerate trie ++ a)
                (snd
                   (partition (KeyBasedPartitioningFunction Trie key)
                              {|
                                XMap.this := m;
                                XMap.is_bst :=  bst_m |}))
                b)) .
    Proof.
      intros.
      pose proof (partition_Partition_simple
                    _
                    (KeyBasedPartitioningFunction Trie key0)
                    (KeyBasedPartitioningFunction_Proper _ _)
                    (XMap.Bst bst_m)) as part.
      erewrite Partition_fold with
      (f := (fun (_ : key) (trie : Trie) (a : list BagType) =>
               Trie_enumerate trie ++ a))
        (m := {| XMap.this := m; XMap.is_bst := bst_m |} )
        (i := b);
        (eauto using part, Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
    Qed.

      Lemma In_fold_left_split' :
      forall bag l acc,
        List.In bag
                (acc ++ fold_left
                     (fun (a0 : list BagType) (p : key * Trie) =>
                        Trie_enumerate (snd p) ++ a0) l
                     [ ])
        <-> List.In bag
                    ((fold_left
                        (fun (a0 : list BagType) (p : key * Trie) =>
                           Trie_enumerate (snd p) ++ a0) l
                        acc)).
    Proof.
      induction l; simpl; intros.
      - rewrite app_nil_r in *; eauto.
        reflexivity.
      - rewrite <- IHl.
        split; intros.
        rewrite <- app_assoc; apply in_or_app.
        apply in_app_or in H; intuition eauto.
        right; apply in_or_app; eauto.
        rewrite <- IHl in H0.
        rewrite <- !app_assoc in H0.
        apply in_app_or in H0; intuition.
        apply in_app_or in H; intuition.
        apply in_app_or in H0; intuition.
        apply in_or_app; intuition.
        right; rewrite <- IHl; intuition.
        apply in_or_app; intuition.
        rewrite <- IHl in H0.
        apply in_app_or in H0; intuition.
        right.
        rewrite <- IHl.
        apply in_or_app; auto.
    Qed.

    Corollary In_fold_left_split :
      forall (k : X.t) t bag l acc,
        List.In (k, bag)
                (List.map (fun bag0 : BagType => (t, bag0))
                          (acc ++ fold_left
                               (fun (a0 : list BagType) (p : key * Trie) =>
                                  Trie_enumerate (snd p) ++ a0) l
                               [ ]))
        <-> List.In (k, bag)
                    (List.map (fun bag0 : BagType => (t, bag0))
                              (fold_left
                                 (fun (a0 : list BagType) (p : key * Trie) =>
                                    Trie_enumerate (snd p) ++ a0) l
                                 acc)).
    Proof.
      intros; rewrite !in_map_iff;
      split; intros; destruct_ex; intuition;
      eexists; split; eauto.
      rewrite In_fold_left_split' in H1; eauto.
      rewrite <- In_fold_left_split' in H1; eauto.
    Qed.

    Lemma In_fold_left_map_split' :
      forall bag l acc,
        List.In bag
                (acc ++ fold_left
                     (fun (a0 : list (key * BagType)) (p : key * Trie) =>
                      List.map (fun bag0 : BagType => (fst p, bag0))
                               (Trie_enumerate (snd p)) ++ a0)
                     l
                     [ ])
        <-> List.In bag
                    (fold_left
                         (fun (a0 : list (key * BagType)) (p : key * Trie) =>
                               List.map (fun bag0 : BagType => (fst p, bag0))
                                        (Trie_enumerate (snd p)) ++ a0)
                         l
                         acc).
    Proof.
      induction l; simpl; intros.
      - rewrite app_nil_r in *; eauto.
        reflexivity.
      - rewrite <- IHl.
        split; intros.
        rewrite <- app_assoc; apply in_or_app.
        apply in_app_or in H; intuition eauto.
        right; apply in_or_app; eauto.
        rewrite <- IHl in H0.
        rewrite <- !app_assoc in H0.
        apply in_app_or in H0; intuition.
        apply in_app_or in H; intuition.
        apply in_app_or in H0; intuition.
        apply in_or_app; intuition.
        right; rewrite <- IHl; intuition.
        apply in_or_app; intuition.
        rewrite <- IHl in H0.
        apply in_app_or in H0; intuition.
        right.
        rewrite <- IHl.
        apply in_or_app; auto.
    Qed.

    Lemma Trie_add_Correct
    : forall trie item st1 st2,
        eqlistA X.eq (projection item) (st2 ++ st1)
        -> TrieOK trie st2
        -> Permutation
             (TrieBag_benumerate (Trie_add trie st1 item))
             (item :: TrieBag_benumerate trie).
    Proof.
      intros trie item st1; eapply Trie_add_ind; intros; subst.
      - destruct trie0; simpl.
        unfold TrieBag_benumerate; simpl.
        rewrite !XMapfold_eq, !fold_1 by eauto.
        rewrite Permutation_benumerate_fold_left.
        simpl; rewrite binsert_enumerate; eauto.
        simpl; constructor.
        symmetry.
        rewrite Permutation_benumerate_fold_left; simpl.
        reflexivity.
      - destruct trie0; simpl.
        unfold TrieBag_benumerate; simpl.
        replaceXMapfold.
        replaceXMapfold.
        unfold XMap.fold at 2.

        rewrite Permutation_KeyBasedPartition with (key0 := key0)
                                                     (bst_m := SubTrieMapBST H1).

        pose proof (@partition_after_KeyBasedPartition_and_add
                      _ key0 (Trie_add subtrie st' item0) (XMap.Bst (SubTrieMapBST H1)))
          as part_add.

        rewrite Partition_fold at 1;
          (eauto using part_add, Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).

        apply find_2 in e0.

        pose proof (KeyBasedPartition_fst_singleton key0 subtrie (XMap.Bst (SubTrieMapBST H1)) e0) as singleton.
        pose proof (add_Equal_simple singleton key0 (Trie_add subtrie st' item0)) as singleton'.
        rewrite (fold_Equal_simpl (eqA := @Permutation BagType) singleton')
          by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
        rewrite (fold_Equal_simpl (eqA := @Permutation BagType) singleton)
          by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
        rewrite (fold_Equal_simpl (multiple_adds _ _ _ _))
          by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
        rewrite !fold_add
          by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey, empty_In).

        rewrite fold_empty.
        rewrite !map_app.
        unfold TrieBag_benumerate in H.
        rewrite !flatten_app, (H (st2 ++ [key0])); eauto.
        rewrite <- app_assoc; simpl; eauto.
        inversion H1; subst; eauto.
      - destruct trie0; simpl.
        unfold TrieBag_benumerate; simpl.
        replaceXMapfold.
        replaceXMapfold.

        pose proof (@partition_after_KeyBasedPartition_and_add
                      _ key0 (Trie_add TrieBag_bempty st' item0) (XMap.Bst (SubTrieMapBST H1)))
          as part_add.

        pose proof (partition_Partition_simple
                      _
                      (KeyBasedPartitioningFunction Trie key0)
                      (KeyBasedPartitioningFunction_Proper _ _)
                      (XMap.Bst (SubTrieMapBST H1))) as part.

        rewrite Partition_fold at 1;
          (eauto using part_add, Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
        rewrite Partition_fold with (m := {| XMap.this := m; XMap.is_bst := H3 |} );
          (eauto using part, Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
        rewrite !fold_add;
          eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey, empty_In.
        rewrite map_app, flatten_app.
        rewrite (H (st2 ++ [key0])); simpl.
        unfold TrieBag_benumerate; simpl.
        rewrite benumerate_bempty_nil; simpl.
        reflexivity.
        rewrite <- app_assoc; eauto.
        econstructor; eauto using bempty_RepInv.
        + rewrite benumerate_bempty_nil in *; simpl in *; intuition.
        + intros; elimtype False; eapply empty_1; eauto.
        + intro H4.
          destruct H4.
          apply (@partition_iff_1 _
                                  (KeyBasedPartitioningFunction Trie key0)
                                  (Proper_KeyBasedPartitioningFunction key0)
                                  {| XMap.this := m; XMap.is_bst := SubTrieMapBST H1 |}
                                  _
                                  key0 x
                                  (refl_equal _)) in H4; intuition.
          apply find_1 in H5; eauto; simpl in *; congruence.
    Qed.

    Corollary TrieBag_BagInsertEnumerate :
      BagInsertEnumerate TrieBagRepInv TrieBag_benumerate TrieBag_binsert.
    Proof.
      unfold BagInsertEnumerate; intros; eapply Trie_add_Correct; eauto.
      simpl; reflexivity.
    Qed.

    Lemma TrieBag_enumerateOK
    : forall l st1 (bags : list (key * BagType)) k bag,
        (forall (k : X.t) (subtrie : Trie),
           InA (PX.eqke (elt:=Trie)) (k, subtrie) l ->
           TrieOK subtrie (st1 ++ [k])) ->
        (forall (k : key) (bag : BagType),
           List.In (k, bag) bags ->
           forall (item: TItem),
              List.In item (benumerate bag) ->
              Prefix (st1 ++ [k]) (projection item))
        -> List.In (k, bag) (fold_left
                          (fun (a : list (key * BagType)) (p : key * Trie) =>
                             (List.map (fun bag => (fst p, bag)) (Trie_enumerate (snd p)) ++ a)) l bags)
        -> forall (item: TItem),
              List.In item (benumerate bag) ->
              Prefix (st1 ++ [k]) (projection item).
    Proof.
      induction l; simpl; eauto.
      - intros.
        rewrite <- In_fold_left_map_split' in H1.
        rewrite <- app_assoc in H1.
        apply in_app_or in H1; intuition eauto.
        destruct a as [k' t]; simpl in *.
        assert (InA (PX.eqke (elt:=Trie)) (k', t) ((k', t) :: l))
               by (econstructor; eauto).
        generalize (H k' t H1).
        assert (k = k')
          by (revert H3; clear; induction (Trie_enumerate t);
              simpl; intro; intuition; injections; eauto).
        subst.
        apply in_map with (f := snd) in H3; rewrite map_map, map_id in H3.
        remember (st1 ++ [k']).
        setoid_rewrite <- Heql0.
        generalize bag H2 H3; clear.
        eapply (fun P H => @Trie_enumerate_ind P H t l0).
        simpl; intros.
        destruct trie; simpl in *.
        rewrite !XMapfold_eq, !fold_1 in H3; eauto.
        rewrite <- In_fold_left_split' in H3.
        apply in_app_or in H3; intuition.
        + simpl in H1; intuition; injections; subst.
          inversion H0; subst.
          apply H6 in H2; revert H2; clear.
          * revert st; induction (projection item); simpl.
            intros; inversion H2; subst.
            eexists nil; rewrite app_nil_r.
            constructor; symmetry; eauto.
            eexists nil; simpl; rewrite app_nil_r; symmetry; eauto.
        +  assert
             (forall (k : key) (trie' : Trie),
                InA (XMap.eq_key_elt (elt:=Trie)) (k,trie') (elements m) ->     List.In item (benumerate bag) ->
                List.In (t, bag)
                        (List.map (fun bag0 : BagType => (t, bag0)) (Trie_enumerate trie')) ->
                TrieOK trie' (st ++ [k]) -> Prefix (st ++ [k]) (projection item)).
           { intros; eapply H; eauto.
             eapply (@XMap.elements_2 _ (XMap.Bst (SubTrieMapBST H0))); eauto.
             apply in_map with (f := snd) in H5;
               rewrite map_map, map_id in H5; simpl in *;
               eauto.
           }
           assert (forall k' trie,
                     InA (XMap.eq_key_elt (elt:=Trie)) (k', trie) (elements m)
                     -> TrieOK trie (st ++ [k'])).
           {  revert H0; clear.
              intros; inversion H0; subst.
              apply (@XMap.elements_2 _ (XMap.Bst H4)) in H.
              apply H7 in H; simpl in H; eauto.
           }
           generalize st bag item b t H2 H3 H1 H4; clear.
           induction (elements m); simpl; intros.
           * intuition.
           * rewrite <- In_fold_left_split' in H1.
             apply in_app_or in H1; intuition eauto.
             assert (forall a b c, Prefix (a ++ [b]) c ->
                                   Prefix a c).
             {
               clear; intros; destruct H.
               exists (b :: x); rewrite <- app_assoc in H; eauto.
             }
             destruct a; eapply H0; eapply H3.
             econstructor; reflexivity.
             eauto.
             rewrite app_nil_r in H.
             eauto.
             simpl in H.
             apply in_map_iff; eauto.
             eapply H4; econstructor; eauto.
             reflexivity.
             eapply IHl; eauto.
        + eapply IHl; eauto.
          apply In_fold_left_map_split'; eauto.
    Qed.

    Lemma TrieBag_enumerateOK1
    : forall l st1 search_term bags,
        (forall (k : X.t) (subtrie : Trie),
           InA (PX.eqke (elt:=Trie)) (k, subtrie) l ->
           TrieOK subtrie (st1 ++ [k])) ->
        (forall (k : X.t) (bag : BagType) item,
           List.In (k, bag) bags
           -> List.In item (benumerate (Bag := TBag) bag)
           -> Prefix (st1 ++ [k]) (projection item))
        -> Permutation
             (List.filter (TrieBag_bfind_matcher (Some st1, search_term))
                          (flatten
                             (List.map (fun p => benumerate (snd p))
                                       (fold_left
                                          (fun (a : list (key * BagType)) (p : key * Trie) =>
                                             (List.map (fun bag => (fst p, bag)) (Trie_enumerate (snd p)) ++ a)) l bags))))
             [].
    Proof.
      induction l; simpl; eauto.
      - induction bags; simpl in *; intros; eauto.
        rewrite filter_app, IHbags; eauto.
        destruct a.
        rewrite app_nil_r.
        simpl.
        generalize (fun item => H0 _ _ item (or_introl (refl_equal _))) ; clear; simpl.
        induction (benumerate b); simpl; eauto.
        intros.
        unfold TrieBag_bfind_matcher, IsPrefix; simpl.
        destruct (Prefix_dec F.eq_dec (projection a) st1); simpl in *.
        find_if_inside; eauto.
        intros.
        pose proof (H _ (or_introl (refl_equal _))).
        elimtype False.
        generalize st1 p H0; clear.
        induction (projection a); simpl.
        + destruct st1; simpl; intros;  destruct H0; inversion H.
        + destruct st1; simpl; try congruence.
          intros; inversion p; inversion H.
          intros; eapply (IHl st1).
          destruct p; simpl in *; inversion H; subst; eexists; eauto.
          intros; destruct H0; inversion H; subst.
          eexists; eauto.
        + eauto.
      - intros; rewrite IHl; eauto.
        intros.
        apply in_app_or in H1; intuition eauto.
        destruct a.
        assert (InA (PX.eqke (elt:=Trie)) (t, t0) ((t, t0) :: l)) by
            (econstructor; eauto).
        apply H in H1; simpl in *.
        assert (k = t).
        {
          revert H3; clear; induction (Trie_enumerate t0); simpl;
          intros; intuition;  congruence.
        }
        subst.
        revert H2 H3 H1.
        clear.
        eapply (fun P H => @Trie_enumerate_ind P H t0 (st1 ++ [t])).
        simpl; intros.
        destruct trie; simpl in *.
        rewrite !XMapfold_eq, !fold_1 in H3; eauto.
        rewrite <- In_fold_left_split, map_app in H3.
        apply in_app_or in H3; intuition.
        + simpl in H0; intuition; injections; subst.
          inversion H1; subst.
          apply H6 in H2; revert H2; clear.
          * revert st; induction (projection item); simpl.
            intros; inversion H2; subst.
            eexists nil; rewrite app_nil_r.
            constructor; symmetry; eauto.
            eexists nil; simpl; rewrite app_nil_r; symmetry; eauto.
        +  assert
             (forall (k : key) (trie' : Trie),
                InA (XMap.eq_key_elt (elt:=Trie)) (k,trie') (elements m) ->     List.In item (benumerate bag) ->
                List.In (t, bag)
                        (List.map (fun bag0 : BagType => (t, bag0)) (Trie_enumerate trie')) ->
                TrieOK trie' (st ++ [k]) -> Prefix (st ++ [k]) (projection item)).
           { intros; eapply H; eauto.
             eapply (@XMap.elements_2 _ (XMap.Bst (SubTrieMapBST H1))); eauto. }
           assert (forall k' trie,
                     InA (XMap.eq_key_elt (elt:=Trie)) (k', trie) (elements m)
                     -> TrieOK trie (st ++ [k'])).
           {  revert H1; clear.
              intros; inversion H1; subst.
              apply (@XMap.elements_2 _ (XMap.Bst H4)) in H.
              apply H7 in H; simpl in H; eauto.
           }
           generalize st bag item b t H2 H3 H0 H4; clear.
           induction (elements m); simpl; intros.
           * intuition.
           * rewrite <- In_fold_left_split, map_app in H0.
             apply in_app_or in H0; intuition eauto.
             assert (forall a b c, Prefix (a ++ [b]) c ->
                                   Prefix a c).
             {
               clear; intros; destruct H.
               exists (b :: x); rewrite <- app_assoc in H; eauto.
             }
             destruct a; eapply H0; eapply H3.
             econstructor; reflexivity.
             eauto.
             rewrite app_nil_r in H.
             eauto.
             eapply H4; econstructor; eauto.
             reflexivity.
             eapply IHl; eauto.
    Qed.

    Corollary TrieBag_enumerateOK'
    : forall l st1 search_term,
        (forall (k : X.t) (subtrie : Trie),
           InA (PX.eqke (elt:=Trie)) (k, subtrie) l ->
           TrieOK subtrie (st1 ++ [k]))
        -> Permutation
             (List.filter (TrieBag_bfind_matcher (Some st1, search_term))
                          (flatten
                             (List.map benumerate
                                       (fold_left
                                          (fun (a : list (BagType)) (p : key * Trie) =>
                                             (Trie_enumerate (snd p)) ++ a) l [ ]))))
             [].
    Proof.
      intros.
      rewrite <- (@TrieBag_enumerateOK1 l st1 search_term [ ] H) by
          intuition.
      remember (@nil BagType); remember (@nil (X.t * BagType)).
      assert (List.map snd l1 = l0) by (subst; eauto).
      generalize l1 l0 H0; clear; induction l; simpl; intros.
      rewrite <- map_map with (f := snd). setoid_rewrite H0.
      reflexivity.
      rewrite <- IHl; eauto.
      rewrite map_app, map_map, map_id; simpl.
      setoid_rewrite H0; reflexivity.
    Qed.

    Global Instance Prefix_refl :
      Reflexive Prefix.
    Proof.
      intros; eexists nil; rewrite app_nil_r; reflexivity.
    Qed.

    Global Instance Prefix_trans :
      Transitive Prefix.
    Proof.
      unfold Transitive;
      intros; destruct H as [k H]; destruct H0 as [k' H0].
      eexists (k ++ k'); rewrite <- H0, <- H, <- app_assoc; reflexivity.
    Qed.

    (*Add Parametric Relation
    : (list _) (Prefix)
        reflexivity proved by reflexivity
        transitivity proved by transitivity
          as refine_rel.*)

    Lemma Prefix_app :
      forall l l',
        Prefix l (l ++ l').
    Proof.
      intros; eexists l'; reflexivity.
    Qed.

    Lemma filter_Prefix
    : forall (b : BagType) m st l search_term',
        TrieOK (Node b m) l
        -> Prefix l st
        -> Permutation (List.filter (bfind_matcher search_term') (benumerate b))
                       (List.filter (TrieBag_bfind_matcher (Some st, search_term'))
                                    (benumerate b)).
    Proof.
      intros; inversion H; subst.
      revert H0 H5; clear.
      induction (benumerate b); simpl; eauto.
      unfold TrieBag_bfind_matcher; simpl.
      intros; case_eq (Prefix_dec F.eq_dec (projection a) st); simpl; intros.
      find_if_inside; simpl; rewrite IHl0; eauto.
      assert (Prefix (projection a) l)
        by (eexists nil; rewrite app_nil_r; eauto).
      destruct n.
      rewrite H1; apply H0.
    Qed.

    Lemma filter_negb_Prefix
    : forall (b : BagType) m st l search_term',
        TrieOK (Node b m) l
        -> Prefix l st
        -> Permutation (List.filter (fun a => negb (bfind_matcher search_term' a)) (benumerate b))
                       (List.filter (fun a => negb (TrieBag_bfind_matcher (Some st, search_term') a))
                                    (benumerate b)).
    Proof.
      intros; inversion H; subst.
      revert H0 H5; clear.
      induction (benumerate b); simpl; eauto.
      unfold TrieBag_bfind_matcher; simpl.
      intros; case_eq (Prefix_dec F.eq_dec (projection a) st); simpl; intros.
      find_if_inside; simpl; rewrite IHl0; eauto.
      assert (Prefix (projection a) l)
        by (eexists nil; rewrite app_nil_r; eauto).
      destruct n.
      rewrite H1; apply H0.
    Qed.

    Lemma Prefix_cons_inv
    : forall a l l',
        Prefix (a :: l) (a :: l') -> Prefix l l'.
    Proof.
      induction l; simpl; intros.
      - eexists l'; simpl; reflexivity.
      - destruct H; inversion H; subst.
        exists x; eauto.
    Qed.

    Lemma Prefix_app_inv
    : forall a l l',
        Prefix (a ++ l) (a ++ l') -> Prefix l l'.
    Proof.
      induction a; simpl; intros; eauto.
      apply IHa; eapply Prefix_cons_inv; eauto.
    Qed.

    Lemma filter_remove_key :
      forall key' m l st' search_term,
        (forall (k : X.t) (subtrie : Trie),
           InA (PX.eqke (elt:=Trie)) (k, subtrie)
               (elements (remove key' (XMap.this m))) ->
           TrieOK subtrie (l ++ [k]))
        -> Permutation
          (flatten
             (List.map
                (fun x : BagType =>
                   List.filter
                     (TrieBag_bfind_matcher (Some (l ++ key' :: st'), search_term))
                     (benumerate x))
                (XMap.fold
                   (fun (_ : key) (trie : Trie) (a : list BagType) =>
                      Trie_enumerate trie ++ a)
                   (XMap.remove (elt:=Trie) key' m
                   )
                   []))) [].
    Proof.
      intros; unfold XMap.fold; rewrite fold_1; simpl; eauto.
      remember (@nil BagType) as bags.
      remember (@nil (key * BagType)) as bags'.
      assert (forall (k0 : key) (bag0 : BagType),
     List.In (k0, bag0) bags' ->
     forall item : TItem,
       List.In item (benumerate bag0) -> Prefix (l ++ [k0]) (projection item)) by (rewrite Heqbags'; intuition).
      generalize
           (fun k bag =>
              @TrieBag_enumerateOK
                (elements (remove key' (XMap.this m))) l bags' k bag
                H H0).
      clear H0.
      assert (bags = List.map (@snd _ _) bags')  as H0
        by (rewrite Heqbags', Heqbags; reflexivity);
        rewrite H0; clear H0.
      assert (forall (k : X.t) (subtrie : Trie),
                InA (PX.eqke (elt:=Trie)) (k, subtrie)
                    (elements (remove key' (XMap.this m))) ->
                ~X.eq k key')
        by (intros;
            rewrite <- (@elements_mapsto_iff _ (XMap.Bst (remove_bst key' (XMap.is_bst m)))) in H0;
            apply remove_mapsto_iff in H0; intuition).
      assert (forall (k : X.t) b,
                InA (PX.eqke (elt:=BagType)) (k, b) bags' ->
                ~X.eq k key')
        by (intros;
            rewrite Heqbags' in *; inversion H1).
      generalize bags' H H0 H1; clear; induction (elements (remove key' (XMap.this m))); simpl.
      - induction bags'; simpl; intros; eauto.
        rewrite IHbags'; eauto.
        destruct a; simpl in *.
        assert (~ X.eq k key') by
            (intros; eapply H1; econstructor; eauto).
        generalize (fun item => H2 k b (or_introl (refl_equal _)) item) H3;
          clear.
        induction (benumerate b); simpl; eauto; intros.
        pose proof (H _ (or_introl (refl_equal _))).
        rewrite <- IsPrefix_iff_Prefix in H0.
        unfold TrieBag_bfind_matcher, IsPrefix in *; simpl in *.
        case_eq (Prefix_dec F.eq_dec (projection a) (l ++ key' :: st')); eauto.
        intros.
        assert (Prefix (l ++ [k]) (l ++ key' :: st')).
        etransitivity; eauto.
        pose proof (Prefix_app_inv _ _ _ H2).
        destruct H4; inversion H4; subst.
        elimtype False; eapply H3; eauto.
      - intros.
        rewrite <- (IHl0 ((List.map (fun a' => (fst a, a')) (Trie_enumerate (snd a))) ++ bags')); eauto.
        rewrite map_app, map_map, map_id; reflexivity.
        intros.
        apply InA_app in H3; intuition eauto.
        assert (~X.eq k (fst a))
          by (destruct a; intro; eapply H0; eauto; econstructor).
        apply H3; revert H5; clear; induction (Trie_enumerate (snd a));
        intros; inversion H5; subst; eauto.
        destruct H0; simpl in *; eauto.
      - eapply (remove_bst _ (XMap.is_bst m)).
    Qed.

    Lemma elements_add_eq elt
    : forall k (v : elt) m,
        XMap.Equal (XMap.add k v m)
                   (XMap.add k v (XMap.remove k m)).
    Proof.
      unfold XMap.Equal; intros.
      symmetry; case_eq (XMap.find (elt:=elt) y (XMap.add k v m)); intros.
      apply find_2 in H.
      rewrite (@add_mapsto_iff _ m k y v e) in H; intuition; subst.
      apply find_1; eauto.
      exact (XMap.is_bst _).
      apply add_1; eauto.
      apply find_1; eauto.
      exact (XMap.is_bst _).
      apply add_2; eauto.
      apply remove_2; eauto.
      exact (XMap.is_bst _).
      rewrite <- not_find_in_iff in *.
      intro; apply H.
      destruct H0.
      rewrite (@add_mapsto_iff _ (XMap.remove k m) k y v x) in H0; intuition; subst.
      eexists; eapply add_1; eauto.
      rewrite (@remove_mapsto_iff _ m k y x) in H2; intuition.
      eexists; eauto.
      apply add_2; eauto.
    Qed.

    Lemma Permutation_benumerate_add
    : forall k v m,
        Permutation
          (flatten
             (List.map benumerate
                       (fold_left
                          (fun (a : list BagType) (p : XMap.key * Trie) =>
                             Trie_enumerate (snd p) ++ a) (XMap.elements (XMap.add k v m))
                          [])))
          (flatten
             (List.map benumerate
                       (Trie_enumerate v ++
                                       (fold_left
                                          (fun (a : list BagType) (p : key * Trie) =>
                                             Trie_enumerate (snd p) ++ a) (XMap.elements (XMap.remove k m))
                                          [])))).
    Proof.
      intros; pose (@XMap.fold_1 _ (XMap.add k v m) _ nil
                                 (fun _ (p : Trie) (a : list BagType) =>
                                    Trie_enumerate p ++ a)).
      simpl in e.
      rewrite <- !e.
      rewrite (fold_Equal_simpl (eqA := @Permutation BagType) (elements_add_eq k v m))
        by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
      rewrite !fold_add;
        eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey, empty_In.
      rewrite XMap.fold_1; simpl.
      f_equiv.
      eapply XMap.remove_1; reflexivity.
    Qed.

    Corollary TrieBag_enumerateOK'''
    : forall l st1 key' st' search_term,
        (forall (k : X.t) (subtrie : Trie),
           InA (PX.eqke (elt:=Trie)) (k, subtrie) l ->
           TrieOK subtrie (st1 ++ [k]))
        -> ( forall (k : X.t) (subtrie : Trie),
               InA (PX.eqke (elt:=Trie)) (k, subtrie)
                   l -> ~X.eq k key')
        -> Permutation
             (List.filter (fun a => negb (TrieBag_bfind_matcher (Some (st1 ++ key' :: st'), search_term) a))
                          (flatten
                             (List.map benumerate
                                       (fold_left
                                          (fun (a : list (BagType)) (p : key * Trie) =>
                                             (Trie_enumerate (snd p)) ++ a) l [ ]))))
             (flatten
                (List.map benumerate
                          (fold_left
                             (fun (a : list (BagType)) (p : key * Trie) =>
                                (Trie_enumerate (snd p)) ++ a) l [ ]))).
    Proof.
      intros.
      remember (@nil BagType) as bags.
      remember (@nil (key * BagType)) as bags'.
      assert (forall (k0 : key) (bag0 : BagType),
                List.In (k0, bag0) bags' ->
                forall item : TItem,
                  List.In item (benumerate bag0) -> Prefix (st1 ++ [k0]) (projection item)) by (rewrite Heqbags'; intuition).
      generalize
        (fun k bag =>
           @TrieBag_enumerateOK
             l st1 bags' k bag
             H H1).
      clear H1.
      assert (bags = List.map (@snd _ _) bags') as H1
          by (rewrite Heqbags', Heqbags; reflexivity);
        rewrite H1; clear H1.
      assert (forall (k : X.t) b,
                InA (PX.eqke (elt:=BagType)) (k, b) bags' ->
                ~X.eq k key')
        by (intros;
            rewrite Heqbags' in *; inversion H1).
      generalize bags' H H0 H1; clear; induction l; simpl; intros.
      - induction bags'; simpl; intros; eauto.
        rewrite filter_app, IHbags'; eauto; f_equiv.
        destruct a; simpl in *.
        assert (~ X.eq k key') by
            (intros; eapply H1; econstructor; eauto).
        generalize (fun item => H2 k b (or_introl (refl_equal _)) item) H3;
          clear.
        induction (benumerate b); simpl; eauto; intros.
        pose proof (H _ (or_introl (refl_equal _))).
        rewrite <- IsPrefix_iff_Prefix in H0.
        unfold TrieBag_bfind_matcher, IsPrefix in *; simpl in *.
        case_eq (Prefix_dec F.eq_dec (projection a) (st1 ++ key' :: st')); eauto.
        intros.
        assert (Prefix (st1 ++ [k]) (st1 ++ key' :: st'))
          by (etransitivity; eauto).
        pose proof (Prefix_app_inv _ _ _ H2).
        destruct H4; inversion H4; subst.
        elimtype False; eapply H3; eauto.
        simpl; intros; f_equiv.
        generalize (fun item In_item => H item (or_intror In_item)).
        generalize H3; clear; induction l; simpl; intros; eauto.
        pose proof (H _ (or_introl (refl_equal _))).
        destruct (Prefix_dec F.eq_dec (projection a) (st1 ++ key' :: st')); simpl in *; eauto.
        intros.
        assert (Prefix (st1 ++ [k]) (st1 ++ key' :: st'))
          by (etransitivity; eauto).
        apply Prefix_app_inv in H1.
        destruct H1; simpl in H1; inversion H1; subst.
        intuition.
        try rewrite IHl; eauto.
        intros; try eapply H2; eauto.
        constructor 2; eauto.
      - intros.
        pose proof (IHl ((List.map (fun a' => (fst a, a')) (Trie_enumerate (snd a))) ++ bags')) as H'.
        rewrite map_app, map_map, map_id in H'.
        rewrite <- H' at 2; clear H'; intros.
        rewrite !flatten_filter; eauto.
        destruct a; eapply H; econstructor 2; eauto.
        eapply H0; eauto.
        apply InA_app in H3; intuition eauto.
        assert (~X.eq k (fst a))
          by (destruct a; intro; eapply H0; eauto; econstructor).
        apply H3; revert H5; clear; induction (Trie_enumerate (snd a));
        intros; inversion H5; subst; eauto.
        destruct H0; simpl in *; eauto.
        eapply H2; eauto.
    Qed.

    Lemma filter_negb_remove
    : forall key m,
        XMap.Equal (filter
                      (fun (k : XMap.key) (e : Trie) =>
                         negb (KeyBasedPartitioningFunction Trie key k e))
                      m)
                   (XMap.remove key m).
    Proof.
      unfold XMap.Equal; intros.
      destruct (X.eq_dec key0 y).
      - rewrite remove_eq_o; eauto.
        rewrite <- e; unfold filter; clear y e.
        destruct m; unfold XMap.fold; rewrite fold_1; simpl; eauto.
        assert (XMap.find (elt:=Trie) key0 (XMap.empty Trie) = None).
        { rewrite <- not_find_in_iff.
          intro H; destruct H; simpl in *; eapply empty_1; eauto.
        }
        revert H.
        remember (XMap.empty Trie); generalize t; clear Heqt.
        induction (elements this); intros; simpl.
        + eauto.
        + eapply IHl.
          case_eq (negb (KeyBasedPartitioningFunction Trie key0 (fst a) (snd a)));
            intros; eauto.
          rewrite add_neq_o; eauto.
          intro; unfold KeyBasedPartitioningFunction in *.
          case_eq (F.eq_dec (fst a) key0); intros; rewrite H2 in H0;
          simpl in *; try congruence.
      - rewrite remove_neq_o by eauto.
        destruct m; unfold filter, XMap.fold; rewrite fold_1; simpl; eauto.
        case_eq (XMap.find (elt:=Trie) y {| XMap.this := this; XMap.is_bst := is_bst |}).
        + intros; apply find_2 in H.
          pose (@elements_mapsto_iff _ (XMap.Bst is_bst)) as H2; simpl in H2;
          unfold XMap.MapsTo in H2; simpl in H2; rewrite H2 in H;
          unfold XMap.elements in H; simpl in H; clear H2.
          assert (InA (XMap.eq_key_elt (elt:=Trie)) (y, t) (elements this) \/
                  InA (XMap.eq_key_elt (elt:=Trie)) (y, t) (XMap.elements (XMap.empty Trie)))
            by eauto.
          assert (forall key' v, XMap.MapsTo key' v (XMap.empty Trie) ->
                                 ~ X.eq key' key0)
            by (unfold not; intros; eapply XMap.empty_1; eauto).
          assert (forall key' v, XMap.MapsTo key' v (XMap.empty Trie) ->
                                 ~ InA X.eq key' (List.map fst (elements this)))
            by (unfold not; intros; eapply XMap.empty_1; eauto).
          assert (forall key' v, InA X.eq key' (List.map fst (elements this))
                                 -> ~ XMap.MapsTo key' v (XMap.empty Trie))
            by (unfold not; intros; eapply XMap.empty_1; eauto).
          assert (NoDupA X.eq (List.map fst (XMap.elements (elt:=_) (XMap.Bst is_bst)))).
          { pose proof (@XMap.elements_3w _ (XMap.Bst is_bst)).
            unfold XMap.eq_key, PX.eqk in H4.
            revert H4; clear; induction (XMap.elements (XMap.Bst is_bst)); intros;
            constructor; eauto;
            inversion H4; subst;
            [ | apply IHl; eauto].
            intro; apply H1; revert H; clear; induction l; intros; inversion H; subst.
            constructor; eauto.
            constructor 2; eauto.
          }
          unfold XMap.elements in H4; simpl in H4.
          revert H1 H0 H2 H3 H4.
          remember (XMap.empty Trie) as t'; generalize t'; clear Heqt' H.
          induction (elements this); intros; simpl.
          destruct t'0; apply find_1; eauto.
          apply elements_mapsto_iff; simpl in H0; intuition.
          inversion H.
          eapply IHl; simpl in *; intuition.
          * unfold KeyBasedPartitioningFunction in *.
            destruct (X.eq_dec (fst a) key0); simpl in *; eauto; try congruence.
            destruct a; simpl in *.
            eapply XMap.add_3 in H0; eauto.
          * unfold KeyBasedPartitioningFunction in *.
            destruct (X.eq_dec (fst a) key0); simpl in *; eauto; try congruence.
            eapply XMap.add_3 in H0; eauto.
          * inversion H; subst.
            destruct H5; destruct a; simpl in *; subst.
            right; rewrite <- elements_mapsto_iff; simpl.
            unfold KeyBasedPartitioningFunction in *.
            destruct (X.eq_dec k key0); simpl in *; eauto; try congruence.
            rewrite e in H0; symmetry in H0; intuition.
            apply add_1; eauto.
            eauto.
          * right; rewrite <- elements_mapsto_iff; simpl.
            unfold KeyBasedPartitioningFunction in *.
            destruct (X.eq_dec (fst a) key0); simpl in *; eauto; try congruence.
            rewrite <- elements_mapsto_iff in *; simpl; eauto.
            rewrite <- elements_mapsto_iff in *; simpl; eauto.
            apply add_2; eauto.
          * unfold KeyBasedPartitioningFunction in *.
            destruct (F.eq_dec (fst a) key0); simpl in *; eauto.
            pose proof (proj1 (add_mapsto_iff _ _ _ _ _) H0); intuition; subst.
            inversion H4; subst; eauto.
            rewrite H6 in H9; eauto.
            eapply H3; eauto.
          * unfold KeyBasedPartitioningFunction in *.
            destruct (F.eq_dec (fst a) key0); simpl in *; eauto.
            pose proof (proj1 (add_mapsto_iff _ _ _ _ _) H0); intuition; subst.
            inversion H4; subst; eauto.
            rewrite H6 in H9; eauto.
            eapply H3; eauto.
          *  unfold KeyBasedPartitioningFunction in *.
             destruct (F.eq_dec (fst a) key0); simpl in *; eauto.
             pose proof (proj1 (add_mapsto_iff _ _ _ _ _) H5); intuition; subst.
             inversion H4; subst; eauto.
             rewrite H6 in H9; eauto.
             eapply H3; eauto.
          * unfold KeyBasedPartitioningFunction in *.
            destruct (F.eq_dec (fst a) key0); simpl in *; eauto.
            pose proof (proj1 (add_mapsto_iff _ _ _ _ _) H5); intuition; subst.
            inversion H4; subst; eauto.
            rewrite H6 in H9; eauto.
            eapply H3; eauto.
          * inversion H4; eauto.
          * inversion H4; eauto.
        + intros; apply not_find_in_iff in H.
          assert (forall v, ~ InA (XMap.eq_key_elt (elt:=Trie)) (y, v) (XMap.elements (XMap.Bst is_bst)) /\
                            ~ InA (XMap.eq_key_elt (elt:=Trie)) (y, v) (XMap.elements (XMap.empty Trie))).
          { unfold not in*; split; intros.
            rewrite <- elements_mapsto_iff in H0.
            apply H; eexists v; simpl in *; apply H0.
            rewrite <- elements_mapsto_iff in H0.
            eapply XMap.empty_1; eauto.
          }
          assert (forall key' v, XMap.MapsTo key' v (XMap.empty Trie) ->
                                 ~ X.eq key' key0)
            by (unfold not; intros; eapply XMap.empty_1; eauto).
          assert (forall key' v, XMap.MapsTo key' v (XMap.empty Trie) ->
                                 ~ InA X.eq key' (List.map fst (elements this)))
            by (unfold not; intros; eapply XMap.empty_1; eauto).
          assert (forall key' v, InA X.eq key' (List.map fst (elements this))
                                 -> ~ XMap.MapsTo key' v (XMap.empty Trie))
            by (unfold not; intros; eapply XMap.empty_1; eauto).
          assert (NoDupA X.eq (List.map fst (XMap.elements (elt:=_) (XMap.Bst is_bst)))).
          { pose proof (@XMap.elements_3w _ (XMap.Bst is_bst)).
            unfold XMap.eq_key, PX.eqk in H4.
            revert H4; clear; induction (XMap.elements (XMap.Bst is_bst)); intros;
            constructor; eauto;
            inversion H4; subst;
            [ | apply IHl; eauto].
            intro; apply H1; revert H; clear; induction l; intros; inversion H; subst.
            constructor; eauto.
            constructor 2; eauto.
          }
          unfold XMap.elements in H4; simpl in H4, H0.
          unfold XMap.elements at 1 in H0; simpl in H0.
          rewrite <- not_find_in_iff.
          revert H1 H0 H2 H3 H4.
          remember (XMap.empty Trie) as t'; generalize t'; clear Heqt' H.
          induction (elements this); intros; simpl.
          unfold not; intros; destruct H as [x H].
          apply (proj2 (H0 x)).
          rewrite <- elements_mapsto_iff; eassumption.
          eapply IHl; simpl in *; intuition.
          * unfold KeyBasedPartitioningFunction in *.
            destruct (X.eq_dec (fst a) key0); simpl in *; eauto; try congruence.
            destruct a; simpl in *.
            eapply XMap.add_3 in H; eauto.
          * apply (proj1 (H0 v)); eauto.
          * unfold KeyBasedPartitioningFunction in *.
            destruct (X.eq_dec (fst a) key0); simpl in *; eauto; try congruence.
            apply (proj2 (H0 v)); eauto.
            rewrite <- elements_mapsto_iff in H.
            pose proof (proj1 (add_mapsto_iff _ _ _ _ _) H); intuition; subst.
            apply (proj1 (H0 (snd a))); econstructor.
            constructor; eauto.
            apply (proj2 (H0 v)); rewrite <- elements_mapsto_iff; eauto.
          * unfold KeyBasedPartitioningFunction in *.
            destruct (X.eq_dec (fst a) key0); simpl in *; eauto; try congruence.
            pose proof (proj1 (add_mapsto_iff _ _ _ _ _) H); intuition; subst.
            inversion H4; subst; eauto.
            rewrite H6 in H9; eauto.
            eapply H2; eauto.
          * unfold KeyBasedPartitioningFunction in *.
            destruct (F.eq_dec (fst a) key0); simpl in *; eauto.
            pose proof (proj1 (add_mapsto_iff _ _ _ _ _) H5); intuition; subst.
            inversion H4; subst; eauto.
            rewrite H6 in H9; eauto.
            eapply H3; eauto.
          * inversion H4; eauto.
    Qed.

    Hint Resolve filter_negb_Prefix filter_Prefix Prefix_app.

    Lemma TrieOK_subtrie_remove
    : forall b m l key' k subtrie,
        TrieOK (Node b m) l
        -> bst m
        -> InA (PX.eqke (elt:=Trie)) (k, subtrie)
            (elements
               (remove key' m)) ->
        TrieOK subtrie (l ++ [k]).
    Proof.
      intros.
      inversion H; subst; intros; eapply H8.
      assert (bst (remove key'
                          (XMap.this
                             {| XMap.this := m; XMap.is_bst := H0 |}))).
      apply remove_bst; eauto.
      rewrite <- (@elements_mapsto_iff _ (XMap.Bst H2)) in H1.
      simpl in H1; unfold XMap.MapsTo in H1; simpl in H1.
      eapply remove_3; eauto.
    Qed.

    Lemma TrieOK_subtrie_filter
    : forall b m l bst_m f k subtrie,
        Proper (X.eq ==> eq ==> eq) f
        -> TrieOK (Node b m) l
        -> InA (PX.eqke (elt:=Trie)) (k, subtrie)
            (XMap.elements
               (filter f
                       {| XMap.this := m; XMap.is_bst := bst_m |})) ->
        TrieOK subtrie (l ++ [k]).
    Proof.
      intros.
      inversion H0; subst; intros; eapply H8.
      rewrite <- elements_mapsto_iff in H1.
      rewrite filter_iff in H1; intuition.
    Qed.

    Hint Resolve TrieOK_subtrie_remove TrieOK_subtrie_filter.

    Lemma TrieBag_BagFindCorrect :
      BagFindCorrect TrieBagRepInv TrieBag_bfind TrieBag_bfind_matcher TrieBag_benumerate.
    Proof.
      intros container search_term.
      destruct search_term as [ [st |] search_term].
      { unfold TrieBag_bfind.
        rewrite <- (app_nil_l st) at 1.
        unfold TrieBagRepInv; remember [] as l; clear Heql; revert l.
        eapply Trie_find_ind; intros; subst; simpl.
        - rewrite !app_nil_r, <- bfind_correct by eauto.
          destruct trie; simpl.
          unfold TrieBag_benumerate; simpl.
          rewrite !XMapfold_eq, !fold_1 by eauto.
          rewrite Permutation_benumerate_fold_left, flatten_app; simpl;
          rewrite filter_app, app_nil_r; simpl.
          rewrite <- app_nil_r; f_equiv.
          + rewrite filter_Prefix; eauto; reflexivity.
          + inversion H; subst.
            eapply TrieBag_enumerateOK'; intros.
            eapply H6.
            eapply (@XMap.elements_2 _ (XMap.Bst (SubTrieMapBST' H))); eauto.
        - rewrite <- H; eauto.
          destruct trie; simpl in *.
          unfold TrieBag_benumerate; simpl.
          rewrite !XMapfold_eq, !fold_1 by eauto.
          rewrite Permutation_benumerate_fold_left, flatten_app; simpl;
          rewrite filter_app, app_nil_r; simpl; f_equiv.
          rewrite <- bfind_correct by eauto.
          + inversion H0; subst.
            rewrite filter_Prefix; eauto.
          + rewrite <- (fun H => @fold_1 _ m H (list BagType) [ ] (fun k trie a => Trie_enumerate trie ++ a)) by eauto.
            rewrite Permutation_KeyBasedPartition with (key0 := key0)
                                                         (bst_m := SubTrieMapBST H0).
            simpl.
            apply find_2 in e0.
            pose proof (KeyBasedPartition_fst_singleton key0 subtrie (XMap.Bst (SubTrieMapBST H0)) e0) as singleton.
            rewrite (fold_Equal_simpl (eqA := @Permutation BagType) singleton)
              by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
            rewrite !fold_add;
              eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey, empty_In.
            rewrite map_app, flatten_app, filter_app, <- app_nil_r.
            f_equiv.
            rewrite <- app_assoc; simpl; eauto.
            rewrite fold_empty, flatten_filter,map_map.

            rewrite (fold_Equal_simpl (eqA := @Permutation BagType) (filter_negb_remove key0 _))
              by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
            eapply filter_remove_key; eauto.
        - rewrite !app_nil_r, <- bfind_correct by eauto.
          destruct trie; simpl.
          unfold TrieBag_benumerate; simpl.
          rewrite !XMapfold_eq, !fold_1 by eauto.
          rewrite Permutation_benumerate_fold_left, flatten_app; simpl;
          rewrite filter_app, app_nil_r; simpl.
          rewrite <- app_nil_r; f_equiv.
          + rewrite filter_Prefix; eauto.
          + rewrite <- (fun H => @fold_1 _ m H (list BagType) [ ] (fun k trie a => Trie_enumerate trie ++ a)) by eauto.
            rewrite Permutation_KeyBasedPartition with (key0 := key0)
                                                         (bst_m := SubTrieMapBST' H).
            simpl in *.
            rewrite <- (@not_find_in_iff _ (XMap.Bst (SubTrieMapBST' H)) key0) in e0.
            pose proof (KeyBasedPartition_fst_singleton_None key0 (XMap.Bst (SubTrieMapBST H)) e0) as singleton.
            rewrite (fold_Equal_simpl (eqA := @Permutation BagType) singleton)
              by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
            rewrite fold_empty, flatten_filter, map_map.
            rewrite (fold_Equal_simpl (eqA := @Permutation BagType) (filter_negb_remove key0 _))
              by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
            eapply filter_remove_key; eauto.
      }
      { simpl; unfold TrieBag_bfind_matcher; simpl.
        intros.
        generalize (Trie_enumerate_RepInv containerCorrect).
        unfold TrieBag_benumerate.
        induction (Trie_enumerate container); simpl.
        - eauto.
        - intros; rewrite <- bfind_correct by eauto.
          rewrite !filter_app; f_equiv; eauto.
      }
    Qed.

    Corollary TrieBag_enumerateOK''
      : forall l st1 search_term,
        (forall (k : X.t) (subtrie : Trie),
            InA (PX.eqke (elt:=Trie)) (k, subtrie) l ->
            TrieOK subtrie (st1 ++ [k]))
        -> Permutation
             (List.filter (fun a => negb (TrieBag_bfind_matcher (Some st1, search_term) a))
                          (flatten
                             (List.map benumerate
                                       (fold_left
                                          (fun (a : list (BagType)) (p : key * Trie) =>
                                             (Trie_enumerate (snd p)) ++ a) l [ ]))))
             (flatten
                (List.map benumerate
                          (fold_left
                             (fun (a : list (BagType)) (p : key * Trie) =>
                                (Trie_enumerate (snd p)) ++ a) l [ ]))).
    Proof.
      intros; generalize (@TrieBag_enumerateOK' l st1 search_term H); clear.
      induction (flatten
                   (List.map benumerate
                             (fold_left
                                (fun (a : list (BagType)) (p : key * Trie) =>
                                   (Trie_enumerate (snd p)) ++ a) l [ ])));
        simpl; eauto.
      find_if_inside; intros; simpl.
      symmetry in H; apply Permutation_nil in H; discriminate.
      eauto.
    Qed.

    Lemma TrieOK_distinct_subtries :
      forall b m key' l k subtrie bst_m
             (OK : TrieOK (Node b m) l),
        InA (PX.eqke (elt:=Trie)) (k, subtrie)
            (elements
               (XMap.this
                  (XMap.remove (elt:=Trie) key'
                               {|
                                 XMap.this := m;
                                 XMap.is_bst := bst_m  |}))) ->
        ~ X.eq k key'.
    Proof.
      simpl; intros.
      assert (bst (remove key' m)) by eauto using remove_bst.
      rewrite <- (@elements_mapsto_iff _ (XMap.Bst (H0))) in H;
        simpl in H0.
      unfold not; intros.
      symmetry in H1; revert H1.
      pose proof (@remove_mapsto_iff  _ (XMap.Bst (bst_m))).
      eapply H1; simpl; eauto.
    Qed.

    Lemma TrieOK_distinct_subtries' :
      forall b m key' l k subtrie bst_m
             (OK : TrieOK (Node b m) l),
        InA (PX.eqke (elt:=Trie)) (k, subtrie)
            (elements
               (XMap.this
                  (filter
                     (fun (k0 : XMap.key) (e : Trie) =>
                        negb (KeyBasedPartitioningFunction Trie key' k0 e))
                     {|
                       XMap.this := m;
                       XMap.is_bst := bst_m |}))) ->
        ~ X.eq k key'.
    Proof.
      intros * OK H2.
      assert (bst ((XMap.this
                              (filter
                                 (fun (k0 : XMap.key) (e : Trie) =>
                                    negb (KeyBasedPartitioningFunction Trie key' k0 e))
                                 {|
                                   XMap.this := m;
                                   XMap.is_bst := bst_m |})))) by exact (XMap.is_bst _).
      intros; rewrite <- (@elements_mapsto_iff _ (XMap.Bst H) k subtrie) in H2.
      apply (@filter_iff _ (fun (k0 : XMap.key) (e : Trie) =>
                              negb
                                (KeyBasedPartitioningFunction Trie key' k0 e))) in H2.
      intuition.
      unfold KeyBasedPartitioningFunction in *.
      find_if_inside; simpl in *; try congruence.
      unfold Proper, respectful; intros; subst.
      unfold KeyBasedPartitioningFunction; repeat find_if_inside; eauto.
      rewrite <- e in n; intuition.
    Qed.

    Lemma Proper_negb_KeyBasedPartitioningFunction
    : forall key',
        Proper (X.eq ==> eq ==> eq)
               (fun (k0 : XMap.key) (e : Trie) =>
                  negb (KeyBasedPartitioningFunction Trie key' k0 e)).
    Proof.
      unfold Proper, respectful, KeyBasedPartitioningFunction; intros.
      repeat find_if_inside; subst; simpl; eauto.
      rewrite H in n; intuition.
    Qed.

    Instance Proper_Trie_enumerate_app
      : Proper
          (X.eq ==> eq ==> Permutation (A:=BagType) ==> Permutation (A:=BagType))
          (fun (_ : X.t) (tries : Trie) (bags : list BagType) =>
             Trie_enumerate tries ++ bags).
    Proof.
      unfold Proper, respectful, KeyBasedPartitioningFunction; intros.
      subst; rewrite H1.
      reflexivity.
    Qed.

    Lemma transpose_neqkey_Trie_enumerate_app
      : transpose_neqkey (Permutation (A:=BagType))
                         (fun (_ : X.t) (tries : Trie) (bags : list BagType) =>
                            Trie_enumerate tries ++ bags).
    Proof.
      unfold transpose_neqkey; intros.
      rewrite !app_assoc; f_equiv.
      apply Permutation_app_swap.
    Qed.

    Lemma TrieBag_BagDeleteCorrect :
      BagDeleteCorrect TrieBagRepInv TrieBag_bfind TrieBag_bfind_matcher
                       TrieBag_benumerate TrieBag_bdelete.
    Proof.
      intros container search_term.
      destruct search_term as [ [st | ] search_term].
      { unfold TrieBag_bdelete.
        split.
        {
          rewrite <- (app_nil_l st) at 2.
          revert containerCorrect.
          unfold TrieBagRepInv; remember [] as l; clear Heql; revert l.
          eapply Trie_delete_ind; intros; subst; simpl.
          - destruct (bdelete_correct (TrieNode trie) search_term0); eauto.
            destruct trie; simpl.
            unfold TrieBag_benumerate; simpl.
            rewrite !XMapfold_eq, !fold_1 by eauto.
            rewrite e0 in H.
            rewrite partition_filter_neq.
            rewrite Permutation_benumerate_fold_left, flatten_app; simpl.
            rewrite (Permutation_benumerate_fold_left _ [b]), flatten_app; simpl.
            rewrite filter_app.
            rewrite H, partition_filter_neq, !app_nil_r; simpl.
            f_equiv.
            + eapply filter_negb_Prefix; eauto; reflexivity.
            + inversion containerCorrect; subst.
              rewrite <- TrieBag_enumerateOK'' at 1.
              unfold TrieBag_bfind_matcher, IsPrefix; reflexivity.
              intros; eapply H7.
              eapply (@XMap.elements_2 _ (XMap.Bst H4)); eauto.
          - rewrite e2 in H; simpl in *.
            destruct trie; simpl in *.
            unfold TrieBag_benumerate; simpl.
            rewrite !XMapfold_eq, !fold_1 by eauto.
            rewrite partition_filter_neq.
            rewrite Permutation_benumerate_fold_left, flatten_app; simpl.
            rewrite (Permutation_benumerate_fold_left _ [b]), flatten_app; simpl.
            rewrite !filter_app.
            rewrite app_nil_r, <- app_assoc.
            f_equiv.
            + replace (bag') with (snd  (bdelete b search_term0))
                by (rewrite e0; eauto).
              destruct (bdelete_correct b search_term0); eauto.
              rewrite H0.
              rewrite partition_filter_neq.
              eapply filter_negb_Prefix; eauto; reflexivity.
            + simpl.
              rewrite <- (fun H => @fold_1 _ m H (list BagType) [ ] (fun k trie a => Trie_enumerate trie ++ a)) by eauto.
              rewrite Permutation_KeyBasedPartition with (key0 := key0)
                                                           (bst_m := SubTrieMapBST containerCorrect).
              simpl in *.
              apply find_2 in e1.
              pose proof (KeyBasedPartition_fst_singleton key0 subtrie (XMap.Bst (SubTrieMapBST containerCorrect)) e1) as singleton.
              rewrite (fold_Equal_simpl (eqA := @Permutation BagType) singleton)
                by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
              rewrite !fold_add;
                eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey, empty_In.
              rewrite flatten_filter.
              rewrite !map_app, fold_empty, !map_map.
              rewrite flatten_app.
              rewrite (Permutation_benumerate_add key0 bag'' (XMap.Bst (SubTrieMapBST containerCorrect))).
              rewrite map_app, flatten_app.
              f_equiv.
              * rewrite (H (l ++ [key0])), partition_filter_neq.
                unfold TrieBag_benumerate; rewrite flatten_filter, map_map.
                unfold TrieBag_bfind_matcher; rewrite <- app_assoc.
                repeat f_equiv.
                inversion containerCorrect; subst; eauto.
              * pose (@XMap.fold_1 _ (XMap.remove key0 (XMap.Bst (SubTrieMapBST containerCorrect)))
                                   _ nil
                                   (fun (_ : key) (trie : Trie) (a : list BagType) =>
                                      Trie_enumerate trie ++ a)).
                simpl in e;  unfold XMap.key, key in *; rewrite <- e.
                rewrite (fold_Equal_simpl (eqA := @Permutation BagType) (filter_negb_remove key0 _))
                  by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
                unfold XMap.fold.
                rewrite !fold_1.
                rewrite <- TrieBag_enumerateOK'''.
                rewrite flatten_filter.
                rewrite map_map.
                unfold TrieBag_bfind_matcher, IsPrefix; simpl.
                f_equiv.
                intros; eapply TrieOK_subtrie_remove; simpl in *;
                eauto using Proper_negb_KeyBasedPartitioningFunction.
                intros; eapply TrieOK_distinct_subtries; eauto.
                exact (XMap.is_bst _).
          - destruct trie; simpl in *.
            unfold TrieBag_benumerate; simpl.
            rewrite !XMapfold_eq, !fold_1 by eauto.
            rewrite partition_filter_neq.
            rewrite Permutation_benumerate_fold_left, flatten_app; simpl.
            rewrite (Permutation_benumerate_fold_left _ [b]), flatten_app; simpl.
            rewrite !filter_app.
            rewrite app_nil_r, <- app_assoc.
            f_equiv.
            + replace (bag') with (snd  (bdelete b search_term0))
                by (rewrite e0; eauto).
              destruct (bdelete_correct b search_term0); eauto.
              rewrite H.
              rewrite partition_filter_neq.
              eapply filter_negb_Prefix; eauto; reflexivity.
            + simpl.
              rewrite <- (fun H => @fold_1 _ m H (list BagType) [ ] (fun k trie a => Trie_enumerate trie ++ a)) by eauto.
              rewrite Permutation_KeyBasedPartition with (key0 := key0)
                                                           (bst_m := SubTrieMapBST containerCorrect).
              simpl.
              rewrite <- (@not_find_in_iff _ (XMap.Bst (SubTrieMapBST' containerCorrect)) key0) in e1.
              pose proof (KeyBasedPartition_fst_singleton_None key0 (XMap.Bst (SubTrieMapBST containerCorrect)) e1) as singleton.
              rewrite (fold_Equal_simpl (eqA := @Permutation BagType) singleton)
                by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
              rewrite !fold_empty;
                eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey, empty_In.
              unfold XMap.fold; rewrite !fold_1.
              rewrite <- TrieBag_enumerateOK''' at 1.
              unfold TrieBag_bfind_matcher, IsPrefix.
              f_equiv.
              intros; eapply TrieOK_subtrie_filter; simpl in *;
              eauto using Proper_negb_KeyBasedPartitioningFunction.
              intros; eapply TrieOK_distinct_subtries'; eauto.
              exact (XMap.is_bst _).
        }
        { rewrite <- (app_nil_l st) at 2.
          revert containerCorrect.
          unfold TrieBagRepInv; remember [] as l; clear Heql; revert l.
          eapply Trie_delete_ind; intros; subst; simpl.
          - destruct (bdelete_correct (TrieNode trie) search_term0); eauto.
            destruct trie; simpl.
            unfold TrieBag_benumerate; simpl.
            rewrite !XMapfold_eq, !fold_1 by eauto.
            rewrite e0 in H.
            rewrite partition_filter_eq.
            rewrite Permutation_benumerate_fold_left, flatten_app; simpl.
            rewrite filter_app.
            replace deletedItems with (fst (bdelete b search_term0)) by
                (simpl in *; rewrite e0; eauto).
            destruct (bdelete_correct b search_term0); eauto.
            rewrite H2, partition_filter_eq; simpl.
            rewrite <- app_nil_r at 1.
            f_equiv.
            + inversion containerCorrect; subst.
              revert H7; clear.
              induction (benumerate b); simpl; eauto.
              unfold TrieBag_bfind_matcher, IsPrefix.
              intros; case_eq (Prefix_dec F.eq_dec (projection a) l); simpl; intros.
              find_if_inside; simpl; rewrite IHl0; eauto.
              rewrite app_nil_r, H; simpl; eauto.
              rewrite andb_false_r; eauto.
              find_if_inside.
              simpl; rewrite app_nil_r, H; simpl.
              assert (Prefix (projection a) l)
                by (eexists nil; rewrite app_nil_r; eauto).
              rewrite <- IsPrefix_iff_Prefix in H0; simpl in *; rewrite H in H0; congruence.
              assert (Prefix (projection a) l)
                by (eexists nil; rewrite app_nil_r; eauto).
              rewrite <- IsPrefix_iff_Prefix in H0; simpl in *; rewrite H in H0; congruence.
            + inversion containerCorrect; subst.
              rewrite TrieBag_enumerateOK' at 1; eauto.
              rewrite app_nil_r.
              intros; eapply H9.
              eapply (@XMap.elements_2 _ (XMap.Bst H6)); eauto.
          - rewrite e2 in H; simpl in *.
            destruct trie; simpl in *.
            unfold TrieBag_benumerate; simpl.
            rewrite !XMapfold_eq, !fold_1 by eauto.
            rewrite partition_filter_eq.
            rewrite Permutation_benumerate_fold_left, flatten_app; simpl.
            rewrite !filter_app; simpl.
            f_equiv.
            + replace deletedItems with (fst (bdelete b search_term0))
                by (rewrite e0; eauto).
              destruct (bdelete_correct b search_term0); eauto.
              rewrite H1, partition_filter_eq, app_nil_r.
              inversion containerCorrect; subst.
              intros; eapply filter_Prefix; eauto; reflexivity.
            + rewrite (H (l ++ [key0])); simpl; eauto.
              rewrite partition_filter_eq.
              rewrite <- (fun H => @fold_1 _ m H (list BagType) [ ] (fun k trie a => Trie_enumerate trie ++ a)) by eauto.
              rewrite Permutation_KeyBasedPartition with (key0 := key0)
                                                           (bst_m := SubTrieMapBST containerCorrect).
              simpl.
              apply find_2 in e1.
              pose proof (KeyBasedPartition_fst_singleton key0 subtrie (XMap.Bst (SubTrieMapBST containerCorrect)) e1) as singleton.
              rewrite (fold_Equal_simpl (eqA := @Permutation BagType) singleton)
                by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
              rewrite !fold_add;
                eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey, empty_In.
              rewrite flatten_filter.
              rewrite !map_app, fold_empty, !map_map.
              rewrite flatten_app.
              rewrite <- app_nil_r at 1.
              f_equiv.
              * unfold TrieBag_benumerate; rewrite flatten_filter, map_map, <- app_assoc; reflexivity.
              * rewrite <- filter_remove_key; eauto.
                rewrite (fold_Equal_simpl (eqA := @Permutation BagType) (filter_negb_remove key0 _))
                  by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
                eauto.
                simpl; eauto.
          - destruct trie; simpl in *.
            unfold TrieBag_benumerate; simpl.
            rewrite !XMapfold_eq, !fold_1 by eauto.
            rewrite partition_filter_eq.
            rewrite Permutation_benumerate_fold_left, flatten_app; simpl.
            rewrite !filter_app.
            rewrite <- app_nil_r at 1.
            f_equiv.
            + replace deletedItems with (fst (bdelete b search_term0))
                by (rewrite e0; eauto).
              destruct (bdelete_correct b search_term0); eauto.
              rewrite H0, partition_filter_eq, app_nil_r.
              eapply filter_Prefix; eauto.
            + simpl.
              rewrite <- (fun H => @fold_1 _ m H (list BagType) [ ] (fun k trie a => Trie_enumerate trie ++ a)) by eauto.
              rewrite Permutation_KeyBasedPartition with (key0 := key0)
                                                           (bst_m := SubTrieMapBST containerCorrect).
              rewrite <- (@not_find_in_iff _ (XMap.Bst (SubTrieMapBST' containerCorrect)) key0) in e1.
              pose proof (KeyBasedPartition_fst_singleton_None key0 (XMap.Bst (SubTrieMapBST containerCorrect)) e1) as singleton.
              rewrite (fold_Equal_simpl (eqA := @Permutation BagType) singleton)
                by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
              rewrite !fold_empty;
                eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey, empty_In.
              simpl.
              rewrite (fold_Equal_simpl (eqA := @Permutation BagType) (filter_negb_remove key0 _))
                by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
              rewrite <- filter_remove_key, flatten_filter, map_map; eauto.
        }
      }
      { unfold TrieBag_bfind_matcher; simpl.
        unfold TrieBagRepInv.
        pattern container, (@nil X.t) ; apply Trie_ind'; simpl; intros.
        unfold TrieBag_benumerate; simpl.
        intros; inversion containerCorrect; subst.
        case_eq (bdelete b search_term); simpl; intros.
        destruct (bdelete_correct b search_term); eauto.
        rewrite H0 in H1, H5; simpl in H1, H5.
        rewrite (Permute_XMapfold_cons m [b]), Permute_XMapfold_cons with (l := [b0]).
        rewrite !map_app, !flatten_app, !partition_app; simpl.
        rewrite !app_nil_r.
        split.
        - rewrite H1; f_equiv.
          rewrite !XMapfold_eq.
          setoid_rewrite (fold_pair (XMap.Bst H3)); simpl.
          rewrite fold_spec_right.
          pose fold_spec_right as e; unfold XMap.fold in e; rewrite (e _ (XMap.Bst H3));
          clear e.
          assert (forall k trie,
                     InA (@XMap.eq_key_elt _)
                         (k, trie)
                         (rev
                            (XMap.elements (elt:=Trie)
                                           {| XMap.this := m; XMap.is_bst := H3 |}))
                     -> Permutation (TrieBag_benumerate (snd (Trie_delete' trie search_term)))
                                    (snd
                                       (List.partition
                                          (fun item : TItem => bfind_matcher search_term item)
                                          (TrieBag_benumerate trie)))).
          { intros; eapply H; eauto using elements_mapsto_iff.
            pose elements_mapsto_iff as e; unfold XMap.MapsTo in e; rewrite (e _ (XMap.Bst H3));
            clear e.
            rewrite <- InA_rev; eauto with typeclass_instances.
            eapply H6.
            eapply (@elements_mapsto_iff _ (XMap.Bst H3)).
            eapply InA_rev; eauto with typeclass_instances.
          }
          generalize H7; clear.
          assert (NoDupA (@XMap.eq_key _)
                         (rev
                            (XMap.elements (elt:=Trie) {| XMap.this := m; XMap.is_bst := H3 |})))
          by (apply NoDupA_rev; eauto with typeclass_instances;
              eapply XMap.elements_3w).
          revert H.
          induction (rev
                       (XMap.elements (elt:=Trie) {| XMap.this := m; XMap.is_bst := H3 |}));
            simpl; intros; eauto.
          unfold uncurry.
          pose fold_add as e; unfold XMap.fold, XMap.add in e; simpl in e.
          rewrite e; clear e.
          rewrite !map_app, !flatten_app, !partition_app; simpl.
          unfold TrieBag_benumerate in H7.
          rewrite H7 with (k := fst a); f_equiv; eauto.
          rewrite <- IHl; eauto.
          inversion H; eauto.
          intros; eapply H7; simpl; econstructor 2; eauto.
          econstructor; destruct a; simpl; reflexivity.
          eauto with typeclass_instances.
          eauto with typeclass_instances.
          eauto using transpose_neqkey_Trie_enumerate_app.
          inversion H; subst; intro; apply H2.
          unfold XMap.In, In0 in H0.
          revert H0; clear; induction l; simpl.
          + intros; destruct H0; inversion H.
          + intros; destruct H0.
            pose add_mapsto_iff as e; unfold XMap.add, XMap.MapsTo in e; simpl in e;
            rewrite e in H; clear e.
            intuition.
            * econstructor 1; symmetry; apply H.
            * eauto.
        - rewrite H5, Permutation_app_swap; f_equiv.
          rewrite !XMapfold_eq.
          setoid_rewrite (fold_pair (XMap.Bst H3)); simpl.
          rewrite fold_spec_right.
          pose fold_spec_right as e; unfold XMap.fold in e; rewrite (e _ (XMap.Bst H3));
          clear e.
          assert (forall k trie,
                     InA (@XMap.eq_key_elt _)
                         (k, trie)
                         (rev
                            (XMap.elements (elt:=Trie)
                                           {| XMap.this := m; XMap.is_bst := H3 |}))
                     -> Permutation ((fst (Trie_delete' trie search_term)))
                                    (fst
                                       (List.partition
                                          (fun item : TItem => bfind_matcher search_term item)
                                          (TrieBag_benumerate trie)))).
          { intros; eapply H; eauto using elements_mapsto_iff.
            pose elements_mapsto_iff as e; unfold XMap.MapsTo in e; rewrite (e _ (XMap.Bst H3));
            clear e.
            rewrite <- InA_rev; eauto with typeclass_instances.
            eapply H6.
            eapply (@elements_mapsto_iff _ (XMap.Bst H3)).
            eapply InA_rev; eauto with typeclass_instances.
          }
          generalize H7; clear.
          assert (NoDupA (@XMap.eq_key _)
                         (rev
                            (XMap.elements (elt:=Trie) {| XMap.this := m; XMap.is_bst := H3 |})))
          by (apply NoDupA_rev; eauto with typeclass_instances;
              eapply XMap.elements_3w).
          revert H.
          induction (rev
                       (XMap.elements (elt:=Trie) {| XMap.this := m; XMap.is_bst := H3 |}));
            simpl; intros; eauto.
          unfold uncurry.
          rewrite !map_app, !flatten_app, !partition_app; simpl.
          unfold TrieBag_benumerate in H7.
          rewrite H7 with (k := fst a); f_equiv; eauto.
          rewrite <- IHl; eauto.
          inversion H; eauto.
          econstructor; destruct a; simpl; reflexivity.
      }
    Qed.

    Lemma TrieBag_BagUpdateCorrect :
      BagUpdateCorrect TrieBagRepInv TrieBag_ValidUpdate
                       TrieBag_bfind TrieBag_bfind_matcher
                       TrieBag_benumerate bupdate_transform TrieBag_bupdate.
    Proof.
      intros container search_term.
      destruct search_term as [ [st | ] search_term].
      {
        unfold TrieBag_bupdate.
        split.
        {
          rewrite <- (app_nil_l st); rewrite app_nil_l at 1.
          revert containerCorrect.
          unfold TrieBagRepInv; remember [] as l; clear Heql; revert l valid_update.
          eapply Trie_update_ind; intros; subst; simpl.
          - destruct (bupdate_correct (TrieNode trie) search_term0 updateTerm); eauto.
            destruct trie; simpl.
            rewrite partition_filter_neq, partition_filter_eq.
            unfold TrieBag_benumerate; simpl.
            rewrite !XMapfold_eq, !fold_1 by eauto.
            rewrite e0 in H, H0; simpl in *.
            rewrite Permutation_benumerate_fold_left, flatten_app; simpl.
            rewrite (Permutation_benumerate_fold_left _ [b]), flatten_app; simpl.
            rewrite H, partition_filter_neq,
            partition_filter_eq, !app_nil_r, !filter_app, <- !app_assoc ; simpl.
            f_equiv.
            + eapply filter_negb_Prefix; eauto; reflexivity.
            + symmetry.
              rewrite map_app, Permutation_app_swap, <- app_assoc; f_equiv.
              f_equiv.
              * symmetry; eapply filter_Prefix; eauto; reflexivity.
              * inversion containerCorrect; subst.
                rewrite TrieBag_enumerateOK'; simpl.
                rewrite <- TrieBag_enumerateOK'' at 2.
                unfold TrieBag_bfind_matcher, IsPrefix; reflexivity.
                intros; eapply H7; eapply (@elements_mapsto_iff _ (XMap.Bst H4)); eauto.
                intros; eapply H7; eapply (@elements_mapsto_iff _ (XMap.Bst H4)); eauto.
          - rewrite e2 in H; simpl in *.
            destruct trie; simpl in *.
            unfold TrieBag_benumerate; simpl.
            rewrite !XMapfold_eq, !fold_1 by eauto.
            rewrite partition_filter_neq, partition_filter_eq.
            rewrite Permutation_benumerate_fold_left, flatten_app; simpl.
            rewrite (Permutation_benumerate_fold_left _ [b]), flatten_app; simpl.
            rewrite !filter_app.
            rewrite app_nil_r, <- !app_assoc; simpl.
            rewrite map_app.
            replace (bag') with (snd  (bupdate b search_term0 updateTerm))
              by (rewrite e0; eauto).
            destruct (bupdate_correct b search_term0 updateTerm); eauto.
            rewrite H0, partition_filter_neq, partition_filter_eq, <- !app_assoc.
            f_equiv.
            + eapply filter_negb_Prefix; eauto; reflexivity.
            + symmetry; rewrite Permutation_app_swap, <- app_assoc.
              f_equiv.
              * symmetry; f_equiv; eapply filter_Prefix; eauto.
              * rewrite <- (fun H => @fold_1 _ m H (list BagType) [ ] (fun k trie a => Trie_enumerate trie ++ a)) by eauto.
                rewrite Permutation_KeyBasedPartition with (key0 := key0)
                                                             (bst_m := SubTrieMapBST containerCorrect).
                rewrite (Permutation_benumerate_add key0 bag'' (XMap.Bst (SubTrieMapBST containerCorrect))).
                rewrite map_app, flatten_app.
                rewrite (H (l ++ [key0])), partition_filter_neq, partition_filter_eq.
                rewrite <- app_assoc.
                symmetry; rewrite Permutation_app_swap; symmetry.
                rewrite <- app_assoc.
                f_equiv.
                { simpl.
                  apply find_2 in e1.
                  pose proof (KeyBasedPartition_fst_singleton key0 subtrie (XMap.Bst (SubTrieMapBST containerCorrect)) e1) as singleton.
                  rewrite (fold_Equal_simpl (eqA := @Permutation BagType) singleton)
                    by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
                  rewrite !fold_add;
                    eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey, empty_In.
                  rewrite flatten_filter.
                  rewrite !map_app, fold_empty, !map_map.
                  rewrite flatten_app.
                  rewrite Permutation_app_swap, map_app.
                  rewrite (fold_Equal_simpl (eqA := @Permutation BagType) (filter_negb_remove key0 _))
                    by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
                  rewrite filter_remove_key; eauto.
                  simpl.
                  unfold TrieBag_benumerate.
                  rewrite <- map_map.
                  rewrite flatten_filter, map_flatten.
                  setoid_rewrite map_id; setoid_rewrite map_id.
                  rewrite map_map, <- app_assoc; reflexivity.
                }
                simpl.
                rewrite flatten_filter, map_map.
                apply find_2 in e1.
                pose proof (KeyBasedPartition_fst_singleton key0 subtrie (XMap.Bst (SubTrieMapBST containerCorrect)) e1) as singleton.
                rewrite (fold_Equal_simpl (eqA := @Permutation BagType) singleton)
                  by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
                rewrite !fold_add;
                  eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey, empty_In.
                rewrite map_app, flatten_app.
                symmetry; rewrite Permutation_app_swap; symmetry.
                f_equiv.
                { unfold TrieBag_benumerate;
                  rewrite <- map_map.
                  rewrite flatten_filter, <- app_assoc; simpl; reflexivity.
                }
                rewrite fold_empty.
                rewrite (fold_Equal_simpl (eqA := @Permutation BagType) (filter_negb_remove key0 _))
                  by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
                unfold XMap.fold, XMap.remove, XMap.elements; simpl.
                rewrite fold_1; simpl.
                rewrite <- TrieBag_enumerateOK'''; eauto.
                rewrite flatten_filter, map_map; unfold TrieBag_bfind_matcher, IsPrefix; reflexivity; eauto.
                intros; eapply TrieOK_distinct_subtries; eauto.
                apply remove_bst.
                eauto.
                eauto.
                eauto.
          - destruct trie; simpl in *.
            unfold TrieBag_benumerate; simpl.
            rewrite !XMapfold_eq, !fold_1 by eauto.
            rewrite partition_filter_neq, partition_filter_eq.
            rewrite Permutation_benumerate_fold_left, flatten_app; simpl.
            rewrite (Permutation_benumerate_fold_left _ [b]), flatten_app; simpl.
            rewrite !filter_app.
            rewrite app_nil_r, <- !app_assoc; simpl.
            rewrite map_app.
            replace (bag') with (snd  (bupdate b search_term0 updateTerm))
              by (rewrite e0; eauto).
            destruct (bupdate_correct b search_term0 updateTerm); eauto.
            rewrite H, partition_filter_neq, partition_filter_eq, <- !app_assoc.
            f_equiv.
            + eapply filter_negb_Prefix; eauto; reflexivity.
            + symmetry; rewrite Permutation_app_swap, <- app_assoc.
              f_equiv.
              * rewrite filter_Prefix; eauto; reflexivity.
              * simpl.
                rewrite <- (fun H => @fold_1 _ m H (list BagType) [ ] (fun k trie a => Trie_enumerate trie ++ a)) by eauto.
                rewrite Permutation_KeyBasedPartition with (key0 := key0)
                                                             (bst_m := SubTrieMapBST containerCorrect).
                simpl.
                rewrite <- (@not_find_in_iff _ (XMap.Bst (SubTrieMapBST' containerCorrect)) key0) in e1.
                pose proof (KeyBasedPartition_fst_singleton_None key0 (XMap.Bst (SubTrieMapBST containerCorrect)) e1) as singleton.
                rewrite (fold_Equal_simpl (eqA := @Permutation BagType) singleton)
                  by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
                rewrite !fold_empty;
                  eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey, empty_In.
                rewrite <- app_nil_l; f_equiv.
                {
                  replace (@nil TItem) with (List.map (bupdate_transform updateTerm) (@nil _)) by
                      reflexivity.
                  f_equiv.
                  rewrite (fold_Equal_simpl (eqA := @Permutation BagType) (filter_negb_remove key0 _))
                    by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
                  rewrite <- filter_remove_key; eauto.
                  rewrite flatten_filter, map_map; eauto.
                  eauto.
                }
                unfold XMap.fold; symmetry.
                rewrite fold_1, <- TrieBag_enumerateOK''' at 1.
                rewrite fold_1; unfold TrieBag_bfind_matcher, IsPrefix; eauto.
                exact (XMap.is_bst _).
                eauto using Proper_negb_KeyBasedPartitioningFunction.
                intros; eapply TrieOK_distinct_subtries'; eauto.
                exact (XMap.is_bst _).
        }
        {
          rewrite <- (app_nil_l st); rewrite app_nil_l at 1.
          revert containerCorrect.
          unfold TrieBagRepInv; remember [] as l; clear Heql; revert l valid_update.
          eapply Trie_update_ind; intros; subst; simpl.
          - destruct (bupdate_correct (TrieNode trie) search_term0 updateTerm); eauto.
            destruct trie; simpl.
            rewrite partition_filter_eq.
            unfold TrieBag_benumerate; simpl.
            rewrite !XMapfold_eq, !fold_1 by eauto.
            rewrite e0 in H, H0; simpl in *.
            rewrite Permutation_benumerate_fold_left, flatten_app; simpl.
            rewrite H0, partition_filter_eq, !app_nil_r, !filter_app ; simpl.
            rewrite <- app_nil_r at 1.
            f_equiv.
            + rewrite filter_Prefix; eauto; reflexivity.
            + inversion containerCorrect; subst.
              rewrite TrieBag_enumerateOK' at 1; eauto.
              intros; eapply H7.
              eapply (@XMap.elements_2 _ (XMap.Bst H4)); eauto.
          - rewrite e2 in H; simpl in *.
            destruct trie; simpl in *.
            unfold TrieBag_benumerate; simpl.
            rewrite !XMapfold_eq, !fold_1 by eauto.
            rewrite partition_filter_eq.
            rewrite Permutation_benumerate_fold_left, flatten_app; simpl.
            rewrite !filter_app, app_nil_r; simpl.
            replace (updatedItems) with (fst (bupdate b search_term0 updateTerm))
              by (rewrite e0; eauto).
            destruct (bupdate_correct b search_term0 updateTerm); eauto.
            rewrite H1, partition_filter_eq.
            f_equiv.
            + rewrite filter_Prefix; eauto; reflexivity.
            + rewrite (H (l ++ [key0])); simpl; eauto.
              rewrite partition_filter_eq.
              rewrite <- (fun H => @fold_1 _ m H (list BagType) [ ] (fun k trie a => Trie_enumerate trie ++ a)) by eauto.
              rewrite Permutation_KeyBasedPartition with (key0 := key0)
                                                           (bst_m := SubTrieMapBST containerCorrect).
              simpl.
              apply find_2 in e1.
              pose proof (KeyBasedPartition_fst_singleton key0 subtrie (XMap.Bst (SubTrieMapBST containerCorrect)) e1) as singleton.
              rewrite (fold_Equal_simpl (eqA := @Permutation BagType) singleton)
                by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
              rewrite !fold_add;
                eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey, empty_In.
              rewrite flatten_filter.
              rewrite !map_app, fold_empty, !map_map.
              rewrite flatten_app.
              rewrite <- app_nil_r at 1.
              f_equiv.
              * unfold TrieBag_benumerate; rewrite flatten_filter, map_map, <- app_assoc; reflexivity.
              * rewrite <- filter_remove_key; eauto.
                rewrite (fold_Equal_simpl (eqA := @Permutation BagType) (filter_negb_remove key0 _))
                  by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
                eauto.
                eauto.
          - destruct trie; simpl in *.
            unfold TrieBag_benumerate; simpl.
            rewrite !XMapfold_eq, !fold_1 by eauto.
            rewrite partition_filter_eq.
            rewrite Permutation_benumerate_fold_left, flatten_app; simpl.
            rewrite !filter_app, app_nil_r; simpl.
            replace (updatedItems) with (fst (bupdate b search_term0 updateTerm))
              by (rewrite e0; eauto).
            destruct (bupdate_correct b search_term0 updateTerm); eauto.
            rewrite H0, partition_filter_eq.
            rewrite <- app_nil_r at 1.
            f_equiv.
            + rewrite filter_Prefix; eauto.
            + simpl.
              rewrite <- (fun H => @fold_1 _ m H (list BagType) [ ] (fun k trie a => Trie_enumerate trie ++ a)) by eauto.
              rewrite Permutation_KeyBasedPartition with (key0 := key0)
                                                           (bst_m := SubTrieMapBST containerCorrect).
              rewrite <- (@not_find_in_iff _ (XMap.Bst (SubTrieMapBST' containerCorrect)) key0) in e1.
              pose proof (KeyBasedPartition_fst_singleton_None key0 (XMap.Bst (SubTrieMapBST containerCorrect)) e1) as singleton.
              rewrite (fold_Equal_simpl (eqA := @Permutation BagType) singleton)
                by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
              rewrite !fold_empty;
                eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey, empty_In.
              simpl.
              rewrite (fold_Equal_simpl (eqA := @Permutation BagType) (filter_negb_remove key0 _))
                by (eauto using Permutation_Equivalence, Tries_enumerate_app_Proper, Tries_enumerate_app_transpose_neqkey).
              rewrite <- filter_remove_key; eauto.
              rewrite flatten_filter, map_map; eauto.
              eauto.
        }
      }
      { unfold TrieBag_bfind_matcher; simpl.
        unfold TrieBagRepInv.
        pattern container, (@nil X.t) ; apply Trie_ind'; simpl; intros.
        unfold TrieBag_benumerate; simpl.
        intros; inversion containerCorrect; subst.
        case_eq (bupdate b search_term update_term); simpl; intros.
        destruct (bupdate_correct b search_term update_term); eauto.
        rewrite H0 in H1, H5; simpl in H1, H5.
        rewrite (Permute_XMapfold_cons m [b]), Permute_XMapfold_cons with (l := [b0]).
        rewrite !map_app, !flatten_app, !partition_app; simpl.
        rewrite !app_nil_r.
        split.
        - rewrite H1.
          rewrite app_assoc.
          symmetry.
          rewrite (Permutation_app_swap).
          symmetry.
          rewrite <- !app_assoc.
          rewrite (Permutation_app_swap (snd _)).
          rewrite !app_assoc, map_app.
          f_equiv.
          symmetry; rewrite Permutation_app_swap, app_assoc.
          f_equiv.
          rewrite !XMapfold_eq.
          symmetry.
          setoid_rewrite (fold_pair (XMap.Bst H3)); simpl.
          rewrite fold_spec_right.
          pose fold_spec_right as e; unfold XMap.fold in e; rewrite (e _ (XMap.Bst H3));
          clear e.
          assert (forall k trie,
                     InA (@XMap.eq_key_elt _)
                         (k, trie)
                         (rev
                            (XMap.elements (elt:=Trie)
                                           {| XMap.this := m; XMap.is_bst := H3 |}))
                     -> Permutation (TrieBag_benumerate (snd (Trie_update' trie search_term update_term)))
                                    (snd
                                       (List.partition
                                          (fun item : TItem => bfind_matcher search_term item)
                                          (TrieBag_benumerate trie))
                                          ++ List.map (bupdate_transform update_term)
                                          (fst
                                             (List.partition
                                                (fun item : TItem => bfind_matcher search_term item)
                                                (TrieBag_benumerate trie)))
                 )).
          { intros; eapply H; eauto using elements_mapsto_iff.
            pose elements_mapsto_iff as e; unfold XMap.MapsTo in e; rewrite (e _ (XMap.Bst H3));
            clear e.
            rewrite <- InA_rev; eauto with typeclass_instances.
            eapply H6.
            eapply (@elements_mapsto_iff _ (XMap.Bst H3)).
            eapply InA_rev; eauto with typeclass_instances.
          }
          generalize H7; clear.
          assert (NoDupA (@XMap.eq_key _)
                         (rev
                            (XMap.elements (elt:=Trie) {| XMap.this := m; XMap.is_bst := H3 |})))
          by (apply NoDupA_rev; eauto with typeclass_instances;
              eapply XMap.elements_3w).
          revert H.
          induction (rev
                       (XMap.elements (elt:=Trie) {| XMap.this := m; XMap.is_bst := H3 |}));
            simpl; intros; eauto.
          unfold uncurry.
          pose fold_add as e; unfold XMap.fold, XMap.add in e; simpl in e.
          rewrite e; clear e.
          rewrite !map_app, !flatten_app, !partition_app; simpl.
          unfold TrieBag_benumerate in H7.
          rewrite H7 with (k := fst a); eauto with typeclass_instances.
          rewrite <- !app_assoc; f_equiv; eauto.
          rewrite IHl.
          rewrite Permutation_app_swap, <- app_assoc, map_app.
          f_equiv.
          rewrite Permutation_app_swap; f_equiv.
          inversion H; eauto.
          intros; eapply H7; econstructor 2; eauto.
          destruct a; econstructor 1; reflexivity.
          eauto with typeclass_instances.
          eauto with typeclass_instances.
          eauto using transpose_neqkey_Trie_enumerate_app.
          inversion H; subst; intro; apply H2.
          unfold XMap.In, In0 in H0.
          revert H0; clear; induction l; simpl.
          + intros; destruct H0; inversion H.
          + intros; destruct H0.
            pose add_mapsto_iff as e; unfold XMap.add, XMap.MapsTo in e; simpl in e;
            rewrite e in H; clear e.
            intuition.
            * econstructor 1; symmetry; apply H.
            * eauto.
        - rewrite H5, Permutation_app_swap; f_equiv.
          rewrite !XMapfold_eq.
          setoid_rewrite (fold_pair (XMap.Bst H3)); simpl.
          rewrite fold_spec_right.
          pose fold_spec_right as e; unfold XMap.fold in e; rewrite (e _ (XMap.Bst H3));
          clear e.
          assert (forall k trie,
                     InA (@XMap.eq_key_elt _)
                         (k, trie)
                         (rev
                            (XMap.elements (elt:=Trie)
                                           {| XMap.this := m; XMap.is_bst := H3 |}))
                     -> Permutation ((fst (Trie_update' trie search_term update_term)))
                                    (fst
                                       (List.partition
                                          (fun item : TItem => bfind_matcher search_term item)
                                          (TrieBag_benumerate trie)))).
          { intros; eapply H; eauto using elements_mapsto_iff.
            pose elements_mapsto_iff as e; unfold XMap.MapsTo in e; rewrite (e _ (XMap.Bst H3));
            clear e.
            rewrite <- InA_rev; eauto with typeclass_instances.
            eapply H6.
            eapply (@elements_mapsto_iff _ (XMap.Bst H3)).
            eapply InA_rev; eauto with typeclass_instances.
          }
          generalize H7; clear.
          assert (NoDupA (@XMap.eq_key _)
                         (rev
                            (XMap.elements (elt:=Trie) {| XMap.this := m; XMap.is_bst := H3 |})))
          by (apply NoDupA_rev; eauto with typeclass_instances;
              eapply XMap.elements_3w).
          revert H.
          induction (rev
                       (XMap.elements (elt:=Trie) {| XMap.this := m; XMap.is_bst := H3 |}));
            simpl; intros; eauto.
          unfold uncurry.
          rewrite !map_app, !flatten_app, !partition_app; simpl.
          unfold TrieBag_benumerate in H7.
          rewrite H7 with (k := fst a); f_equiv; eauto.
          rewrite <- IHl; eauto.
          inversion H; eauto.
          econstructor; destruct a; simpl; reflexivity.
      }
      Grab Existential Variables.
      eauto.
    Qed.

  End TrieBagDefinitions.

  Global Instance TrieAsBag
         {BagType TItem SearchTermType UpdateTermType : Type}
         (TBag : Bag BagType TItem SearchTermType UpdateTermType)
         projection
  : Bag Trie TItem ((option (list TKey)) * (SearchTermType)) UpdateTermType :=
    {

      bempty            := TrieBag_bempty TBag;

      bfind_matcher     := TrieBag_bfind_matcher TBag projection;
      bupdate_transform := bupdate_transform;

      benumerate := TrieBag_benumerate TBag;
      bfind      := TrieBag_bfind TBag;
      binsert    := TrieBag_binsert TBag projection;
      bcount     := TrieBag_bcount TBag;
      bdelete    := TrieBag_bdelete TBag;
      bupdate    := TrieBag_bupdate TBag }.

  Global Instance TrieBagAsCorrectBag
         {BagType TItem SearchTermType UpdateTermType : Type}
         (TBag : Bag BagType TItem SearchTermType UpdateTermType)
         (RepInv : BagType -> Prop)
         (ValidUpdate : UpdateTermType -> Prop)
         (CorrectTBag : CorrectBag RepInv ValidUpdate TBag)
         projection
  : CorrectBag (TrieBagRepInv TBag RepInv projection)
               (TrieBag_ValidUpdate _ ValidUpdate projection)
               (TrieAsBag TBag projection ) :=
    {
      bempty_RepInv     := Trie_Empty_RepInv CorrectTBag projection;
      binsert_RepInv    := @TrieBag_binsert_Preserves_RepInv _ _ _ _ TBag _ _ _ projection;
      bdelete_RepInv    := @TrieBag_bdelete_Preserves_RepInv _ _ _ _ TBag _ _ _ projection;
      bupdate_RepInv    := @TrieBag_bupdate_Preserves_RepInv _ _ _ _ TBag _ _ CorrectTBag projection;

      binsert_enumerate := @TrieBag_BagInsertEnumerate _ _ _ _ _ _ _ CorrectTBag projection;
      benumerate_empty  := @TrieBag_BagEnumerateEmpty _ _ _ _ _ _ _ CorrectTBag;
      bfind_correct     := @TrieBag_BagFindCorrect _ _ _ _ _ _ _ CorrectTBag projection;
      bcount_correct    := @TrieBag_BagCountCorrect _ _ _ _ _ _ _ CorrectTBag projection;
      bdelete_correct   := @TrieBag_BagDeleteCorrect _ _ _ _ _ _ _ CorrectTBag projection ;
      bupdate_correct   := @TrieBag_BagUpdateCorrect _ _ _ _ _ _ _ CorrectTBag projection
    }.

End TrieBag.
