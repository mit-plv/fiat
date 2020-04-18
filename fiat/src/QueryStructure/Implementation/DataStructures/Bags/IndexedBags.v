Require Export Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsInterface
               Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsProperties.

Unset Implicit Arguments.

Section IBagSpecs.

  Context {TBag TIndex TItem TSearchTerm : Type}.

  Definition TMap := TIndex -> option TItem.

  Definition ib_RepInv_fact
             (RepInv : TMap -> TBag -> Prop)
             (ibenumerate : TBag -> list TIndex) :=
    forall bag imap imap',
      (forall idx, List.In idx (ibenumerate bag) -> imap idx = imap' idx) ->
      (RepInv imap bag -> RepInv imap' bag).

  Definition ibempty_Preserves_RepInv
             (RepInv  : TMap -> TBag -> Prop)
             (ibempty : TBag) :=
    forall imap, RepInv imap ibempty.

  Definition ibinsert_Preserves_RepInv
             (RepInv   : TMap -> TBag -> Prop)
             (ibinsert : TBag -> TIndex -> TBag) :=
    forall bag imap idx, RepInv imap bag -> RepInv imap (ibinsert bag idx).

  Definition ibdelete_Preserves_RepInv
             (RepInv   : TMap -> TBag -> Prop)
             (ibdelete : TBag -> TSearchTerm -> list TIndex * TBag) :=
    forall bag imap searchterm, RepInv imap bag -> RepInv imap (snd (ibdelete bag searchterm)).

  Definition IBagEnumerateEmpty
             (ibempty     : TBag)
             (ibenumerate : TBag -> list TIndex) :=
    forall idx, ~ List.In idx (ibenumerate ibempty).

  Definition IBagInsertEnumerate
             (RepInv      : TMap -> TBag -> Prop)
             (ibenumerate : TBag -> list TIndex)
             (ibinsert    : TBag -> TIndex -> TBag) :=
    forall bag imap idx,
      RepInv imap bag ->
      Permutation (ibenumerate (ibinsert bag idx)) (idx :: ibenumerate bag).

  Definition IBagCountCorrect
             (RepInv  : TMap -> TBag -> Prop)
             (ibfind  : TBag -> TSearchTerm -> list TIndex)
             (ibcount : TBag -> TSearchTerm -> nat) :=
    forall bag imap searchterm,
      RepInv imap bag ->
      List.length (ibfind bag searchterm) = ibcount bag searchterm.

  Definition IBagMatcher
             (Matcher    : TSearchTerm -> TItem -> bool)
             (imap       : TIndex -> option TItem)
             (searchterm : TSearchTerm)
             (idx        : TIndex) :=
    match imap idx with
    | None      => false
    | Some item => Matcher searchterm item
    end.

  Definition IBagFindCorrect
             (RepInv      : TMap -> TBag -> Prop)
             (Matcher     : TSearchTerm -> TItem -> bool)
             (ibenumerate : TBag -> list TIndex)
             (ibfind      : TBag -> TSearchTerm -> list TIndex) :=
    forall bag imap searchterm,
      RepInv imap bag ->
      Permutation (ibfind bag searchterm)
                  (List.filter (IBagMatcher Matcher imap searchterm) (ibenumerate bag)).

  Definition IBagDeleteCorrect
             (RepInv      : TMap -> TBag -> Prop)
             (Matcher     : TSearchTerm -> TItem -> bool)
             (ibenumerate : TBag -> list TIndex)
             (ibdelete    : TBag -> TSearchTerm -> list TIndex * TBag) :=
    forall bag imap searchterm,
      RepInv imap bag ->
      Permutation (ibenumerate (snd (ibdelete bag searchterm)))
                  (snd (List.partition (IBagMatcher Matcher imap searchterm)
                                       (ibenumerate bag))) /\
      Permutation (fst (ibdelete bag searchterm))
                  (fst (List.partition (IBagMatcher Matcher imap searchterm)
                                       (ibenumerate bag))).

End IBagSpecs.

Class IBag (TBag TIndex TSearchTerm : Type) :=
  { ibempty     : TBag;
    ibenumerate : TBag -> list TIndex;
    ibfind      : TBag -> TSearchTerm -> list TIndex;
    ibinsert    : TBag -> TIndex -> TBag;
    ibcount     : TBag -> TSearchTerm -> nat;
    ibdelete    : TBag -> TSearchTerm -> list TIndex * TBag }.

Class IBagCorrect (TBag TIndex TItem TSearchTerm : Type)
      (RepInv  : (TIndex -> option TItem) -> TBag -> Prop)
      (Matcher : TSearchTerm -> TItem -> bool)
      (IBagImplementation : IBag TBag TIndex TSearchTerm) :=
  { ib_RepInv          : ib_RepInv_fact RepInv ibenumerate;
    ibempty_RepInv     : ibempty_Preserves_RepInv RepInv ibempty;
    ibinsert_RepInv    : ibinsert_Preserves_RepInv RepInv ibinsert;
    ibdelete_RepInv    : ibdelete_Preserves_RepInv RepInv ibdelete;

    ibenumerate_empty  : IBagEnumerateEmpty ibempty ibenumerate;
    ibinsert_enumerate : IBagInsertEnumerate RepInv ibenumerate ibinsert;
    ibcount_correct    : IBagCountCorrect RepInv ibfind ibcount;
    ibfind_correct     : IBagFindCorrect RepInv Matcher ibenumerate ibfind;
    ibdelete_correct   : IBagDeleteCorrect RepInv Matcher ibenumerate ibdelete }.

Class IPool (TPool TIndex TItem : Type) :=
  { pempty : TPool;
    pget   : TPool -> TIndex -> option TItem;
    pput   : TPool -> TIndex -> option TItem -> TPool;
    pfresh : TPool -> TIndex }.

Class IPoolCorrect (TPool TIndex TItem : Type)
      (PoolImplementation : IPool TPool TIndex TItem) :=
  { pempty_correct : forall idx, pget pempty idx = None;
    pput_eq        : forall pool idx item, pget (pput pool idx item) idx = item;
    pput_neq       : forall pool idx idx' item, idx <> idx' ->
                                                pget (pput pool idx item) idx' = pget pool idx';
    pfresh_correct : forall pool, pget pool (pfresh pool) = None }.

Module NatIPool.

  Context {TItem : Type}.

  Require Import
          Coq.FSets.FMapInterface
          Coq.FSets.FMapFacts
          Coq.FSets.FMapAVL
          Coq.Structures.OrderedTypeEx.

  Module Import XMap := FMapAVL.Make Nat_as_OT.
  Module Import XMapFacts := WFacts_fun Nat_as_OT XMap.

  Definition TPool := { ds : (t TItem * nat) |
                        forall idx t, MapsTo idx t (fst ds) -> idx < snd ds }.

  Definition NatIPool_pempty : TPool.
    refine (exist _ (empty TItem, O) _).
    intros idx t. rewrite empty_mapsto_iff. tauto.
  Defined.

  Definition NatIPool_pget (pool : TPool) (idx : nat) :=
    find idx (fst (proj1_sig pool)).

  Definition NatIPool_pput : TPool -> nat -> option TItem -> TPool.
    intros [ [m n] pf].
    refine (fun idx t =>
              match t with
              | None   => exist _ (remove idx m, n) _
              | Some t'=> exist _ (add idx t' m, max n (S idx)) _
              end); simpl in *; intuition.
    - destruct (Peano_dec.eq_nat_dec idx idx0); subst.
      apply NPeano.Nat.max_lt_iff. right. auto with arith.
      apply NPeano.Nat.max_lt_iff. left. eapply pf. eapply add_3. eauto. eauto.
    - eapply pf; eapply remove_3; eauto.
  Defined.

  Definition NatIPool_pfresh (pool : TPool) :=
    snd (proj1_sig pool).

  Lemma NatIPool_pempty_correct :
    forall idx, NatIPool_pget NatIPool_pempty idx = None.
  Proof.
    apply empty_o.
  Qed.

  Lemma NatIPool_pput_eq :
    forall pool idx item, NatIPool_pget (NatIPool_pput pool idx item) idx = item.
  Proof.
    unfold NatIPool_pget, NatIPool_pput.
    intros [ [m n] pf] idx item; destruct item eqn: eq; simpl; subst.
    - eapply add_eq_o; eauto.
    - eapply remove_eq_o; eauto.
  Qed.

  Lemma NatIPool_pput_neq :
    forall pool idx idx' item,
      idx <> idx' ->
      NatIPool_pget (NatIPool_pput pool idx item) idx' = NatIPool_pget pool idx'.
  Proof.
    unfold NatIPool_pget, NatIPool_pput.
    intros [ [m n] pf] idx idx' item; destruct item eqn: eq; simpl; subst; intros.
    - eapply add_neq_o; eauto.
    - eapply remove_neq_o; eauto.
  Qed.

  Lemma NatIPool_pfresh_correct :
    forall pool, NatIPool_pget pool (NatIPool_pfresh pool) = None.
  Proof.
    unfold NatIPool_pget, NatIPool_pfresh; intros [ [m n] pf]; simpl.
    destruct (find (elt:=TItem) n m) eqn: eq; eauto.
    apply find_2 in eq. apply pf in eq. simpl in eq. omega.
  Qed.

  Global Instance NatIPoolAsIPool
    : IPool TPool nat TItem :=
    {| pempty := NatIPool_pempty;
       pget   := NatIPool_pget;
       pput   := NatIPool_pput;
       pfresh := NatIPool_pfresh |}.

  Global Instance NatIPoolAsCorrectIPool
    : IPoolCorrect TPool nat TItem NatIPoolAsIPool :=
    {| pempty_correct := NatIPool_pempty_correct;
       pput_eq        := NatIPool_pput_eq;
       pput_neq       := NatIPool_pput_neq;
       pfresh_correct := NatIPool_pfresh_correct |}.

End NatIPool.

Section IndexedBag.

  Context {TBag TPool TIndex TItem TSearchTerm TUpdateTerm : Type}
          (TIndex_dec : forall idx idx' : TIndex, {idx = idx'} + {idx <> idx'})

          (RepInv : (TIndex -> option TItem) -> TBag -> Prop)
          (Matcher : TSearchTerm -> TItem -> bool)
          (Transform : TUpdateTerm -> TItem -> TItem)

          (IBagImpl : IBag TBag TIndex TSearchTerm)
          (IBagProof : IBagCorrect TBag TIndex TItem TSearchTerm RepInv Matcher IBagImpl)

          (IPoolImpl : IPool TPool TIndex TItem)
          (IPoolProof : IPoolCorrect TPool TIndex TItem IPoolImpl).

  Definition TIndexedBag := prod TBag TPool.

  Definition IndexedBag_bempty := (ibempty, pempty).

  Definition IndexesToItems
             (idxs : list TIndex)
             (pool : TPool) :=
    List.fold_right (fun idx ls => match pget pool idx with
                                   | None      => ls
                                   | Some item => cons item ls
                                   end) nil idxs.

  Definition IndexedBag_benumerate
             (bag : TIndexedBag) :=
    IndexesToItems (ibenumerate (fst bag)) (snd bag).

  Definition IndexedBag_bfind
             (bag : TIndexedBag)
             (searchterm : TSearchTerm) :=
    IndexesToItems (ibfind (fst bag) searchterm) (snd bag).

  Definition IndexedBag_binsert
             (bag : TIndexedBag)
             (item : TItem) :=
    let fresh := pfresh (snd bag) in
    (ibinsert (fst bag) fresh, pput (snd bag) fresh (Some item)).

  Definition IndexedBag_bcount
             (bag : TIndexedBag)
             (searchterm : TSearchTerm) :=
    ibcount (fst bag) searchterm.

  Definition IndexedBag_bdelete
             (bag : TIndexedBag)
             (searchterm : TSearchTerm) :=
    let (deleted, ibag) := ibdelete (fst bag) searchterm in
    (IndexesToItems deleted (snd bag),
     (ibag, List.fold_right (fun idx p => pput p idx None) (snd bag) deleted)).

  Definition IndexedBag_bupdate
             (bag : TIndexedBag)
             (searchterm : TSearchTerm)
             (updateterm : TUpdateTerm) :=
    let matched := ibfind (fst bag) searchterm in
    (IndexesToItems matched (snd bag),
     (fst bag, List.fold_right
                 (fun idx p => match pget p idx with
                               | None      => p
                               | Some item => pput p idx (Some (Transform updateterm item))
                               end) (snd bag) matched)).

  Definition IndexedBag_RepInv
             (bag : TIndexedBag) :=
    RepInv (pget (snd bag)) (fst bag) /\
    forall idx, List.In idx (ibenumerate (fst bag)) <->
                pget (snd bag) idx <> None.

  Definition IndexedBag_ValidUpdate
             (updateterm : TUpdateTerm) :=
    forall ibag imap idx,
      RepInv imap ibag ->
      RepInv (fun i => if TIndex_dec i idx
                       then match imap i with
                            | Some item => Some (Transform updateterm item)
                            | None      => None
                            end
                       else imap i) ibag.

  Lemma IndexedBag_Empty_RepInv :
    IndexedBag_RepInv IndexedBag_bempty.
  Proof.
    unfold IndexedBag_RepInv.
    split. apply ibempty_RepInv.
    intro idx. split.
    - intro asmp. exfalso. apply (ibenumerate_empty idx). assumption.
    - intro asmp. exfalso. apply asmp. apply pempty_correct.
  Qed.

  Lemma IndexedBag_binsert_Preserves_RepInv :
    binsert_Preserves_RepInv IndexedBag_RepInv IndexedBag_binsert.
  Proof.
    unfold binsert_Preserves_RepInv, IndexedBag_binsert, IndexedBag_RepInv.
    intros [ibag pool] item [repi repp]; simpl in *; split.
    - eapply ibinsert_RepInv; eapply ib_RepInv; [ | eauto ].
      intros idx asmp; rewrite pput_neq; eauto.
      intro contra; subst; apply repp in asmp; apply asmp; apply pfresh_correct.
    - intro idx; split; intro asmp.
      + eapply Permutation_in in asmp; try eapply ibinsert_enumerate; eauto.
        inversion asmp. subst. rewrite pput_eq. congruence.
        rewrite pput_neq. apply repp. assumption. intro contra.
        subst. apply repp in H. apply H. apply pfresh_correct.
      + eapply Permutation_in. symmetry. eapply ibinsert_enumerate. eauto.
        destruct (TIndex_dec (pfresh pool) idx); subst.
        * left; eauto.
        * right; apply repp; rewrite pput_neq in asmp; eauto.
  Qed.

  Lemma Permutation_in' :
    forall {A : Type} {l l' : list A} (x : A),
      Permutation l l' -> (List.In x l <-> List.In x l').
  Proof.
    split; intros; eapply Permutation_in; [ | | symmetry | ]; eauto.
  Qed.

  Lemma IndexedBag_bdelete_Preserves_RepInv :
    bdelete_Preserves_RepInv IndexedBag_RepInv IndexedBag_bdelete.
  Proof.
    unfold bdelete_Preserves_RepInv, IndexedBag_bdelete, IndexedBag_RepInv.
    simpl; intros [ibag pool] st [repi repp]; simpl.
    assert (forall idx, List.In idx (ibenumerate (snd (ibdelete ibag st))) ->
                        ~ List.In idx (fst (ibdelete ibag st))).
    { intros idx asmp asmp'.
      pose proof (ibdelete_correct _ _ st repi) as [Hsnd Hfst].
      pose proof (Permutation_in _ Hsnd asmp) as asmp_ls.
      pose proof (Permutation_in _ Hfst asmp') as asmp'_ls.
      apply ListFacts.In_partition_unmatched in asmp_ls.
      apply ListFacts.In_partition_matched in asmp'_ls.
      congruence. }
    rewrite surjective_pairing with (p:=ibdelete ibag st); split; simpl in *.
    - pose proof (ibdelete_RepInv _ _ st repi) as repi'; eapply ib_RepInv; [ | eauto ].
      intros idx asmp; apply H in asmp.
      generalize asmp; apply Common.fold_right_rect; eauto; intros; subst.
      destruct (TIndex_dec b idx); eauto; subst. exfalso. apply asmp0. econstructor. eauto.
      rewrite pput_neq; eauto. apply H0. intro. apply asmp0. econstructor 2. eauto.
    - intro idx; split; intro asmp.
      + pose proof (H _ asmp) as asmp'; generalize asmp'.
        eapply Common.fold_right_rect; eauto; intros; subst. apply repp.
        eapply (fun A f x l H => proj1 (proj1 (@List.filter_In A x f l) H)).
        pose proof (ibdelete_correct _ _ st repi) as [Hdel _].
        rewrite ListFacts.partition_filter_neq in Hdel; eapply Permutation_in; eauto.
        destruct (TIndex_dec b idx); subst; [ rewrite pput_eq | rewrite pput_neq ]; eauto.
        exfalso; apply asmp'0; econstructor; eauto.
        apply H0; intro; apply asmp'0; econstructor 2; eauto.
      + specialize (H idx); pose proof (ibdelete_correct _ _ st repi) as [Hsnd Hfst].
        rewrite ListFacts.partition_filter_neq in Hsnd; rewrite (Permutation_in' idx Hsnd) in *.
        rewrite ListFacts.partition_filter_eq in Hfst; symmetry in Hfst.
        apply PermutationFacts.permutation_filter in Hfst.
        destruct Hfst as [ls [Hfst1 Hfst2] ]. rewrite <- Hfst1 in *.
        apply List.filter_In; rewrite (Permutation_in' idx Hfst2).
        specialize (fun H => proj1 (Permutation_in' idx Hfst2) (proj2 (repp idx) H)); clear repp; intro repp.

        clear H Hfst1 Hfst2 Hsnd.
         induction ls; eauto; simpl in *.
        * exfalso; eauto.
        * destruct (IBagMatcher Matcher (pget pool) st a) eqn: eq; simpl in *.
          { destruct (TIndex_dec a idx); subst; eauto.
            rewrite pput_eq in asmp; congruence. rewrite pput_neq in asmp; eauto.
            specialize (IHls asmp); clear asmp.
            split; [ right | ]; apply IHls; intro; destruct (repp H); try congruence; eauto. }
          { destruct (TIndex_dec a idx); subst; eauto.
            split. tauto. rewrite eq. auto.
            split; [ right | ]; apply IHls; eauto.
            intro. destruct (repp H). congruence. auto. intro.
            destruct (repp H). congruence. auto. }
  Qed.

  Lemma  IndexedBag_bupdate_Preserves_RepInv :
    bupdate_Preserves_RepInv IndexedBag_RepInv IndexedBag_ValidUpdate IndexedBag_bupdate.
  Proof.
    unfold bupdate_Preserves_RepInv, IndexedBag_bupdate, IndexedBag_RepInv, IndexedBag_ValidUpdate.
    simpl; intros [ibag pool] st ut [repi repp]; split; simpl.
    - clear repp; remember (ibfind ibag st) as ls; clear Heqls.
      eapply Common.fold_right_rect; eauto.
      clear repi ls; intros _ idx ls _ asmp.
      remember (List.fold_right (fun (idx : TIndex) (p : TPool) =>
                                   match pget p idx with
                                   | Some item => pput p idx (Some (Transform ut item))
                                   | None => p
                                   end) pool ls) as pool'; clear Heqpool'.
      destruct (pget pool' idx) eqn: eq; eauto.
      specialize (valid_update _ _ idx asmp); clear asmp ls.
      assert ((pget (pput pool' idx (Some (Transform ut t)))) =
              (fun i : TIndex =>
                 if TIndex_dec i idx
                 then
                   match pget pool' i with
                   | Some item => Some (Transform ut item)
                   | None => None
                   end
                 else pget pool' i)) as H; try rewrite H; eauto.
      extensionality idx'; destruct (TIndex_dec idx' idx); subst.
      + rewrite pput_eq; rewrite eq; eauto.
      + rewrite pput_neq; eauto.
    - clear valid_update; intro idx; split; intro asmp.
      + eapply Common.fold_right_rect; simpl; intros; try apply repp; eauto; subst.
        destruct (pget (List.fold_right
                          (fun (idx : TIndex) (p : TPool) =>
                             match pget p idx with
                             | Some item => pput p idx (Some (Transform ut item))
                             | None => p
                             end) pool t) b); eauto.
        destruct (TIndex_dec b idx); subst;
        [ rewrite pput_eq; congruence | rewrite pput_neq ]; eauto.
      + remember (ibfind ibag st) as ls; clear Heqls.
        induction ls; simpl in *. apply repp; eauto.
        destruct (pget (List.fold_right
                          (fun (idx : TIndex) (p : TPool) =>
                             match pget p idx with
                             | Some item => pput p idx (Some (Transform ut item))
                             | None => p
                             end) pool ls) a) eqn: eq.
        * destruct (TIndex_dec a idx); subst. rewrite pput_eq in asmp.
          apply IHls; intro; congruence. rewrite pput_neq in asmp; eauto.
        * apply IHls; intro; congruence.
  Qed.

  Lemma IndexedBag_BagEnumerateEmpty :
    BagEnumerateEmpty IndexedBag_benumerate IndexedBag_bempty.
  Proof.
    unfold IndexedBag_benumerate, IndexedBag_bempty, IndexesToItems.
    hnf; simpl; intros item.
    destruct (ibenumerate ibempty) eqn: eq; eauto.
    exfalso; apply (ibenumerate_empty t); rewrite eq; simpl; eauto.
  Qed.

  Lemma InList_ind_helper :
    forall {A : Type} {P : A -> Prop} {x : A} {xs : list A},
      (forall k, List.In k (x :: xs) -> P k) -> (P x /\ (forall k, List.In k xs -> P k)).
  Proof.
    intros; split; intros; eapply H; simpl; eauto.
  Qed.

  Lemma IndexesToItems_perm :
    forall pool idxs idxs',
      Permutation idxs idxs' ->
      Permutation (IndexesToItems idxs pool) (IndexesToItems idxs' pool).
  Proof.
    unfold IndexesToItems; induction 1; eauto; simpl in *.
    - destruct (pget pool x); eauto.
    - destruct (pget pool x); destruct (pget pool y); eauto; apply perm_swap.
    - eapply perm_trans; eauto.
  Qed.

  Lemma IndexedBag_BagInsertEnumerate :
    BagInsertEnumerate IndexedBag_RepInv IndexedBag_benumerate IndexedBag_binsert.
  Proof.
    unfold IndexedBag_benumerate, IndexedBag_RepInv, IndexedBag_binsert.
    hnf; simpl; intros ins bag [repi repp].
    eapply perm_trans; [ eapply IndexesToItems_perm; try eapply ibinsert_enumerate | ]; eauto.
    simpl; rewrite pput_eq; constructor.
    remember (ibenumerate (fst bag)) as ls; clear Heqls.
    pose proof (fun idx => proj1 (repp idx)) as repp_f; clear repp.
    induction ls; simpl; eauto.
    destruct (InList_ind_helper repp_f) as [repp_f_h repp_f_t]; clear repp_f.
    rewrite pput_neq; eauto.
    destruct (pget (snd bag) a); eauto.
    intro contra; subst; apply repp_f_h; apply pfresh_correct.
  Qed.

  Lemma IndexedBag_BagFindCorrect :
    BagFindCorrect IndexedBag_RepInv IndexedBag_bfind Matcher IndexedBag_benumerate.
  Proof.
    unfold BagFindCorrect, IndexedBag_RepInv, IndexedBag_bfind, IndexedBag_benumerate.
    intros [ibag pool] st [repi _]; simpl in *.
    eapply perm_trans; [ | eapply IndexesToItems_perm; symmetry; eapply ibfind_correct ]; eauto.
    induction (ibenumerate ibag); eauto; simpl.
    unfold IBagMatcher in *; destruct (pget pool a) eqn: eq; simpl in *.
    - destruct (Matcher st t); eauto. simpl. rewrite eq. eapply perm_skip; eauto.
    - eauto.
  Qed.

  Lemma IndexedBag_BagCountCorrect :
    BagCountCorrect IndexedBag_RepInv IndexedBag_bcount IndexedBag_bfind.
  Proof.
    unfold BagCountCorrect, IndexedBag_RepInv, IndexedBag_bcount, IndexedBag_bfind.
    intros [ibag pool] st [repi repp]; simpl in *.
    rewrite <- ibcount_correct; eauto.
    specialize (fun i => proj1 (repp i)); clear repp; intro repp.
    assert (forall i, List.In i (ibfind ibag st) -> pget pool i <> None).
    intros i asmp. apply repp. eapply List.filter_In. eapply Permutation_in.
    eapply ibfind_correct; eauto. eauto.
    induction (ibfind ibag st); eauto.
    destruct (InList_ind_helper H) as [H_h H_t]; clear H.
    simpl; destruct (pget pool a); try congruence. simpl. f_equal.
    apply IHl. eauto.
  Qed.

  Lemma IndexedBag_BagDeleteCorrect :
    BagDeleteCorrect IndexedBag_RepInv IndexedBag_bfind Matcher IndexedBag_benumerate IndexedBag_bdelete.
  Proof.
    unfold BagDeleteCorrect, IndexedBag_benumerate, IndexedBag_bdelete.
    intros [ibag pool] st rep.
    pose proof (IndexedBag_bdelete_Preserves_RepInv _ st rep) as rep_del.
    destruct rep as [repi repp]; destruct rep_del as [_ repp_del].
    rewrite surjective_pairing with (p:=ibdelete ibag st); split; simpl in *.
    - admit.
    - admit.
  Qed.

  Lemma IndexedBag_BagUpdateCorrect :
    BagUpdateCorrect IndexedBag_RepInv IndexedBag_ValidUpdate IndexedBag_bfind Matcher IndexedBag_benumerate Transform IndexedBag_bupdate.
  Proof.
    unfold BagUpdateCorrect, IndexedBag_benumerate, IndexedBag_bupdate.
    simpl; intros [ibag pool] st ut [repi repp]; split; simpl.
    - admit.
    - admit.
  Qed.

  Global Instance IndexedBagAsBag
    : Bag TIndexedBag TItem TSearchTerm TUpdateTerm :=
    {| bempty            := IndexedBag_bempty;
       bfind_matcher     := Matcher;
       bupdate_transform := Transform;

       benumerate := IndexedBag_benumerate;
       bfind      := IndexedBag_bfind;
       binsert    := IndexedBag_binsert;
       bcount     := IndexedBag_bcount;
       bdelete    := IndexedBag_bdelete;
       bupdate    := IndexedBag_bupdate |}.

  Global Instance IndexedBagAsCorrectBag
    : CorrectBag IndexedBag_RepInv IndexedBag_ValidUpdate IndexedBagAsBag :=
    {| bempty_RepInv     := IndexedBag_Empty_RepInv;
       binsert_RepInv    := IndexedBag_binsert_Preserves_RepInv;
       bdelete_RepInv    := IndexedBag_bdelete_Preserves_RepInv;
       bupdate_RepInv    := IndexedBag_bupdate_Preserves_RepInv;

       binsert_enumerate := IndexedBag_BagInsertEnumerate;
       benumerate_empty  := IndexedBag_BagEnumerateEmpty;
       bfind_correct     := IndexedBag_BagFindCorrect;
       bcount_correct    := IndexedBag_BagCountCorrect;
       bdelete_correct   := IndexedBag_BagDeleteCorrect;
       bupdate_correct   := IndexedBag_BagUpdateCorrect |}.

End IndexedBag.
