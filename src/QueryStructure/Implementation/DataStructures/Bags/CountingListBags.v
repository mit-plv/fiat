Require Export Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsInterface.
Unset Implicit Arguments.

Require Import Coq.Arith.Arith
        Fiat.Common.List.ListFacts.

Open Scope list_scope.

Section CountingListBags.

  Context {TItem : Type}
          {TUpdateTerm : Type}
          (bupdate_transform : TUpdateTerm -> TItem -> TItem).

  Record CountingList :=
    {
      clength   : nat;
      ccontents : list TItem
    }.

  Lemma empty_length :
    List.length (@nil TItem) = 0.
  Proof.
    reflexivity.
  Qed.

  Definition CountingList_empty : CountingList :=
    {|
      clength := 0;
      ccontents := @nil TItem
    |}.

  Definition CountingListAsBag_bfind
             (container: CountingList)
             (search_terms: TItem -> bool) :=
    List.filter search_terms (ccontents container).

  Definition CountingListAsBag_binsert
             (container: CountingList)
             (item: TItem) : CountingList :=
    {| clength := S (clength container);
       ccontents := cons item (ccontents container) |}.

  Definition CountingListAsBag_bcount
             (container: CountingList)
             (search_terms: TItem -> bool) :=
    List.fold_left (fun acc x => acc + if search_terms x then 1 else 0)
                              (ccontents container) 0.

  Fixpoint CountingListPartition
           (contents : list TItem)
           (search_term : TItem -> bool)
  : prod CountingList CountingList :=
    match contents with
      | nil => (CountingList_empty, CountingList_empty)
      | x :: tl => let (g,d) := CountingListPartition tl search_term in
                   if search_term x then
                     (CountingListAsBag_binsert g x, d)
                   else
                     (g, CountingListAsBag_binsert d x)
    end.

  Definition CountingListAsBag_bdelete
             (container : CountingList)
             (search_terms : TItem -> bool) :=
    let (d, r) := (CountingListPartition (ccontents container) (search_terms))
    in (ccontents d, r).

  Definition CountingListMap
             (container: CountingList)
             (update_f : TItem -> TItem)
  : CountingList :=
    {| clength := clength container;
       ccontents := List.map update_f (ccontents container) |}.

  Definition CountingListAsBag_bupdate
          (container : CountingList)
          (search_terms : TItem -> bool)
          (update_term : TUpdateTerm)
  : list TItem * CountingList :=
    let (d, r) := (CountingListPartition (ccontents container) search_terms)
    in (ccontents d,
        {| clength := clength container;
           ccontents :=
             (ccontents r) ++ (List.map (bupdate_transform update_term) (ccontents d)) |}
       ).

  Instance CountingListAsBag
  : Bag CountingList TItem (TItem -> bool) _ :=
    {

      bempty := CountingList_empty;
      bfind_matcher f := f;
      bupdate_transform := bupdate_transform;

      benumerate := ccontents;
      bfind      := CountingListAsBag_bfind;
      binsert    := CountingListAsBag_binsert;
      bcount     := CountingListAsBag_bcount;
      bdelete    := CountingListAsBag_bdelete;
      bupdate    := CountingListAsBag_bupdate
    }.

  Definition CountingList_RepInv (container : CountingList) :=
    List.length (ccontents container) = clength container.
  Definition CountingList_ValidUpdate (_ : TUpdateTerm) := True.

  Lemma CountingList_binsert_Preserves_RepInv :
    binsert_Preserves_RepInv CountingList_RepInv CountingListAsBag_binsert.
  Proof.
    unfold binsert_Preserves_RepInv, CountingList_RepInv;
    intros; simpl; rewrite containerCorrect; reflexivity.
  Qed.

  Lemma CountingListMap_consistent
        (container: CountingList)
        (cconsistent : CountingList_RepInv container)
        (update_f : TItem -> TItem)
  : length (List.map update_f (ccontents container)) = clength container.
  Proof.
    rewrite List.map_length; auto using cconsistent.
  Qed.

  Lemma CountingListAsBag_Partition_App
        (container : CountingList)
        (search_term : TItem -> bool)
        (cconsistent : CountingList_RepInv container)
  : length
      (let (g, d) :=
           CountingListPartition (ccontents container) search_term in
       ccontents d ++ ccontents g) =
    let (g, d) :=
        CountingListPartition (ccontents container) search_term in
    (clength g) + (clength d).
  Proof.
    unfold CountingList_RepInv in *.
    destruct container as [n l]; simpl; revert n cconsistent;
    induction l; simpl; intros; eauto.
    destruct (search_term a); simpl;
    destruct (CountingListPartition l search_term); simpl.
    erewrite <- IHl, !List.app_length; simpl; auto with arith.
    erewrite IHl; auto with arith.
    simpl; eauto.
  Qed.

  Lemma CountingList_bdelete_Preserves_RepInv :
    bdelete_Preserves_RepInv CountingList_RepInv CountingListAsBag_bdelete.
  Proof.
    unfold bdelete_Preserves_RepInv, CountingList_RepInv, CountingListAsBag_bdelete;
    destruct container as [n l]; revert n; induction l; intros; simpl in *; eauto.
    destruct (search_term a); simpl.
    destruct n; simpl in *; [ discriminate | injection containerCorrect]; intros.
    pose proof (IHl n search_term H).
    destruct (CountingListPartition l search_term); simpl in *; eauto.
    destruct n; simpl in *; [ discriminate | injection containerCorrect]; intros.
    pose proof (IHl n search_term H).
    destruct (CountingListPartition l search_term); simpl in *; eauto.
  Qed.

  Lemma CountingList_bupdate_Preserves_RepInv
  : bupdate_Preserves_RepInv CountingList_RepInv CountingList_ValidUpdate CountingListAsBag_bupdate.
  Proof.
    unfold bupdate_Preserves_RepInv, CountingList_RepInv, CountingListAsBag_bupdate.
    destruct container as [n l]; simpl; revert n; induction l; intros; simpl in *; eauto.
    destruct (search_term a); simpl.
    destruct n; simpl in *; [ discriminate | injection containerCorrect]; intros.
    pose proof (IHl n search_term update_term).
    destruct (CountingListPartition l search_term); simpl in *; eauto.
    apply H0 in H.
    assert (forall {A: Type} a (b: A) c, (length (a ++ b :: c) = S (length (a ++ c)))).
    induction a0; intros; auto; simpl; rewrite IHa0; reflexivity.
    rewrite H1; rewrite H; reflexivity.
    apply valid_update.
    destruct n; simpl in *; [ discriminate | injection containerCorrect]; intros.
    pose proof (IHl n search_term update_term).
    destruct (CountingListPartition l search_term); simpl in *; eauto.
  Qed.

  Lemma CountingList_BagInsertEnumerate :
      BagInsertEnumerate CountingList_RepInv ccontents CountingListAsBag_binsert.
  Proof.
    firstorder.
  Qed.

  Lemma CountingList_BagEnumerateEmpty :
    BagEnumerateEmpty ccontents CountingList_empty.
  Proof.
    firstorder.
  Qed.

  Lemma CountingList_Empty_RepInv :
    CountingList_RepInv CountingList_empty.
  Proof.
    firstorder.
  Qed.

  Lemma CountingList_BagFindCorrect :
    BagFindCorrect CountingList_RepInv CountingListAsBag_bfind apply ccontents.
  Proof.
    intros; unfold BagFindCorrect, CountingListAsBag_bfind; reflexivity.
  Qed.

  Lemma CountingList_BagCountCorrect_aux :
    forall (container: list TItem) (search_term: TItem -> bool) default,
      length (List.filter search_term container) + default =
      List.fold_left
        (fun (acc : nat) (x : TItem) =>
           acc + (if search_term x then 1 else 0))
        container default.
  Proof.
    induction container; intros.

    + trivial.
    + simpl; destruct (search_term a);
      simpl; rewrite <- IHcontainer; simpl; eauto.
      rewrite (plus_comm 1); eauto using plus_assoc.
  Qed.

  Lemma CountingList_BagCountCorrect :
    BagCountCorrect CountingList_RepInv CountingListAsBag_bcount CountingListAsBag_bfind.
  Proof.
    unfold BagCountCorrect, CountingListAsBag_bcount, CountingListAsBag_bfind,
    CountingList_RepInv; intros;
    pose proof (CountingList_BagCountCorrect_aux (ccontents container) search_term 0) as temp;
    rewrite plus_0_r in temp; simpl in temp.
    simpl; [ apply temp ].
  Qed.

  Lemma CountingList_BagDeleteCorrect :
      BagDeleteCorrect CountingList_RepInv CountingListAsBag_bfind apply ccontents
                       CountingListAsBag_bdelete.
  Proof.
    unfold BagDeleteCorrect, CountingList_RepInv; destruct container as [n l];
    revert n; induction l; simpl; intros; split.
    + constructor.
    + constructor.
    + simpl in *; destruct (IHl _ search_term (refl_equal _)).
      unfold CountingListAsBag_bdelete in *; simpl in *.
      unfold apply in *.
      destruct (search_term a);
        destruct (CountingListPartition l (search_term));
        destruct (List.partition (search_term) l); simpl; auto.
    +  simpl in *; destruct (IHl _ search_term (refl_equal _)).
      unfold CountingListAsBag_bdelete in *; unfold apply in *; simpl in *.
      destruct (search_term a);
        destruct (CountingListPartition l (search_term));
        destruct (List.partition (search_term) l); simpl; auto.
  Qed.

  Lemma CountingList_BagUpdateCorrect :
    BagUpdateCorrect CountingList_RepInv CountingList_ValidUpdate
                     CountingListAsBag_bfind apply ccontents
                     bupdate_transform CountingListAsBag_bupdate.
  Proof.
    unfold BagUpdateCorrect, CountingList_RepInv. destruct container as [n l].
    revert n; induction l; simpl; intros; split.
    - constructor.
    - constructor.
    - unfold CountingListAsBag_bupdate in *; simpl in *.
      destruct (IHl _ search_term update_term (refl_equal _) ).
      apply valid_update.
      unfold apply in *.
      destruct (search_term a);
        destruct (CountingListPartition l (search_term));
        destruct (List.partition (search_term) l); simpl; auto.
      rewrite Permutation_app_comm; simpl.
      apply Permutation_cons_app; rewrite Permutation_app_comm; auto.
    - simpl in *; destruct (IHl _ search_term update_term (refl_equal _)).
      apply valid_update.
      unfold CountingListAsBag_bupdate in *; simpl in *.
      unfold apply in *;
      destruct (search_term a);
        destruct (CountingListPartition l (search_term));
        destruct (List.partition (search_term) l); simpl; auto.
  Qed.

  Instance CountingListAsCorrectBag
  : CorrectBag CountingList_RepInv CountingList_ValidUpdate CountingListAsBag :=
    {
       bempty_RepInv     := CountingList_Empty_RepInv;
       binsert_RepInv    := CountingList_binsert_Preserves_RepInv;
       bdelete_RepInv    := CountingList_bdelete_Preserves_RepInv;
       bupdate_RepInv    := CountingList_bupdate_Preserves_RepInv;

       binsert_enumerate := CountingList_BagInsertEnumerate;
       benumerate_empty  := CountingList_BagEnumerateEmpty;
       bfind_correct     := CountingList_BagFindCorrect;
       bcount_correct    := CountingList_BagCountCorrect;
       bdelete_correct   := CountingList_BagDeleteCorrect;
       bupdate_correct   := CountingList_BagUpdateCorrect
    }.

End CountingListBags.
