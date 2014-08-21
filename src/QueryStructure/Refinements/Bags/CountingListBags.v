Require Export BagsInterface.
Unset Implicit Arguments.

Open Scope list.

Section CountingListBags.

  Context {TItem : Type}.

  Record CountingList :=
    {
      clength   : nat;
      ccontents : list TItem;
      cconsistent: List.length ccontents = clength
    }.

  Lemma empty_length :
    List.length (@nil TItem) = 0.
  Proof.
    reflexivity.
  Qed.

  Definition CountingList_empty : CountingList :=
    {|
      clength := 0;
      ccontents := @nil TItem;
      cconsistent := empty_length
    |}.

  Fixpoint MatchAgainstMany
           (search_terms : list (TItem -> bool)) 
           (item: TItem) :=
    match search_terms with
      | nil                      => true
      | cons is_match more_terms => andb (is_match item) (MatchAgainstMany more_terms item)
    end.

  Definition CountingListAsBag_bfind
             (container: CountingList) 
             (search_terms: list (TItem -> bool)) :=
    match search_terms with
      | nil                      => ccontents container
      | cons is_match more_terms => List.filter (MatchAgainstMany search_terms) (ccontents container)
    end.

  Lemma CountingList_insert :
    forall (container : CountingList) (item : TItem),
      length (item :: ccontents container) = S (clength container).
  Proof.
    intros; rewrite <- (cconsistent container); reflexivity.
  Qed.

  Definition CountingListAsBag_binsert
             (container: CountingList)
             (item: TItem) : CountingList :=
    {| clength := S (clength container);
       ccontents := cons item (ccontents container);
       cconsistent := CountingList_insert container item |}.

  Definition CountingListAsBag_bcount
             (container: CountingList) 
             (search_terms: list (TItem -> bool)) :=
    match search_terms with
      | nil => clength container
      | _   => List.fold_left (fun acc x => acc + if (MatchAgainstMany search_terms x) then 1 else 0)
                              (ccontents container) 0
    end.

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
             (search_terms : list (TItem -> bool)) :=
    let (d, r) := (CountingListPartition (ccontents container) (MatchAgainstMany search_terms))
    in (ccontents d, r).

  Lemma CountingListMap_consistent
        (container: CountingList)
        (update_f : TItem -> TItem)
  : length (List.map update_f (ccontents container)) = clength container.
  Proof.
    rewrite List.map_length; auto using cconsistent.
  Qed.

  Definition CountingListMap
             (container: CountingList)
             (update_f : TItem -> TItem)
  : CountingList :=
    {| clength := clength container;
       ccontents := List.map update_f (ccontents container);
       cconsistent := CountingListMap_consistent container update_f|}.

  Lemma CountingListAsBag_Partition_App
        (container : CountingList)
        (search_term : TItem -> bool)
  : length
      (let (g, d) :=
           CountingListPartition (ccontents container) search_term in
       ccontents d ++ ccontents g) =
    let (g, d) :=
        CountingListPartition (ccontents container) search_term in
    (clength g) + (clength d).
  Proof.
    destruct container as [n l length_l]; simpl;
    destruct (CountingListPartition l search_term); simpl.
    rewrite List.app_length; repeat rewrite cconsistent; auto with arith.
  Qed.

  Lemma CountingListAsBag_bupdate_Consistent
        (container : CountingList)
        (search_term : TItem -> bool)
        (update_f : TItem -> TItem)
  : length
      (let (g, d) :=
           CountingListPartition (ccontents container) search_term in
       ccontents d ++ List.map update_f (ccontents g)) =
    clength container.
  Proof.
    destruct container as [n l length_l]; simpl; revert n length_l;
    induction l; simpl; intros; auto.
    destruct (CountingListPartition l search_term); simpl.
    erewrite <- length_l, <- (IHl (length l)); auto.
    destruct (search_term a); simpl;
    rewrite List.app_length; simpl; rewrite List.map_length;
    repeat rewrite cconsistent; auto.
    rewrite List.app_length; simpl; rewrite List.map_length;
    repeat rewrite cconsistent; auto.
  Qed.

  Program Definition CountingListAsBag_bupdate
          (container : CountingList)
          (search_terms : list (TItem -> bool))
          (update_f : TItem -> TItem) :
    CountingList :=
    {| clength := clength container;
       ccontents :=
         let (g, d) := (CountingListPartition (ccontents container)
                                              (MatchAgainstMany search_terms)) in
         (ccontents d) ++ (List.map update_f (ccontents g));
       cconsistent := CountingListAsBag_bupdate_Consistent
                        container
                        (MatchAgainstMany search_terms)
                        update_f
    |}.

  Lemma CountingList_BagInsertEnumerate :
      BagInsertEnumerate ccontents CountingListAsBag_binsert.
  Proof.
    firstorder.
  Qed.

  Lemma CountingList_BagEnumerateEmpty :
    BagEnumerateEmpty ccontents CountingList_empty.
  Proof.
    firstorder.
  Qed.

  Lemma CountingList_BagFindStar :
      BagFindStar CountingListAsBag_bfind ccontents nil.
  Proof.
    firstorder.
  Qed.

  Require Import AdditionalLemmas.

  Lemma CountingList_BagFindCorrect :
      BagFindCorrect CountingListAsBag_bfind MatchAgainstMany ccontents.
  Proof.
    destruct search_term; simpl; [ rewrite filter_all_true | ]; reflexivity.
  Qed.

  Require Import Omega.
  Lemma CountingList_BagCountCorrect_aux :
    forall (container: list TItem) (search_term: list (TItem -> bool)) default,
      length (List.filter (MatchAgainstMany search_term) container) + default =
      List.fold_left
        (fun (acc : nat) (x : TItem) =>
           acc + (if MatchAgainstMany search_term x then 1 else 0))
        container default.
  Proof.
    induction container; intros.

    + trivial.
    + simpl; destruct (MatchAgainstMany search_term a);
      simpl; rewrite <- IHcontainer; omega.
  Qed.

  Lemma CountingList_BagCountCorrect :
      BagCountCorrect CountingListAsBag_bcount CountingListAsBag_bfind.
  Proof.
    unfold BagCountCorrect, CountingListAsBag_bcount, CountingListAsBag_bfind; intros;
    pose proof (CountingList_BagCountCorrect_aux (ccontents container) search_term 0) as temp;
    rewrite plus_0_r in temp; simpl in temp;
    destruct search_term; simpl; [ apply cconsistent | apply temp ].
  Qed.

  Lemma CountingList_BagDeleteCorrect :
      BagDeleteCorrect CountingListAsBag_bfind MatchAgainstMany ccontents
                       CountingListAsBag_bdelete.
  Proof.
    unfold BagDeleteCorrect; destruct container as [n l length_l];
    revert n length_l; induction l; simpl; intros; split.
    + constructor.
    + constructor.
    + destruct (IHl _ (refl_equal _) search_term).
      unfold CountingListAsBag_bdelete in *; simpl in *.
      destruct (MatchAgainstMany search_term a);
        destruct (CountingListPartition l (MatchAgainstMany search_term));
        destruct (List.partition (MatchAgainstMany search_term) l); simpl; auto.
    +  destruct (IHl _ (refl_equal _) search_term).
      unfold CountingListAsBag_bdelete in *; simpl in *.
      destruct (MatchAgainstMany search_term a);
        destruct (CountingListPartition l (MatchAgainstMany search_term));
        destruct (List.partition (MatchAgainstMany search_term) l); simpl; auto.
  Qed.

  Lemma CountingList_BagUpdateCorrect :
      BagUpdateCorrect CountingListAsBag_bfind MatchAgainstMany ccontents
                       id CountingListAsBag_bupdate.
  Proof.
    unfold BagUpdateCorrect; destruct container as [n l length_l];
    revert n length_l; induction l; simpl; intros.
    constructor.
    pose proof (IHl _ (refl_equal _) search_term update_term).
    unfold CountingListAsBag_bdelete in *; simpl in *.
    destruct (MatchAgainstMany search_term a);
      destruct (CountingListPartition l (MatchAgainstMany search_term));
      destruct (List.partition (MatchAgainstMany search_term) l); simpl in *; auto.
    rewrite Permutation_app_comm; simpl.
    apply Permutation_cons_app; rewrite Permutation_app_comm; auto.
  Qed.

  Instance CountingListAsBag
  : Bag (CountingList) TItem (list (TItem -> bool)) (TItem -> TItem) :=
    {|
      bempty := CountingList_empty;
      bstar  := nil;
      bid    := id;

      benumerate := ccontents;
      bfind      := CountingListAsBag_bfind;
      binsert    := CountingListAsBag_binsert;
      bcount     := CountingListAsBag_bcount;
      bdelete    := CountingListAsBag_bdelete;
      bupdate    := CountingListAsBag_bupdate;

      binsert_enumerate := CountingList_BagInsertEnumerate;
      benumerate_empty  := CountingList_BagEnumerateEmpty;
      bfind_star        := CountingList_BagFindStar;
      bfind_correct     := CountingList_BagFindCorrect;
      bcount_correct    := CountingList_BagCountCorrect;
      bdelete_correct     := CountingList_BagDeleteCorrect;
      bupdate_correct     := CountingList_BagUpdateCorrect
    |}.

End CountingListBags.
