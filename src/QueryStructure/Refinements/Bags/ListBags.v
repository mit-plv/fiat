Require Export BagsInterface.
Unset Implicit Arguments.

Open Scope list.

Section ListBags.

  Context {TItem : Type}
          {TSearchTerm : Type}
          {TUpdateTerm : Type}
          (star: TSearchTerm)
          (bid : TUpdateTerm)
          (bfind_matcher: TSearchTerm -> TItem -> bool)
          (bupdate_transform : TUpdateTerm -> TItem -> TItem)
          (find_star: forall (i: TItem), bfind_matcher star i = true).

  Definition ListAsBag_bfind
             (container: list TItem)
             (search_term: TSearchTerm) :=
    List.filter (bfind_matcher search_term) container.

  Definition ListAsBag_binsert
             (container: list TItem)
             (item: TItem) :=
    cons item container.

  Definition ListAsBag_bcount
             (container: list TItem)
             (search_term: TSearchTerm) :=
    List.fold_left (fun acc x => acc + if (bfind_matcher search_term x) then 1 else 0) container 0.

  Definition ListAsBag_bdelete
             (container : list TItem)
             (search_term : TSearchTerm) :=
    List.partition (bfind_matcher search_term) container.

  Definition ListAsBag_bupdate
             (container   : list TItem)
             (search_term : TSearchTerm)
             (update_term : TUpdateTerm) :=
    (snd (List.partition (bfind_matcher search_term) container))
      ++ List.map (bupdate_transform update_term)
      (fst (List.partition (bfind_matcher search_term)
                           container)).

  Lemma List_BagInsertEnumerate :
    BagInsertEnumerate (fun _ => True) id (ListAsBag_binsert).
  Proof.
    firstorder.
  Qed.

  Lemma List_BagEnumerateEmpty :
    BagEnumerateEmpty id (@nil TItem).
  Proof.
    firstorder.
  Qed.

  Lemma List_BagFindStar :
    BagFindStar (fun _ => True) ListAsBag_bfind id star.
  Proof.
    intros;
    induction container; simpl;
    [ | rewrite find_star, IHcontainer]; trivial.
  Qed.

  Lemma List_BagFindCorrect :
    BagFindCorrect (fun _ => True) ListAsBag_bfind bfind_matcher id.
  Proof.
    firstorder.
  Qed.

  Require Import Omega.
  Lemma List_BagCountCorrect_aux :
    forall (container: list TItem) (search_term: TSearchTerm) default,
      length (List.filter (bfind_matcher search_term) container) + default =
      List.fold_left
        (fun (acc : nat) (x : TItem) =>
           acc + (if bfind_matcher search_term x then 1 else 0))
        container default.
  Proof.
    induction container; intros.

    + trivial.
    + simpl; destruct (bfind_matcher search_term a);
      simpl; rewrite <- IHcontainer; omega.
  Qed.

  Lemma List_BagCountCorrect :
    BagCountCorrect (fun _ => True) ListAsBag_bcount ListAsBag_bfind.
  Proof.
    unfold BagCountCorrect, ListAsBag_bcount, ListAsBag_bfind; intros;
    pose proof (List_BagCountCorrect_aux container search_term 0) as temp;
    rewrite plus_0_r in temp; simpl in temp; exact temp.
  Qed.

  Lemma List_BagDeleteCorrect :
    BagDeleteCorrect (fun _ => True) ListAsBag_bfind bfind_matcher id ListAsBag_bdelete.
  Proof.
    firstorder.
  Qed.

  Lemma List_BagUpdateCorrect :
    BagUpdateCorrect (fun _ => True) ListAsBag_bfind bfind_matcher id bupdate_transform ListAsBag_bupdate.
  Proof.
    firstorder.
  Qed.

  Global Instance ListAsBag
  : Bag TItem  :=
    {|
      BagType        := (list TItem);
      SearchTermType := TSearchTerm;
      UpdateTermType := TUpdateTerm;

      bempty            := nil;
      bid               := bid;
      bstar             := star;
      bfind_matcher     := bfind_matcher;
      bupdate_transform := bupdate_transform;

      benumerate := id;
      bfind      := ListAsBag_bfind;
      binsert    := ListAsBag_binsert;
      bcount     := ListAsBag_bcount;
      bdelete    := ListAsBag_bdelete;
      bupdate    := ListAsBag_bupdate
    |}.

  Global Instance ListAsBagCorrect
  : CorrectBag ListAsBag :=
    {|
      RepInv            := fun _ => True;

      binsert_enumerate := List_BagInsertEnumerate;
      benumerate_empty  := List_BagEnumerateEmpty;
      bfind_star        := List_BagFindStar;
      bfind_correct     := List_BagFindCorrect;
      bcount_correct    := List_BagCountCorrect;
      bdelete_correct   := List_BagDeleteCorrect;
      bupdate_correct   := List_BagUpdateCorrect
    |}.
  Proof.
    eauto.
    unfold binsert_Preserves_RepInv; eauto.
    unfold bdelete_Preserves_RepInv; eauto.
    unfold bupdate_Preserves_RepInv; eauto.
  Qed.

End ListBags.
