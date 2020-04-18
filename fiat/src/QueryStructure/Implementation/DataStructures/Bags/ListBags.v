Require Export Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsInterface.
Unset Implicit Arguments.

Open Scope list_scope.

Section ListBags.

  Context {TItem : Type}
          {TSearchTerm : Type}
          {TUpdateTerm : Type}
          (bid : TUpdateTerm)
          (bfind_matcher: TSearchTerm -> TItem -> bool)
          (bupdate_transform : TUpdateTerm -> TItem -> TItem).

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
    ((fst (List.partition (bfind_matcher search_term) container)),
     ((snd (List.partition (bfind_matcher search_term) container))
        ++ List.map (bupdate_transform update_term)
        (fst (List.partition (bfind_matcher search_term) container)))).

  Definition ListBag_RepInv (_ : list TItem) := True.
  Definition ListBag_ValidUpdate (_ : TUpdateTerm) := True.

  Lemma List_BagInsertEnumerate :
    BagInsertEnumerate ListBag_RepInv id (ListAsBag_binsert).
  Proof.
    firstorder.
  Qed.

  Lemma List_BagEnumerateEmpty :
    BagEnumerateEmpty id (@nil TItem).
  Proof.
    firstorder.
  Qed.

  Lemma List_BagFindCorrect :
    BagFindCorrect ListBag_RepInv ListAsBag_bfind bfind_matcher id.
  Proof.
    firstorder.
  Qed.

  Require Import Coq.omega.Omega.
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
    BagCountCorrect ListBag_RepInv ListAsBag_bcount ListAsBag_bfind.
  Proof.
    unfold BagCountCorrect, ListAsBag_bcount, ListAsBag_bfind; intros;
    pose proof (List_BagCountCorrect_aux container search_term 0) as temp;
    rewrite plus_0_r in temp; simpl in temp; exact temp.
  Qed.

  Lemma List_BagDeleteCorrect :
    BagDeleteCorrect ListBag_RepInv ListAsBag_bfind bfind_matcher id ListAsBag_bdelete.
  Proof.
    firstorder.
  Qed.

  Lemma List_BagUpdateCorrect :
    BagUpdateCorrect ListBag_RepInv ListBag_ValidUpdate
                     ListAsBag_bfind bfind_matcher id bupdate_transform ListAsBag_bupdate.
  Proof.
    firstorder.
  Qed.

  Global Instance ListAsBag
  : Bag (list TItem) TItem TSearchTerm TUpdateTerm :=
    {
      bempty            := nil;
      bfind_matcher     := bfind_matcher;
      bupdate_transform := bupdate_transform;

      benumerate := id;
      bfind      := ListAsBag_bfind;
      binsert    := ListAsBag_binsert;
      bcount     := ListAsBag_bcount;
      bdelete    := ListAsBag_bdelete;
      bupdate    := ListAsBag_bupdate
    }.

  Global Instance ListAsBagCorrect
  : CorrectBag ListBag_RepInv ListBag_ValidUpdate ListAsBag :=
    {|

      binsert_enumerate := List_BagInsertEnumerate;
      benumerate_empty  := List_BagEnumerateEmpty;

      bfind_correct     := List_BagFindCorrect;
      bcount_correct    := List_BagCountCorrect;
      bdelete_correct   := List_BagDeleteCorrect;
      bupdate_correct   := List_BagUpdateCorrect
    |}.
  Proof.
    unfold ListBag_RepInv; eauto.
    unfold binsert_Preserves_RepInv; eauto.
    unfold bdelete_Preserves_RepInv; eauto.
    unfold bupdate_Preserves_RepInv; eauto.
  Qed.

End ListBags.
