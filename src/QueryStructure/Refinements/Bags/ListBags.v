Require Export BagsInterface.
Unset Implicit Arguments.

Open Scope list.

Definition ListAsBag_bfind 
           {TItem TSearchTerm: Type}
           (matcher: TSearchTerm -> TItem -> bool) 
           (container: list TItem) (search_term: TSearchTerm) :=
  List.filter (matcher search_term) container.

Definition ListAsBag_binsert 
           {TItem: Type}
           (container: list TItem) 
           (item: TItem) :=
  cons item container.

Definition ListAsBag_bcount
           {TItem TSearchTerm: Type}
           (matcher: TSearchTerm -> TItem -> bool) 
           (container: list TItem) (search_term: TSearchTerm) :=
  List.fold_left (fun acc x => acc + if (matcher search_term x) then 1 else 0) container 0.

Definition ListAsBag_bdelete
           {TItem TSearchTerm: Type}
           (bfind_matcher : TSearchTerm -> TItem -> bool)
           (container : list TItem)
           (search_term : TSearchTerm) :=
  snd (List.partition (bfind_matcher search_term) container).

Definition ListAsBag_bupdate
           {TItem TSearchTerm: Type}
           (bfind_matcher : TSearchTerm -> TItem -> bool)
           (container : list TItem)
           (search_term : TSearchTerm) 
           (f_update : TItem -> TItem) :=
  (snd (List.partition (bfind_matcher search_term) container))
       ++ List.map f_update (fst (List.partition (bfind_matcher search_term)
                                                 container)).

Lemma List_BagInsertEnumerate :
  forall {TItem: Type},
  BagInsertEnumerate id (ListAsBag_binsert (TItem := TItem)).
Proof.
  firstorder.
Qed.

Lemma List_BagEnumerateEmpty :
  forall {TItem: Type},
    BagEnumerateEmpty id (@nil TItem).
Proof.
  firstorder.
Qed.
  
Lemma List_BagFindStar :
  forall {TItem TSearchTerm: Type}
         (star: TSearchTerm)
         (matcher: TSearchTerm -> TItem -> bool)
         (find_star: forall (i: TItem), matcher star i = true),
  BagFindStar (ListAsBag_bfind matcher) id star.
Proof.
  intros;
  induction container; simpl; 
  [ | rewrite find_star, IHcontainer]; trivial.
Qed.

Lemma List_BagFindCorrect :
  forall {TItem TSearchTerm: Type}
         (matcher: TSearchTerm -> TItem -> bool),
         BagFindCorrect (ListAsBag_bfind matcher) matcher id.
Proof.
  firstorder.
Qed.

Require Import Omega.
Lemma List_BagCountCorrect_aux :
  forall {TItem TSearchTerm: Type}
         (matcher: TSearchTerm -> TItem -> bool),
  forall (container: list TItem) (search_term: TSearchTerm) default,
    length (List.filter (matcher search_term) container) + default =
    List.fold_left
      (fun (acc : nat) (x : TItem) =>
         acc + (if matcher search_term x then 1 else 0)) 
      container default.
Proof.
  induction container; intros.

  + trivial.
  + simpl; destruct (matcher search_term a);
    simpl; rewrite <- IHcontainer; omega. 
Qed.

Lemma List_BagCountCorrect :
  forall {TItem TSearchTerm: Type}
         (matcher: TSearchTerm -> TItem -> bool),
         BagCountCorrect (ListAsBag_bcount matcher) (ListAsBag_bfind matcher).
Proof.
  unfold BagCountCorrect, ListAsBag_bcount, ListAsBag_bfind; intros;
  pose proof (List_BagCountCorrect_aux matcher container search_term 0) as temp;
  rewrite plus_0_r in temp; simpl in temp; exact temp.
Qed.

Lemma List_BagDeleteCorrect :
  forall {TItem TSearchTerm: Type}
         (matcher: TSearchTerm -> TItem -> bool),
    BagDeleteCorrect (ListAsBag_bfind matcher) matcher id
                     (ListAsBag_bdelete matcher).
Proof.
  firstorder.
Qed.

Lemma List_BagUpdateCorrect :
  forall {TItem TSearchTerm: Type}
         (matcher: TSearchTerm -> TItem -> bool),
    BagUpdateCorrect (ListAsBag_bfind matcher) matcher id
   (ListAsBag_bupdate matcher).
Proof.
  firstorder.
Qed.

Instance ListAsBag
         {TItem TSearchTerm: Type}
         (star: TSearchTerm)
         (matcher: TSearchTerm -> TItem -> bool)
         (find_star: forall (i: TItem), matcher star i = true)
: Bag (list TItem) TItem TSearchTerm :=
  {| 
    bempty := nil;
    bstar  := star;
    
    benumerate := id;
    bfind      := ListAsBag_bfind matcher;
    binsert    := ListAsBag_binsert;
    bcount     := ListAsBag_bcount matcher;
    bdelete    := ListAsBag_bdelete matcher;
    bupdate    := ListAsBag_bupdate matcher;

    binsert_enumerate := List_BagInsertEnumerate;
    benumerate_empty  := List_BagEnumerateEmpty;
    bfind_star        := List_BagFindStar star matcher find_star;
    bfind_correct     := List_BagFindCorrect matcher;
    bcount_correct    := List_BagCountCorrect matcher;
    bdelete_correct   := List_BagDeleteCorrect matcher;
    bupdate_correct   := List_BagUpdateCorrect matcher
  |}.
