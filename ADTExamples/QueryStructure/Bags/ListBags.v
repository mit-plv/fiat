Require Export Bags.
Unset Implicit Arguments.

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

Lemma List_BagInsertEnumerate :
  forall {TItem: Type},
  BagInsertEnumerate id (ListAsBag_binsert (TItem := TItem)).
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

Lemma List_BagEnumerateEmpty :
  forall {TItem: Type},
    BagEnumerateEmpty id (@nil TItem).
Proof.
  firstorder.
Qed.
  
Lemma List_BagFindCorrect :
  forall {TItem TSearchTerm: Type}
         (matcher: TSearchTerm -> TItem -> bool),
         BagFindCorrect (ListAsBag_bfind matcher) matcher id.
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
    
    binsert_enumerate := List_BagInsertEnumerate;
    benumerate_empty  := List_BagEnumerateEmpty;
    bfind_star        := List_BagFindStar star matcher find_star;
    bfind_correct     := List_BagFindCorrect matcher
  |}.
