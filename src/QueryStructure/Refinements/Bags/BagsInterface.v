Require Export Program Permutation.

Unset Implicit Arguments.

Definition BagInsertEnumerate
           {TContainer TItem: Type}
           (benumerate : TContainer -> list TItem)
           (binsert    : TContainer -> TItem -> TContainer) :=
  forall inserted container,
    Permutation
      (benumerate (binsert container inserted))
      (inserted :: benumerate container).

Definition BagEnumerateEmpty
           {TContainer TItem: Type}
           (benumerate : TContainer -> list TItem)
           (bempty     : TContainer) :=
  forall item, ~ List.In item (benumerate bempty).

Definition BagFindStar
           {TContainer TItem TSearchTerm: Type}
           (bfind : TContainer -> TSearchTerm -> list TItem)
           (benumerate : TContainer -> list TItem)
           (bstar : TSearchTerm) :=
  forall container, bfind container bstar = benumerate container.

Definition BagFindCorrect
           {TContainer TItem TSearchTerm: Type}
           (bfind         : TContainer -> TSearchTerm -> list TItem)
           (bfind_matcher : TSearchTerm -> TItem -> bool)
           (benumerate : TContainer -> list TItem) :=
  forall container search_term,
    Permutation
      (List.filter (bfind_matcher search_term) (benumerate container))
      (bfind container search_term).

Definition BagCountCorrect
           {TContainer TItem TSearchTerm: Type}
           (bcount        : TContainer -> TSearchTerm -> nat)
           (bfind         : TContainer -> TSearchTerm -> list TItem) :=
  forall container search_term,
    List.length (bfind container search_term) = (bcount container search_term).

Class Bag (TContainer TItem TSearchTerm: Type) :=
  {
    bempty        : TContainer;
    bstar         : TSearchTerm;
    bfind_matcher : TSearchTerm -> TItem -> bool;

    benumerate : TContainer -> list TItem;
    bfind      : TContainer -> TSearchTerm -> list TItem;
    binsert    : TContainer -> TItem -> TContainer;
    bcount     : TContainer -> TSearchTerm -> nat;

    binsert_enumerate : BagInsertEnumerate benumerate binsert;
    benumerate_empty  : BagEnumerateEmpty benumerate bempty;
    bfind_star        : BagFindStar bfind benumerate bstar;
    bfind_correct     : BagFindCorrect bfind bfind_matcher benumerate;
    bcount_correct    : BagCountCorrect bcount bfind
  }.

Record BagPlusBagProof {TItem} :=
  { BagType: Type; 
    SearchTermType: Type; 
    BagProof: Bag BagType TItem SearchTermType }.
