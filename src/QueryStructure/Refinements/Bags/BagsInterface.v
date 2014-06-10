Require Export Program SetEq SetEqProperties.

Unset Implicit Arguments.

Definition HasDecidableEquality (T: Type) :=
  forall (x y: T), {x = y} + {x <> y}.

Definition BagInsertEnumerate
           {TContainer TItem: Type}
           (benumerate : TContainer -> list TItem)
           (binsert    : TContainer -> TItem -> TContainer) :=
  forall item inserted container,
    List.In item (benumerate (binsert container inserted)) <->
    List.In item (benumerate container) \/ item = inserted.

Definition BagInsertCount
           {TContainer TItem}
           (benumerate : TContainer -> list TItem)
           (binsert    : TContainer -> TItem -> TContainer)
           (bcount     : HasDecidableEquality TItem -> TContainer -> TItem -> nat) :=
  forall (beq : HasDecidableEquality TItem),
  forall item inserted container,
    bcount beq (binsert container inserted) item =
    bcount beq container item + (if beq item inserted then 1 else 0).

Definition BagEnumerateEmpty
           {TContainer TItem: Type}
           (benumerate : TContainer -> list TItem)
           (bempty     : TContainer) :=
  forall item, ~ List.In item (benumerate bempty).

Definition BagCountEmpty
           {TContainer TItem: Type}
           (benumerate : TContainer -> list TItem)
           (bempty     : TContainer)
           (bcount     : HasDecidableEquality TItem -> TContainer -> TItem -> nat) :=
  forall (beq : HasDecidableEquality TItem),
  forall item, bcount beq bempty item = 0. 

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
    SetEq
      (List.filter (bfind_matcher search_term) (benumerate container))
      (bfind container search_term).

Class Bag (TContainer TItem TSearchTerm: Type) :=
  {
    bempty        : TContainer;
    bstar         : TSearchTerm;
    bfind_matcher : TSearchTerm -> TItem -> bool;

    benumerate : TContainer -> list TItem;
    bfind      : TContainer -> TSearchTerm -> list TItem;
    binsert    : TContainer -> TItem -> TContainer;
    bcount     : HasDecidableEquality TItem -> TContainer -> TItem -> nat;

    binsert_enumerate : BagInsertEnumerate benumerate binsert;
    binsert_count     : BagInsertCount benumerate binsert bcount;
    benumerate_empty  : BagEnumerateEmpty benumerate bempty;
    bcount_empty      : BagCountEmpty benumerate bempty bcount;
    bfind_star        : BagFindStar bfind benumerate bstar;
    bfind_correct     : BagFindCorrect bfind bfind_matcher benumerate
  }.

Record BagPlusBagProof {TItem} :=
  { BagType: Type; 
    SearchTermType: Type; 
    BagProof: Bag BagType TItem SearchTermType }.
