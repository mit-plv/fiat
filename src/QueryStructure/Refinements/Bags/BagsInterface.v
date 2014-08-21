Require Export Program Permutation.

Unset Implicit Arguments.

(* Enumerating the items of a Bag resulting from inserting
   an item [inserted] into a bag [container] is a permutation
   of adding [inserted] to the original set of elements.
   *)
Definition BagInsertEnumerate
           {TContainer TItem: Type}
           (benumerate : TContainer -> list TItem)
           (binsert    : TContainer -> TItem -> TContainer) :=
  forall inserted container,
    Permutation
      (benumerate (binsert container inserted))
      (inserted :: benumerate container).

(* The enumeration of an empty bag [bempty] is an empty list. *)
Definition BagEnumerateEmpty
           {TContainer TItem: Type}
           (benumerate : TContainer -> list TItem)
           (bempty     : TContainer) :=
  forall item, ~ List.In item (benumerate bempty).

(* [bfind] returns a permutation of the elements in a bag
   [container] filtered by the match function [bfind_matcher]
   using the specified search term [search_term]. *)
Definition BagFindCorrect
           {TContainer TItem TSearchTerm: Type}
           (bfind         : TContainer -> TSearchTerm -> list TItem)
           (bfind_matcher : TSearchTerm -> TItem -> bool)
           (benumerate : TContainer -> list TItem) :=
  forall container search_term,
    Permutation
      (List.filter (bfind_matcher search_term) (benumerate container))
      (bfind container search_term).

(* The [bstar] search term matches every item in a bag. *)
Definition BagFindStar
           {TContainer TItem TSearchTerm: Type}
           (bfind : TContainer -> TSearchTerm -> list TItem)
           (benumerate : TContainer -> list TItem)
           (bstar : TSearchTerm) :=
  forall container, bfind container bstar = benumerate container.

(* The [bid] update term is the identity function *)
Definition BagUpdateID
           {TContainer TItem TUpdateTerm: Type}
           (bupdate_transform : TUpdateTerm -> TUpdateTerm -> TItem)
           (bid : TUpdateTerm) :=
  forall item, bupdate_transform bid item = bupdate_transform bid item.

(* [bcount] returns the number of elements in a bag which match
   a search term [search_term]. *)
Definition BagCountCorrect
           {TContainer TItem TSearchTerm: Type}
           (bcount        : TContainer -> TSearchTerm -> nat)
           (bfind         : TContainer -> TSearchTerm -> list TItem) :=
  forall container search_term,
    List.length (bfind container search_term) = (bcount container search_term).

(* The elements of a bag [container] from which all elements matching
   [search_term] have been deleted is a permutation of filtering
   the enumeration of [container] by the negation of [search_term]. *)
Definition BagDeleteCorrect
           {TContainer TItem TSearchTerm: Type}
           (bfind         : TContainer -> TSearchTerm -> list TItem)
           (bfind_matcher : TSearchTerm -> TItem -> bool)
           (benumerate : TContainer -> list TItem)
           (bdelete    : TContainer -> TSearchTerm -> (list TItem) * TContainer) :=
  forall container search_term,
    Permutation (benumerate (snd (bdelete container search_term)))
                (snd (List.partition (bfind_matcher search_term)
                                     (benumerate container)))
    /\ Permutation (fst (bdelete container search_term))
                   (fst (List.partition (bfind_matcher search_term)
                                     (benumerate container))).

(* The elements of a bag [container] in which the function [f_update]
   has been applied to all elements matching [search_term]
   is a permutation of partitioning the list into non-matching terms
   and matching terms and mapping [f_update] over the latter. *)
Definition BagUpdateCorrect
           {TContainer TItem TSearchTerm TUpdateTerm : Type}
           (bfind         : TContainer -> TSearchTerm -> list TItem)
           (bfind_matcher : TSearchTerm -> TItem -> bool)
           (benumerate : TContainer -> list TItem)
           (bupdate_transform : TUpdateTerm -> TItem -> TItem)
           (bupdate    : TContainer -> TSearchTerm -> TUpdateTerm -> TContainer) :=
  forall container search_term update_term,
    Permutation (benumerate (bupdate container search_term update_term))
                   ((snd (List.partition (bfind_matcher search_term)
                                         (benumerate container)))
                      ++ List.map (bupdate_transform update_term)
                      (fst (List.partition (bfind_matcher search_term)
                                           (benumerate container)))).

Class Bag (TContainer TItem TSearchTerm TUpdateTerm : Type) :=
  {
    bempty            : TContainer;
    bstar             : TSearchTerm;
    bid               : TUpdateTerm;
    bfind_matcher     : TSearchTerm -> TItem -> bool;
    bupdate_transform : TUpdateTerm -> TItem -> TItem;

    benumerate : TContainer -> list TItem;
    bfind      : TContainer -> TSearchTerm -> list TItem;
    binsert    : TContainer -> TItem -> TContainer;
    bcount     : TContainer -> TSearchTerm -> nat;
    bdelete    : TContainer -> TSearchTerm -> (list TItem) * TContainer;
    bupdate    : TContainer -> TSearchTerm -> TUpdateTerm -> TContainer;

    binsert_enumerate : BagInsertEnumerate benumerate binsert;
    benumerate_empty  : BagEnumerateEmpty benumerate bempty;
    bfind_star        : BagFindStar bfind benumerate bstar;
    bfind_correct     : BagFindCorrect bfind bfind_matcher benumerate;
    bcount_correct    : BagCountCorrect bcount bfind;
    bdelete_correct   : BagDeleteCorrect bfind bfind_matcher benumerate bdelete;
    bupdate_correct   : BagUpdateCorrect bfind bfind_matcher benumerate bupdate_transform bupdate
  }.

Record BagPlusBagProof {TItem} :=
  { BagType: Type;
    SearchTermType: Type;
    UpdateTermType: Type;
    BagProof: Bag BagType TItem SearchTermType UpdateTermType}.
