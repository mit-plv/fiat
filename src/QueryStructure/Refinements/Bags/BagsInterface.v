Require Export Program Permutation.

Unset Implicit Arguments.

(* Enumerating the items of a Bag resulting from inserting
   an item [inserted] into a bag [container] is a permutation
   of adding [inserted] to the original set of elements.
   *)
Definition BagInsertEnumerate
           {TContainer TItem: Type}
           (RepInv : TContainer -> Prop)
           (benumerate : TContainer -> list TItem)
           (binsert    : TContainer -> TItem -> TContainer) :=
  forall inserted container,
    RepInv container ->
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
           (RepInv : TContainer -> Prop)
           (bfind         : TContainer -> TSearchTerm -> list TItem)
           (bfind_matcher : TSearchTerm -> TItem -> bool)
           (benumerate : TContainer -> list TItem) :=
  forall container search_term,
    RepInv container ->
    Permutation
      (List.filter (bfind_matcher search_term) (benumerate container))
      (bfind container search_term).

(* The [bstar] search term matches every item in a bag. *)
Definition BagFindStar
           {TContainer TItem TSearchTerm: Type}
           (RepInv : TContainer -> Prop)
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
           (RepInv : TContainer -> Prop)
           (bcount        : TContainer -> TSearchTerm -> nat)
           (bfind         : TContainer -> TSearchTerm -> list TItem) :=
  forall container search_term,
    RepInv container ->
    List.length (bfind container search_term) = (bcount container search_term).

(* The elements of a bag [container] from which all elements matching
   [search_term] have been deleted is a permutation of filtering
   the enumeration of [container] by the negation of [search_term]. *)
Definition BagDeleteCorrect
           {TContainer TItem TSearchTerm: Type}
           (RepInv : TContainer -> Prop)
           (bfind         : TContainer -> TSearchTerm -> list TItem)
           (bfind_matcher : TSearchTerm -> TItem -> bool)
           (benumerate : TContainer -> list TItem)
           (bdelete    : TContainer -> TSearchTerm -> (list TItem) * TContainer) :=
  forall container search_term,
    RepInv container ->
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
           (RepInv : TContainer -> Prop)
           (bfind         : TContainer -> TSearchTerm -> list TItem)
           (bfind_matcher : TSearchTerm -> TItem -> bool)
           (benumerate : TContainer -> list TItem)
           (bupdate_transform : TUpdateTerm -> TItem -> TItem)
           (bupdate    : TContainer -> TSearchTerm -> TUpdateTerm -> TContainer) :=
  forall container search_term update_term,
    RepInv container ->
    Permutation (benumerate (bupdate container search_term update_term))
                   ((snd (List.partition (bfind_matcher search_term)
                                         (benumerate container)))
                      ++ List.map (bupdate_transform update_term)
                      (fst (List.partition (bfind_matcher search_term)
                                           (benumerate container)))).

Definition binsert_Preserves_RepInv
           {TContainer TItem: Type}
           (RepInv : TContainer -> Prop)
           (binsert    : TContainer -> TItem -> TContainer)
    := forall container item,
                        RepInv container
                        -> RepInv (binsert container item).

Definition bdelete_Preserves_RepInv
           {TContainer TItem TSearchTerm: Type}
           (RepInv : TContainer -> Prop)
           (bdelete    : TContainer -> TSearchTerm -> (list TItem) * TContainer)
  := forall container search_term,
                        RepInv container
                        -> RepInv (snd (bdelete container search_term)).

Definition bupdate_Preserves_RepInv    
           {TContainer TSearchTerm TUpdateTerm : Type}
           (RepInv : TContainer -> Prop)
           (bupdate    : TContainer -> TSearchTerm -> TUpdateTerm -> TContainer)
  := forall container search_term update_term,
       RepInv container
       -> RepInv (bupdate container search_term update_term).
       
Class Bag (TItem : Type) :=
  {
    BagType : Type;
    SearchTermType : Type;
    UpdateTermType : Type;

    bempty            : BagType;
    bstar             : SearchTermType;
    bid               : UpdateTermType;
    bfind_matcher     : SearchTermType -> TItem -> bool;
    bupdate_transform : UpdateTermType -> TItem -> TItem;

    benumerate : BagType -> list TItem;
    bfind      : BagType -> SearchTermType -> list TItem;
    binsert    : BagType -> TItem -> BagType;
    bcount     : BagType -> SearchTermType -> nat;
    bdelete    : BagType -> SearchTermType -> (list TItem) * BagType;
    bupdate    : BagType -> SearchTermType -> UpdateTermType -> BagType
  }.


Class CorrectBag {TItem} (BagImplementation : Bag TItem) :=
{
  RepInv            : BagType -> Prop;

  bempty_RepInv     : RepInv bempty;
  binsert_RepInv    : binsert_Preserves_RepInv RepInv binsert;
  bdelete_RepInv    : bdelete_Preserves_RepInv RepInv bdelete ;
  bupdate_RepInv    : bupdate_Preserves_RepInv RepInv bupdate;

  binsert_enumerate : BagInsertEnumerate RepInv benumerate binsert;
  benumerate_empty  : BagEnumerateEmpty benumerate bempty;
  bfind_star        : BagFindStar RepInv bfind benumerate bstar;
  bfind_correct     : BagFindCorrect RepInv bfind bfind_matcher benumerate;
  bcount_correct    : BagCountCorrect RepInv bcount bfind;
  bdelete_correct   : BagDeleteCorrect RepInv bfind bfind_matcher benumerate bdelete;
  bupdate_correct   : BagUpdateCorrect RepInv bfind bfind_matcher benumerate bupdate_transform bupdate
}.
