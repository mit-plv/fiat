Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Require Export Coq.Program.Program Coq.Sorting.Permutation.

Unset Implicit Arguments.
Global Set Asymmetric Patterns.

(* Enumerating the items of a Bag resulting from inserting
   an item [inserted] into a bag [container] is a permutation
   of adding [inserted] to the original set of elements.
   *)
Definition BagInsertEnumerate
           {TContainer TItem: Type}
           (RepInv : TContainer -> Prop)
           (benumerate : TContainer -> list TItem)
           (binsert    : TContainer -> TItem -> TContainer) :=
  forall inserted container
         (containerCorrect : RepInv container),
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
  forall container search_term
         (containerCorrect : RepInv container),
    Permutation
      (List.filter (bfind_matcher search_term) (benumerate container))
      (bfind container search_term).

(* [bcount] returns the number of elements in a bag which match
   a search term [search_term]. *)
Definition BagCountCorrect
           {TContainer TItem TSearchTerm: Type}
           (RepInv : TContainer -> Prop)
           (bcount        : TContainer -> TSearchTerm -> nat)
           (bfind         : TContainer -> TSearchTerm -> list TItem) :=
  forall container search_term
  (containerCorrect : RepInv container),
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
  forall container search_term
         (containerCorrect : RepInv container),
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
           (ValidUpdate : TUpdateTerm -> Prop)
           (bfind         : TContainer -> TSearchTerm -> list TItem)
           (bfind_matcher : TSearchTerm -> TItem -> bool)
           (benumerate : TContainer -> list TItem)
           (bupdate_transform : TUpdateTerm -> TItem -> TItem)
           (bupdate    : TContainer -> TSearchTerm -> TUpdateTerm -> list TItem * TContainer) :=
  forall container search_term update_term
         (containerCorrect : RepInv container)
         (valid_update : ValidUpdate update_term),
    Permutation (benumerate (snd (bupdate container search_term update_term)))
                   ((snd (List.partition (bfind_matcher search_term)
                                         (benumerate container)))
                      ++ List.map (bupdate_transform update_term)
                      (fst (List.partition (bfind_matcher search_term)
                                           (benumerate container))))
    /\ Permutation (fst (bupdate container search_term update_term))
                   (fst (List.partition (bfind_matcher search_term)
                                     (benumerate container))).

Definition binsert_Preserves_RepInv
           {TContainer TItem: Type}
           (RepInv : TContainer -> Prop)
           (binsert    : TContainer -> TItem -> TContainer)
    := forall container item
              (containerCorrect : RepInv container),
         RepInv (binsert container item).

Definition bdelete_Preserves_RepInv
           {TContainer TItem TSearchTerm: Type}
           (RepInv : TContainer -> Prop)
           (bdelete    : TContainer -> TSearchTerm -> (list TItem) * TContainer)
  := forall container search_term
            (containerCorrect : RepInv container),
       RepInv (snd (bdelete container search_term)).

Definition bupdate_Preserves_RepInv
           {TContainer TItem TSearchTerm TUpdateTerm : Type}
           (RepInv : TContainer -> Prop)
           (ValidUpdate       : TUpdateTerm -> Prop)
           (bupdate    : TContainer -> TSearchTerm -> TUpdateTerm -> (list TItem) * TContainer)
  := forall container search_term update_term
            (containerCorrect : RepInv container)
            (valid_update : ValidUpdate update_term),
       RepInv (snd (bupdate container search_term update_term)).

Class Bag (BagType TItem SearchTermType UpdateTermType : Type) :=
  {

    bempty            : BagType;
    bfind_matcher     : SearchTermType -> TItem -> bool;
    bupdate_transform : UpdateTermType -> TItem -> TItem;

    benumerate : BagType -> list TItem;
    bfind      : BagType -> SearchTermType -> list TItem;
    binsert    : BagType -> TItem -> BagType;
    bcount     : BagType -> SearchTermType -> nat;
    bdelete    : BagType -> SearchTermType -> (list TItem) * BagType;
    bupdate    : BagType -> SearchTermType -> UpdateTermType -> (list TItem) * BagType
  }.


Class CorrectBag
      {BagType TItem SearchTermType UpdateTermType : Type}
      (RepInv            : BagType -> Prop)
      (ValidUpdate       : UpdateTermType -> Prop)
      (BagImplementation : Bag BagType TItem SearchTermType UpdateTermType) :=
{

  bempty_RepInv     : RepInv bempty;
  binsert_RepInv    : binsert_Preserves_RepInv RepInv binsert;
  bdelete_RepInv    : bdelete_Preserves_RepInv RepInv bdelete ;
  bupdate_RepInv    : bupdate_Preserves_RepInv RepInv ValidUpdate bupdate;

  benumerate_empty  : BagEnumerateEmpty benumerate bempty;
  binsert_enumerate : BagInsertEnumerate RepInv benumerate binsert;
  bfind_correct     : BagFindCorrect RepInv bfind bfind_matcher benumerate;
  bcount_correct    : BagCountCorrect RepInv bcount bfind;
  bdelete_correct   : BagDeleteCorrect RepInv bfind bfind_matcher benumerate bdelete;
  bupdate_correct   : BagUpdateCorrect RepInv ValidUpdate bfind bfind_matcher benumerate bupdate_transform bupdate
}.

(* [BagPlusProof] packages a container with its operations and
   their correctness proofs. *)
Record BagPlusProof (TItem : Type) :=
  { BagTypePlus : Type;
    SearchTermTypePlus : Type;
    UpdateTermTypePlus : Type;

    RepInvPlus : BagTypePlus -> Prop;
    ValidUpdatePlus : UpdateTermTypePlus -> Prop;

    BagPlus : Bag BagTypePlus TItem SearchTermTypePlus UpdateTermTypePlus;
    CorrectBagPlus : CorrectBag RepInvPlus ValidUpdatePlus BagPlus
  }.

Arguments BagTypePlus [TItem] _.
Arguments SearchTermTypePlus [TItem] _.
Arguments UpdateTermTypePlus [TItem] _.
Arguments RepInvPlus [TItem] _ _.
Arguments ValidUpdatePlus [TItem] _ _.
Arguments BagPlus [TItem] _.
Arguments CorrectBagPlus [TItem] _.

Instance BagPlusProofAsBag {TItem}
         (bag : BagPlusProof TItem)
: Bag _ _ _ _ := BagPlus bag.

Instance BagPlusProofAsCorrectBag {TItem}
         (bag : BagPlusProof TItem)
: CorrectBag _ _ _ := CorrectBagPlus bag.

(* We can bundle a container and its invariant if we so desire. *)
Definition WFBagPlusType {TItem} (Index : BagPlusProof TItem)
  := sigT (RepInvPlus Index).

Instance WFBagPlusTypeAsBag {TItem}
         (Index : BagPlusProof TItem)
: Bag (WFBagPlusType Index) TItem (SearchTermTypePlus Index)
      (sigT (ValidUpdatePlus Index)).
Proof.
  destruct Index as [? ? ? ? ? BagPlus' CorrectBagPlus'];
  destruct BagPlus'; destruct CorrectBagPlus'; simpl in *.
  econstructor 1; simpl; try solve [eassumption].
  (* bempty *)
  econstructor; eauto.
  (* bupdate_transform *)
  intro; apply bupdate_transform0; apply X.
  (* benumerate *)
  intros; apply benumerate0; apply X.
  (* bfind *)
  intros; destruct X; apply (bfind0 x X0).
  (* binsert *)
  intros; destruct X; econstructor; eapply binsert_RepInv0; apply r.
  (* bcount *)
  intros; destruct X; eapply bcount0; [apply x | apply X0 ].
  (* bdelete *)
  intros x search_term; constructor.
  - eapply (fst (bdelete0 (projT1 x) search_term)).
  - econstructor; eapply bdelete_RepInv0; apply (projT2 x).
  (* bupdate *)
  - intros x search_term update_term; destruct x; destruct update_term;
    econstructor.
    eapply (fst (bupdate0 x search_term x0)).
    econstructor; eapply bupdate_RepInv0.
    apply r.
    apply v.
    Grab Existential Variables.
    simpl; apply search_term.
    simpl; apply search_term.
    apply X0.
Defined.

Instance WFBagPlusTypeAsCorrectBag {TItem}
         (Index : BagPlusProof TItem)
: CorrectBag (fun _ => True) (fun _ => True) (WFBagPlusTypeAsBag Index).
Proof.
  destruct Index as [? ? ? ? ? BagPlus' CorrectBagPlus'];
  destruct BagPlus'; destruct CorrectBagPlus'; simpl in *.
  constructor; simpl; eauto;
  cbv delta [binsert_Preserves_RepInv
               bupdate_Preserves_RepInv
               bdelete_Preserves_RepInv
               BagInsertEnumerate
               BagEnumerateEmpty
               BagFindCorrect
               BagCountCorrect
               BagDeleteCorrect
               BagUpdateCorrect]; simpl; eauto;
  try (solve [intros; destruct container; eauto]).
  (* bupdate_correct *)
  destruct container; simpl; intros.
  destruct update_term; eauto.
  eapply bupdate_correct0.
  eapply r.
  eapply v.
Qed.
