Require Export BagsInterface.
Unset Implicit Arguments.

Record CountingList {A} := 
  {
    clength   : nat;
    ccontents : list A;
    cconsistent: List.length ccontents = clength
  }.

Fixpoint MatchAgainstMany {TItem}
         (search_terms : list (TItem -> bool)) (item: TItem) :=
  match search_terms with
    | nil                      => true
    | cons is_match more_terms => andb (is_match item) (MatchAgainstMany more_terms item)
  end.

Definition CountingListAsBag_bfind 
           {TItem: Type}
           (container: @CountingList TItem) (search_terms: list (TItem -> bool)) :=
  match search_terms with
    | nil                      => ccontents container
    | cons is_match more_terms => List.filter (MatchAgainstMany search_terms) (ccontents container)
  end.

Lemma CountingList_insert :
  forall (TItem : Type) (container : @CountingList TItem) (item : TItem),
    length (item :: ccontents container) = S (clength container).
Proof.
  intros; rewrite <- (cconsistent container); reflexivity.
Qed.

Definition CountingListAsBag_binsert 
           {TItem: Type}
           (container: @CountingList TItem) 
           (item: TItem) : @CountingList TItem :=
  {| clength := S (clength container);
     ccontents := cons item (ccontents container);
     cconsistent := CountingList_insert TItem container item |}.

Definition CountingListAsBag_bcount
           {TItem: Type}
           (container: @CountingList TItem) (search_terms: list (TItem -> bool)) :=
  match search_terms with
    | nil => clength container
    | _   => List.fold_left (fun acc x => acc + if (MatchAgainstMany search_terms x) then 1 else 0) 
                            (ccontents container) 0
  end.

Lemma CountingList_BagInsertEnumerate :
  forall {TItem: Type},
  BagInsertEnumerate ccontents (CountingListAsBag_binsert (TItem := TItem)).
Proof.
  firstorder.
Qed.

Lemma empty_length {A} :
  List.length (@nil A) = 0.
Proof.
  reflexivity.
Qed.

Definition CountingList_empty {TItem} : @CountingList TItem :=
  {| 
    clength := 0;
    ccontents := @nil TItem;
    cconsistent := empty_length
  |}.

Lemma CountingList_BagEnumerateEmpty :
  forall {TItem: Type},
    BagEnumerateEmpty ccontents (@CountingList_empty TItem).
Proof.
  firstorder.
Qed.
  
Lemma CountingList_BagFindStar :
  forall {TItem: Type},
    BagFindStar (CountingListAsBag_bfind) (@ccontents TItem) nil.
Proof.
  firstorder.
Qed.

Require Import AdditionalLemmas.

Lemma CountingList_BagFindCorrect :
  forall {TItem: Type},
         BagFindCorrect CountingListAsBag_bfind (@MatchAgainstMany TItem) (ccontents).
Proof.
  destruct search_term; simpl; [ rewrite filter_all_true | ]; reflexivity.
Qed.

Require Import Omega.
Lemma CountingList_BagCountCorrect_aux :
  forall {TItem: Type},
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
  forall {TItem: Type},
    BagCountCorrect (TItem := TItem) (CountingListAsBag_bcount) (CountingListAsBag_bfind).
Proof.
  unfold BagCountCorrect, CountingListAsBag_bcount, CountingListAsBag_bfind; intros;
  pose proof (CountingList_BagCountCorrect_aux (ccontents container) search_term 0) as temp;
  rewrite plus_0_r in temp; simpl in temp;
  destruct search_term; simpl; [ apply cconsistent | apply temp ].
Qed.

Instance CountingListAsBag {TItem: Type}
: Bag (@CountingList TItem) TItem (list (TItem -> bool)) :=
  {| 
    bempty := CountingList_empty;
    bstar  := nil;
    
    benumerate := ccontents;
    bfind      := CountingListAsBag_bfind;
    binsert    := CountingListAsBag_binsert;
    bcount     := CountingListAsBag_bcount;
    
    binsert_enumerate := CountingList_BagInsertEnumerate;
    benumerate_empty  := CountingList_BagEnumerateEmpty;
    bfind_star        := CountingList_BagFindStar;
    bfind_correct     := CountingList_BagFindCorrect;
    bcount_correct    := CountingList_BagCountCorrect
  |}.
