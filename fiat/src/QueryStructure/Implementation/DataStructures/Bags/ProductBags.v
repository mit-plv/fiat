Require Export Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsInterface
        Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsProperties.

Unset Implicit Arguments.

Section ProductBag.

  Context {BagType TItem TSearchTerm_A TSearchTerm_B TUpdateTerm : Type}
          (TBag_A : Bag BagType TItem TSearchTerm_A TUpdateTerm)
          (TBag_B : Bag BagType TItem TSearchTerm_B TUpdateTerm)
          (RepInv_A : BagType -> Prop)
          (RepInv_B : BagType -> Prop)
          (ValidUpdate_A : TUpdateTerm -> Prop)
          (ValidUpdate_B : TUpdateTerm -> Prop)
          (TBagCorrect_A : CorrectBag RepInv_A ValidUpdate_A TBag_A)
          (TBagCorrect_B : CorrectBag RepInv_B ValidUpdate_B TBag_B).

  Inductive TSearchTermChoice := ProdChoiceA | ProdChoiceB.

  Class ProdSearchTerm :=
    { Prod_st_A : TSearchTerm_A;
      Prod_st_B : TSearchTerm_B;
      Prod_st_choice : TSearchTermChoice;
      Prod_st_proof :
        forall item, bfind_matcher Prod_st_A item = bfind_matcher Prod_st_B item }.

  Class ProdUpdateTerm :=
    { Prod_ut : TUpdateTerm;
      Prod_ut_proof :
        forall item, bupdate_transform (Bag:=TBag_A) Prod_ut item =
                     bupdate_transform (Bag:=TBag_B) Prod_ut item }.

  Definition ProdBag := prod BagType BagType.

  Definition ProdBag_bempty := (@bempty _ _ _ _ TBag_A, @bempty _ _ _ _ TBag_B).

  Definition ProdBag_bfind_matcher
             (searchterm : ProdSearchTerm) (item: TItem) :=
    match Prod_st_choice with
    | ProdChoiceA => bfind_matcher Prod_st_A item
    | ProdChoiceB => bfind_matcher Prod_st_B item
    end.

  Definition ProdBag_bupdate_transform := bupdate_transform (Bag:=TBag_A).

  Definition ProdBag_benumerate
             (container : ProdBag) := benumerate (Bag:=TBag_A) (fst container).

  Definition ProdBag_bfind
             (container : ProdBag)
             (searchterm : ProdSearchTerm) :=
    match Prod_st_choice with
    | ProdChoiceA => bfind (Bag:=TBag_A) (fst container) Prod_st_A
    | ProdChoiceB => bfind (Bag:=TBag_B) (snd container) Prod_st_B
    end.

  Definition ProdBag_binsert
             (container : ProdBag)
             (item : TItem) :=
    (binsert (Bag:=TBag_A) (fst container) item,
     binsert (Bag:=TBag_B) (snd container) item).

  Definition ProdBag_bcount
             (container : ProdBag)
             (searchterm : ProdSearchTerm) :=
    match Prod_st_choice with
    | ProdChoiceA => bcount (fst container) Prod_st_A
    | ProdChoiceB => bcount (snd container) Prod_st_B
    end.

  Definition ProdBag_bdelete
             (container : ProdBag)
             (searchterm : ProdSearchTerm) : list TItem * ProdBag :=
    let (resultA, bagA) := bdelete (fst container) Prod_st_A in
    let (resultB, bagB) := bdelete (snd container) Prod_st_B in
    match Prod_st_choice with
    | ProdChoiceA => (resultA, (bagA, bagB))
    | ProdChoiceB => (resultB, (bagA, bagB))
    end.

  Definition ProdBag_bupdate
             (container: ProdBag)
             (searchterm: ProdSearchTerm)
             (updateterm : TUpdateTerm) : list TItem * ProdBag :=
    let (resultA, bagA) := bupdate (Bag:=TBag_A) (fst container) Prod_st_A updateterm in
    let (resultB, bagB) := bupdate (Bag:=TBag_B) (snd container) Prod_st_B updateterm in
    match Prod_st_choice with
    | ProdChoiceA => (resultA, (bagA, bagB))
    | ProdChoiceB => (resultB, (bagA, bagB))
    end.

  Definition ProdBag_RepInv (container : ProdBag) :=
    RepInv_A (fst container) /\
    RepInv_B (snd container) /\
    Permutation (benumerate (Bag:=TBag_A) (fst container))
                (benumerate (Bag:=TBag_B) (snd container)).

  Definition ProdBag_ValidUpdate (updateterm : TUpdateTerm) :=
    ValidUpdate_A updateterm /\
    ValidUpdate_B updateterm /\
    forall item, bupdate_transform (Bag:=TBag_A) updateterm item =
                 bupdate_transform (Bag:=TBag_B) updateterm item.

  Lemma ProdBag_Empty_RepInv :
    ProdBag_RepInv ProdBag_bempty.
  Proof.
    unfold ProdBag_RepInv, ProdBag_bempty; intuition; simpl;
    [ apply bempty_RepInv | apply bempty_RepInv | ].
    assert (forall A (ls ls' : list A), ls = nil -> ls' = nil -> Permutation ls ls') as perm_nil by (intuition; subst; constructor).
    assert (forall A (ls : list A), (forall a, ~ List.In a ls) -> ls = nil) as emp.
    intros; destruct ls; eauto; specialize (H a); simpl in H; tauto.
    eapply perm_nil.
    eapply emp; eapply benumerate_empty.
    eapply emp; eapply benumerate_empty.
  Qed.

  Lemma ProdBag_binsert_Preserves_RepInv :
    binsert_Preserves_RepInv ProdBag_RepInv ProdBag_binsert.
  Proof.
    unfold binsert_Preserves_RepInv, ProdBag_RepInv.
    intros container item [repA [repB repP] ]; intuition.
    - eapply binsert_RepInv; eauto.
    - eapply binsert_RepInv; eauto.
    - eapply perm_trans; [ eapply binsert_enumerate | ]; eauto.
      eapply perm_trans; [ | symmetry; eapply binsert_enumerate ]; eauto.
  Qed.

  Lemma ProdBag_bdelete_Preserves_RepInv :
    bdelete_Preserves_RepInv ProdBag_RepInv ProdBag_bdelete.
  Proof.
    unfold bdelete_Preserves_RepInv, ProdBag_bdelete.
    intros container st [repA [repB repP] ].
    rewrite surjective_pairing with (p:=bdelete (fst container) Prod_st_A).
    rewrite surjective_pairing with (p:=bdelete (snd container) Prod_st_B).
    unfold ProdBag_RepInv; intuition.
    - destruct Prod_st_choice; eapply bdelete_RepInv; eauto.
    - destruct Prod_st_choice; eapply bdelete_RepInv; eauto.
    - destruct Prod_st_choice; simpl;
      (eapply perm_trans; [ eapply bdelete_correct | ]; eauto;
      eapply perm_trans; [ | symmetry; eapply bdelete_correct ]; eauto;
      rewrite !ListFacts.partition_filter_neq;
      apply ListMorphisms.filter_permutation_morphism; eauto;
      unfold Morphisms.pointwise_relation; intro; f_equal; eapply Prod_st_proof).
  Qed.

  Lemma ProdBag_bupdate_Preserves_RepInv :
    bupdate_Preserves_RepInv ProdBag_RepInv ProdBag_ValidUpdate ProdBag_bupdate.
  Proof.
    unfold bupdate_Preserves_RepInv, ProdBag_bupdate.
    intros container st ut [repA [repB repP] ] [valA [valB valP] ].
    rewrite surjective_pairing with (p:=bupdate (fst container) Prod_st_A ut).
    rewrite surjective_pairing with (p:=bupdate (snd container) Prod_st_B ut).
    unfold ProdBag_RepInv; intuition.
    - destruct Prod_st_choice; eapply bupdate_RepInv; eauto.
    - destruct Prod_st_choice; eapply bupdate_RepInv; eauto.
    - destruct Prod_st_choice; simpl;
      (eapply perm_trans; [ eapply bupdate_correct | ]; eauto;
      eapply perm_trans; [ | symmetry; eapply bupdate_correct ]; eauto;
      eapply Permutation_app;
        [ rewrite !ListFacts.partition_filter_neq |
          eapply ListMorphisms.map_permutation_morphism;
            [ unfold Morphisms.pointwise_relation; eapply valP |
              rewrite !ListFacts.partition_filter_eq ] ];
      eapply ListMorphisms.filter_permutation_morphism; eauto;
      unfold Morphisms.pointwise_relation; intro; f_equal; eapply Prod_st_proof).
  Qed.

  Lemma ProdBag_BagInsertEnumerate :
    BagInsertEnumerate ProdBag_RepInv ProdBag_benumerate ProdBag_binsert.
  Proof.
    unfold BagInsertEnumerate, ProdBag_benumerate, ProdBag_binsert.
    intros inserted container [repA [repB repP] ]; simpl.
    eapply binsert_enumerate; eauto.
  Qed.

  Lemma ProdBag_BagCountCorrect :
    BagCountCorrect ProdBag_RepInv ProdBag_bcount ProdBag_bfind.
  Proof.
    unfold ProdBag_bcount, ProdBag_bfind, BagCountCorrect.
    intros container st [repA [repB repP] ].
    destruct Prod_st_choice; eapply bcount_correct; eauto.
  Qed.

  Lemma ProdBag_BagEnumerateEmpty :
    BagEnumerateEmpty ProdBag_benumerate ProdBag_bempty.
  Proof.
    unfold ProdBag_benumerate, BagEnumerateEmpty.
    eapply benumerate_empty.
  Qed.

  Lemma ProdBag_BagFindCorrect :
    BagFindCorrect ProdBag_RepInv ProdBag_bfind ProdBag_bfind_matcher ProdBag_benumerate.
  Proof.
    unfold ProdBag_bfind, ProdBag_benumerate, ProdBag_bfind_matcher, BagFindCorrect.
    intros container st [repA [repB repP] ].
    destruct Prod_st_choice. eapply bfind_correct; eauto.
    setoid_rewrite repP. eapply bfind_correct; eauto.
  Qed.

  Lemma ProdBag_BagMatcherEquiv :
    forall st i, ProdBag_bfind_matcher st i = bfind_matcher Prod_st_A i.
  Proof.
    intros st i; unfold ProdBag_bfind_matcher.
    destruct Prod_st_choice; try rewrite Prod_st_proof; eauto.
  Qed.

  Lemma ProdBag_BagDeleteCorrect :
    BagDeleteCorrect ProdBag_RepInv ProdBag_bfind ProdBag_bfind_matcher
                     ProdBag_benumerate ProdBag_bdelete.
  Proof.
    unfold ProdBag_benumerate, ProdBag_bfind_matcher, ProdBag_bdelete, ProdBag_bfind;
    hnf; intros container st [repA [repB repP] ];
    rewrite surjective_pairing with (p:=bdelete (fst container) Prod_st_A);
    rewrite surjective_pairing with (p:=bdelete (snd container) Prod_st_B); split.
    - rewrite ListFacts.partition_filter_neq; eapply perm_trans.
      + destruct Prod_st_choice; eapply bdelete_correct; eauto.
      + eapply perm_trans; [ |
        eapply ListMorphisms.filter_permutation_morphism; try eapply Permutation_refl;
        unfold Morphisms.pointwise_relation; intro a;
        pose proof (ProdBag_BagMatcherEquiv st a); unfold ProdBag_bfind_matcher in H; rewrite H;
        reflexivity ].
        rewrite <- ListFacts.partition_filter_neq; reflexivity.
    - destruct Prod_st_choice; try eapply bdelete_correct; eauto.
      simpl; eapply perm_trans; try eapply bdelete_correct; eauto.
      rewrite !ListFacts.partition_filter_eq.
      rewrite repP; reflexivity.
  Qed.

  Lemma ProdBag_BagUpdateCorrect :
    BagUpdateCorrect ProdBag_RepInv ProdBag_ValidUpdate
                     ProdBag_bfind ProdBag_bfind_matcher
                     ProdBag_benumerate ProdBag_bupdate_transform ProdBag_bupdate.
  Proof.
    unfold ProdBag_benumerate, ProdBag_bfind_matcher, ProdBag_bupdate, ProdBag_bfind, ProdBag_bupdate_transform;
    hnf; intros container st ut [repA [repB repP] ] [valA [valB valP] ].
    rewrite surjective_pairing with (p:=bupdate (fst container) Prod_st_A ut);
    rewrite surjective_pairing with (p:=bupdate (snd container) Prod_st_B ut); split.
    - rewrite ListFacts.partition_filter_neq; eapply perm_trans.
      + destruct Prod_st_choice; eapply bupdate_correct; eauto.
      + eapply Permutation_app.
        * eapply perm_trans; [ |
          eapply ListMorphisms.filter_permutation_morphism; try eapply Permutation_refl;
          unfold Morphisms.pointwise_relation; intro a;
          pose proof (ProdBag_BagMatcherEquiv st a); unfold ProdBag_bfind_matcher in H; rewrite H;
          reflexivity ]. rewrite <- ListFacts.partition_filter_neq; reflexivity.
        * eapply ListMorphisms.map_permutation_morphism; try reflexivity.
          rewrite !ListFacts.partition_filter_eq.
          destruct Prod_st_choice; try reflexivity.
          eapply ListMorphisms.filter_permutation_morphism; try reflexivity.
          intro; eapply Prod_st_proof.
    - destruct Prod_st_choice; try eapply bupdate_correct; eauto.
      simpl; eapply perm_trans; try eapply bupdate_correct; eauto.
      rewrite !ListFacts.partition_filter_eq.
      rewrite repP; reflexivity.
  Qed.

  Global Instance ProdBagAsBag
  : Bag ProdBag TItem ProdSearchTerm TUpdateTerm :=
    {| bempty            := ProdBag_bempty;
       bfind_matcher     := ProdBag_bfind_matcher;
       bupdate_transform := ProdBag_bupdate_transform;

       benumerate := ProdBag_benumerate;
       bfind      := ProdBag_bfind;
       binsert    := ProdBag_binsert;
       bcount     := ProdBag_bcount;
       bdelete    := ProdBag_bdelete;
       bupdate    := ProdBag_bupdate |}.

  Global Instance ProdBagAsCorrectBag
  : CorrectBag ProdBag_RepInv
               ProdBag_ValidUpdate
               ProdBagAsBag :=
    {| bempty_RepInv     := ProdBag_Empty_RepInv;
       binsert_RepInv    := ProdBag_binsert_Preserves_RepInv;
       bdelete_RepInv    := ProdBag_bdelete_Preserves_RepInv;
       bupdate_RepInv    := ProdBag_bupdate_Preserves_RepInv;

       binsert_enumerate := ProdBag_BagInsertEnumerate;
       benumerate_empty  := ProdBag_BagEnumerateEmpty;
       bfind_correct     := ProdBag_BagFindCorrect;
       bcount_correct    := ProdBag_BagCountCorrect;
       bdelete_correct   := ProdBag_BagDeleteCorrect;
       bupdate_correct   := ProdBag_BagUpdateCorrect |}.

End ProductBag.
