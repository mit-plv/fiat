Require Export Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsInterface Fiat.QueryStructure.Refinements.Bags.CountingListBags Fiat.QueryStructure.Refinements.Bags.TreeBags Fiat.QueryStructure.Specification.Representation.Tuple Fiat.QueryStructure.Specification.Representation.Heading Coq.Lists.List Coq.Program.Program Fiat.Common.ilist Fiat.Common.i2list.
Require Import Fiat.Common.String_as_OT Fiat.Common.Ensembles.IndexedEnsembles Fiat.Common.DecideableEnsembles.
Require Import Coq.Bool.Bool Coq.Strings.String Coq.Structures.OrderedTypeEx Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsOfTuples.
Require Import Fiat.QueryStructure.Implementation.Operations.General.QueryRefinements.
Require Import Fiat.QueryStructure.Specification.Representation.QueryStructureNotations Fiat.QueryStructure.Implementation.DataStructures.ListImplementation.
Require Import Fiat.QueryStructure.AdditionalLemmas Fiat.Common.List.PermutationFacts Fiat.ADT.ComputationalADT Coq.Arith.Arith Fiat.QueryStructure.Refinements.BagADT.BagADT.

Section FiniteMapADT.

  Variable ValueType : Type.
  Variable KeyType : Type.

  Definition FiniteMapSig : ADTSig :=
    ADTsignature {
        Constructor "EmptyMap" : unit             -> rep,
        Method "Find"      : rep x KeyType   -> rep x option ValueType,
        Method "Enumerate" : rep x unit      -> rep x list (KeyType * ValueType),
        Method "Insert"    : rep x (KeyType * ValueType) -> rep x unit,
        Method "Delete"    : rep x KeyType   -> rep x list ValueType
  }.

(*  Definition FiniteMapSpec : ADT FiniteMapSig :=
    ADTRep (NodeType * ElementType -> Prop) {
        Def Constructor "Empty" (_ : unit) : rep :=
          ret (fun kv => None),

        Def Method "Find" (r : rep, key : NodeType)
          : list ElementType :=
            {value | r (key, value)},

        Def Method "Enumerate" (r : rep, f : unit)
          : list ElementType :=
              results <- {l | EnsembleIndexedListEquivalence r l};
        ret (r, map snd results),

        Def Method "Insert" (r : rep, kv : (KeyType * ValueType)) : unit :=
        ret (Add _ r {| elementIndex := freshIdx;
                        indexedElement := element |}, ()),

        Def Method "Count" (r : rep, f : NodeType) : nat :=
          results <- {l | EnsembleIndexedListEquivalence r l};
        ret (r, length (filter (SearchTermMatcher f) results)),

        Def Method "Delete" (r : rep, f : NodeType)
        : list ElementType :=
          deleted <- {l | EnsembleIndexedListEquivalence r l};
          ret (EnsembleDelete
                 r
                 (fun tup =>  f tup = true),
               filter (SearchTermMatcher f) deleted)

           }. *)

End FiniteMapADT.

Section ListADT.

  Variable ValueType : Type.

  Definition ListSig : ADTSig :=
    ADTsignature {
        Constructor "EmptyList" : unit             -> rep,
        Method "Enumerate"      : rep x unit       -> rep x list ValueType,
        Method "Insert"         : rep x ValueType -> rep x unit,
        Method "Delete"         : rep x (ValueType -> bool) -> rep x list ValueType
  }.

(*  Definition FiniteMapSpec : ADT FiniteMapSig :=
    ADTRep (NodeType * ElementType -> Prop) {
        Def Constructor "Empty" (_ : unit) : rep :=
          ret (fun kv => None),

        Def Method "Find" (r : rep, key : NodeType)
          : list ElementType :=
            {value | r (key, value)},

        Def Method "Enumerate" (r : rep, f : unit)
          : list ElementType :=
              results <- {l | EnsembleIndexedListEquivalence r l};
        ret (r, map snd results),

        Def Method "Insert" (r : rep, kv : (KeyType * ValueType)) : unit :=
        ret (Add _ r {| elementIndex := freshIdx;
                        indexedElement := element |}, ()),

        Def Method "Count" (r : rep, f : NodeType) : nat :=
          results <- {l | EnsembleIndexedListEquivalence r l};
        ret (r, length (filter (SearchTermMatcher f) results)),

        Def Method "Delete" (r : rep, f : NodeType)
        : list ElementType :=
          deleted <- {l | EnsembleIndexedListEquivalence r l};
          ret (EnsembleDelete
                 r
                 (fun tup =>  f tup = true),
               filter (SearchTermMatcher f) deleted)

           }. *)

End ListADT.

Section SharpenedBagImplementation.

  Context {heading : Heading}.

  Fixpoint BuildSearchTermTypeFromAttributes
           (Keys : list (@Attributes heading))
  : Type :=
    match Keys with
      | [] => (@Tuple heading -> bool)
      | Key :: Keys' => prod (option (Domain heading Key))
                                (BuildSearchTermTypeFromAttributes Keys')
    end.

Definition packagedADT (Sig : ADTSig) :=
  {Rep : Type & prod Rep
              (pcADT Sig Rep)
  }.

  Fixpoint BuildcADTSignaturesFromAttributes
           (Keys : list (@Attributes heading))
  : list ADTSig :=
    match Keys with
      | [] => [ListSig (@Tuple heading)]
      | Key :: Keys' =>
        @FiniteMapSig
          (packagedADT (BagSig (@Tuple heading) (BuildSearchTermTypeFromAttributes Keys')))
          (Domain heading Key)
          :: BuildcADTSignaturesFromAttributes Keys'
    end.

  Fixpoint BuildDelegateSignatureFromAttributes
           (Keys : list (@Attributes heading))
  : ADTSig :=
    match Keys with
      | [] => ListSig (@Tuple heading)
      | Key :: Keys' =>
        @FiniteMapSig
          (packagedADT (BuildDelegateSignatureFromAttributes Keys'))
          (Domain heading Key)
    end.

  Fixpoint BuildDelegateSignaturesFromAttributes
           (Keys : list (@Attributes heading))
  : list ADTSig :=
    match Keys with
      | [] => [ListSig (@Tuple heading)]
      | Key :: Keys' =>
        BuildDelegateSignatureFromAttributes
          (Key :: Keys')
          :: BuildDelegateSignaturesFromAttributes Keys'
    end.

  Definition UnIndexedBagcADT
             (ListADTImpl : cADT (ListSig (@Tuple heading)))
  : cADT (BagSig (@Tuple heading) (@Tuple heading -> bool))
    :=
    cADTRep (cRep ListADTImpl) {
        Def Constructor "Empty" (u : unit) : rep :=
          CallConstructor ListADTImpl "EmptyList" (),

        Def Method "Find" (r : rep, filt : Tuple -> bool)
          : list (@Tuple heading) :=

            let (r', results) := (CallMethod ListADTImpl "Enumerate" r ()) in
            (r', filter filt results),

        Def Method "Enumerate" (r : rep, f : unit)
          : list (@Tuple heading) :=
              CallMethod ListADTImpl "Enumerate" r (),

        Def Method "Insert" (r : rep, element : Tuple) : unit :=
                CallMethod ListADTImpl "Insert" r element,

        Def Method "Count" (r : rep, filt : Tuple -> bool)
                : nat :=
            let (r', results) := (CallMethod ListADTImpl "Enumerate" r ()) in
            (r', fold_right (fun tup count =>
                               if filt tup then S count else count)
                            0 results),

        Def Method "Delete" (r : rep, filt : Tuple -> bool)
        : list (@Tuple heading) :=
              CallMethod ListADTImpl "Delete" r filt
            }.

  Definition AttributeToIndexedBagcADT
             (Key : Attributes heading)
             SubTreeSearchTermType
             (NodeImpl : cADT (FiniteMapSig (packagedADT (BagSig (@Tuple heading) SubTreeSearchTermType))
                                            (Domain heading Key)))

             (SubTreeImpl : cADT (BagSig (@Tuple heading) SubTreeSearchTermType))
  : cADT (@BagSig (@Tuple heading) (option (Domain heading Key) * SubTreeSearchTermType)).
  Admitted.
(*    refine (cADTRep (cRep NodeImpl) {
        Def Constructor "Empty" (u : unit) : rep :=
          CallConstructor NodeImpl "EmptyMap" u,

        Def Method "Find" (r : rep, indices : option (Domain heading Key) * SubTreeSearchTermType)
          : list (@Tuple heading) :=
                match indices with
                  | (Some index, indices') =>
                    match CallMethod NodeImpl "Find" r index with
                      | (r', Some subtree) =>
                        let results := @CallPackagedADTMethod
                                         (BagSig Tuple SubTreeSearchTermType)
                                         {|bindex := "Find" |} indices' subtree in
                        (fst (CallMethod NodeImpl "Insert" r' (index, fst results)), snd results)
                      | (r', None) => (r', [])
                    end
                  | (None, indices') =>
                    let results := CallMethod NodeImpl "Enumerate" r () in
                    fold_right
                      (fun (subtree : _ * packagedADT (BagSig Tuple SubTreeSearchTermType))
                           (items : cRep NodeImpl * list Tuple) =>
                         let (r, elts) := items in
                         let result := @CallPackagedADTMethod
                                         (BagSig Tuple SubTreeSearchTermType)
                                         {|bindex := "Find" |} indices' (snd subtree) in
                         (fst (CallMethod NodeImpl "Insert" r (fst subtree, fst result)),
                          app (snd result) elts))
                    (fst results, []) (snd results)
            end,

        Def Method "Enumerate" (r : rep, f : unit)
          : list (@Tuple heading) :=
              let results := CallMethod NodeImpl "Enumerate" r () in
              fold_right
                (fun (subtree : _ * packagedADT (BagSig Tuple SubTreeSearchTermType))
                     (items : cRep NodeImpl * list Tuple) =>
                   let (r, elts) := items in
                   let result := @CallPackagedADTMethod
                                         (BagSig Tuple SubTreeSearchTermType)
                                         {|bindex := "Enumerate" |}
                                         () (snd subtree) in
                   (fst (CallMethod NodeImpl "Insert" r (fst subtree, fst result)),
                    app (snd result) elts))
                (fst results, []) (snd results),


        Def Method "Insert" (r : rep, element : @Tuple heading) : unit :=
                match CallMethod NodeImpl "Find" r (element Key) with
                  | (r', Some subtree) =>
                    let result := @CallPackagedADTMethod
                                    (BagSig Tuple SubTreeSearchTermType)
                                    {|bindex := "Insert" |}
                                    element subtree in
                    CallMethod NodeImpl "Insert" r' (element Key, fst result)
                  | (r', None) =>
                    let new_subtree :=
                        (snd (projT2 SubTreeImpl)) {|bindex := "Insert" |}
                                  (fst (projT2 SubTreeImpl) {|bindex := "Empty" |} ())
                                  element in
                    (fst (CallMethod NodeImpl "Insert" r'
                                     (element Key, existT _ (projT1 SubTreeImpl)
                                                          (fst new_subtree,
                                                           projT2 SubTreeImpl))), ())
                end,

        Def Method "Count" (r : rep, indices : option (Domain heading Key) * SubTreeSearchTermType)
                : nat :=
                match indices with
                  | (Some index, indices') =>
                    match CallMethod NodeImpl "Find" r index with
                      | (r', Some subtree) =>
                        let results := @CallPackagedADTMethod
                                         (BagSig Tuple SubTreeSearchTermType)
                                         {|bindex := "Count" |}
                                         indices' subtree in
                        (fst (CallMethod NodeImpl "Insert" r' (index, fst results)), snd results)
                      | (r', None) => (r', 0)
                    end
                  | (None, indices') =>
                    let results := CallMethod NodeImpl "Enumerate" r () in
                    fold_right
                      (fun (subtree : _ * packagedADT (BagSig Tuple SubTreeSearchTermType))
                           (items : cRep NodeImpl * nat) =>
                         let (r, elts) := items in
                         let result := @CallPackagedADTMethod
                                         (BagSig Tuple SubTreeSearchTermType)
                                         {|bindex := "Count" |}
                                         indices' (snd subtree) in
                         (fst (CallMethod NodeImpl "Insert" r (fst subtree, fst result)),
                          (snd result) + elts))
                    (fst results, 0) (snd results)
            end,

        Def Method "Delete" (r : rep, indices : option (Domain heading Key) * SubTreeSearchTermType)
        : list (@Tuple heading) :=
                match indices with
                  | (Some index, indices') =>
                    match CallMethod NodeImpl "Find" r index with
                      | (r', Some subtree) =>
                        let results := @CallPackagedADTMethod
                                         (BagSig Tuple SubTreeSearchTermType)
                                         {|bindex := "Delete" |}
                                         indices' subtree in
                        (fst (CallMethod NodeImpl "Insert" r' (index, fst results)), snd results)
                      | (r', None) => (r', [])
                    end
                  | (None, indices') =>
                    let results := CallMethod NodeImpl "Enumerate" r () in
                    fold_right
                      (fun (subtree : _ * packagedADT (BagSig Tuple SubTreeSearchTermType))
                           (items : cRep NodeImpl * list Tuple) =>
                         let (r, elts) := items in
                         let result := @CallPackagedADTMethod
                                         (BagSig Tuple SubTreeSearchTermType)
                                         {|bindex := "Delete" |}
                                         indices' (snd subtree) in
                         (fst (CallMethod NodeImpl "Insert" r (fst subtree, fst result)),
                          app (snd result) elts))
                    (fst results, []) (snd results)
            end

           }).
    Defined.*)

  Fixpoint NestedTreeFromAttributesAsBagcADT
          (Keys : list (@Attributes heading))
 : ilist (fun Sig => cADT Sig) (BuildDelegateSignaturesFromAttributes Keys) ->
   cADT (@BagSig (@Tuple heading) (BuildSearchTermTypeFromAttributes Keys)) :=
  match Keys return
         ilist cADT (BuildDelegateSignaturesFromAttributes Keys) ->
         cADT (@BagSig (@Tuple heading) (BuildSearchTermTypeFromAttributes Keys))
   with
     | [] => fun Impl => UnIndexedBagcADT (ilist_hd Impl)
     | Key :: Keys' =>
       fun SubTreeImpl =>
         @AttributeToIndexedBagcADT
           Key _
           (ilist_hd SubTreeImpl)
           (NestedTreeFromAttributesAsBagcADT Keys' (ilist_tl SubTreeImpl))
   end.

  Fixpoint ilistBagFromilistFMap
           (Keys : ilist (@Attributes heading))
  : ilist (fun Sig => cADT Sig) (BuildcADTSignaturesFromAttributes Keys)




  Variable SearchTermTypePlus : Type.
  Variable UpdateTermTypePlus : Type.
  Variable BagTypePlus : Type.
  Variable RepInvPlus : BagTypePlus -> Prop.
  Variable ValidUpdatePlus : UpdateTermTypePlus -> Prop.

  Variable BagPlus : Bag BagTypePlus (@Tuple heading) SearchTermTypePlus UpdateTermTypePlus.
  Variable CorrectBagPlus : CorrectBag RepInvPlus ValidUpdatePlus BagPlus.

  Lemma refine_Empty_set_bempty :
    Empty_set IndexedElement ≃ benumerate bempty.
  Proof.
    split.
    - exists 1; unfold UnConstrFreshIdx; intros elements H; destruct H.
    - eexists nil; simpl; intuition.
      + erewrite benumerate_empty_eq_nil by eauto; reflexivity.
      + repeat constructor; simpl; intros; intuition.
        unfold In in H; destruct H.
  Qed.

  Lemma refine_Add_binsert
  : forall or nr iel,
      or ≃ benumerate nr
      -> UnConstrFreshIdx or (elementIndex iel)
      -> RepInvPlus nr
      -> Add IndexedElement or iel ≃ benumerate (binsert nr (indexedElement iel)).
  Proof.
    simpl; intros; destruct_EnsembleIndexedListEquivalence; clear H.
    split.
    - exists (S (elementIndex iel) ).
      unfold UnConstrFreshIdx, Add in *; intros.
      inversion H; subst; unfold In in *.
      + apply H0 in H2; auto with arith.
      + inversion H2; subst; auto with arith.
    - destruct (permutation_map_cons
                    indexedElement
                    (binsert_enumerate (indexedElement iel) nr H1)
                    iel lor eq_refl eqv_or)
        as [lor' (eqv_lor' & perm_lor') ].
      exists lor'; intuition; eauto.
      split; intuition.
      + setoid_rewrite NoDup_modulo_permutation; eexists (_ :: _); intuition; eauto.
        constructor; eauto.
        setoid_rewrite <- eqv_nr; unfold not; intros.
        unfold In in *; apply H0 in H; exfalso; omega.
      + unfold In, Add in *; eapply Permutation_in;
          [ symmetry; eassumption
          | simpl; rewrite <- eqv_nr; inversion H; subst; intuition;
            unfold In in *; inversion H2; subst; eauto].
      + eapply Permutation_in in H; eauto; simpl in *; intuition.
        * constructor 2; subst; constructor.
        * constructor; rewrite eqv_nr; eauto.
  Qed.

  Lemma refine_Delete_bdelete
  : forall or nr search_term,
      or ≃ benumerate nr
      -> RepInvPlus nr
      -> EnsembleDelete or (fun tup => bfind_matcher search_term tup = true) ≃
                        benumerate (snd (bdelete nr search_term)).
  Proof.
    simpl; intros; destruct_EnsembleIndexedListEquivalence; clear H.
    split.
    - exists bnd; unfold UnConstrFreshIdx in *; intros; apply fresh_bnd;
    destruct H; eauto.
    - pose proof (bdelete_correct nr search_term H0); intuition.
      rewrite partition_filter_neq in H1; symmetry in H1.
      destruct (permutation_filter _ _ _ H1) as [l [l_eq Perm_l]].
      symmetry in Perm_l.
      destruct (permutation_map_base indexedElement Perm_l _ eqv_or)
               as [l' [l'_eq Perm_l']].
      exists (filter (fun a => negb (bfind_matcher search_term (indexedElement a))) l'); repeat split.
      + rewrite <- l_eq, <- l'_eq, filter_map; reflexivity.
      + apply NoDupFilter; eapply NoDup_Permutation_rewrite.
          symmetry; eauto.
          eauto.
      + unfold In, EnsembleDelete; intros.
        inversion H; subst.
        unfold In, Complement, In in *.
        rewrite <- partition_filter_neq.
        rewrite <- partition_filter_neq in l_eq.
        rewrite eqv_nr in H3.
        rewrite (In_partition (fun itup => bfind_matcher search_term (indexedElement itup))) in H3; intuition.
        rewrite partition_filter_eq, filter_In in H5; intuition.
        rewrite partition_filter_neq, filter_In in H5;
          rewrite partition_filter_neq, filter_In; intuition.
        symmetry in Perm_l'; eapply Permutation_in; eauto.
      + unfold In, EnsembleDelete; intros.
        rewrite filter_In in H; intuition.
        apply eqv_nr; eapply Permutation_in; eauto.
      + unfold In, Complement, In in *.
        rewrite filter_In in H; intuition.
        rewrite H3 in H5; discriminate.
  Qed.

  Definition SharpenedBagImpl
  : Sharpened (@BagSpec (@Tuple heading) SearchTermTypePlus
                        bfind_matcher).
  Proof.
    unfold BagSpec.
    hone representation using
         (fun r_o r_n =>
            r_o ≃ benumerate (Bag := BagPlus) r_n
            /\ RepInvPlus r_n).
    hone constructor "Empty".
    {
      simplify with monad laws.
      refine pick val bempty.
      finish honing.
      intuition eauto using bempty_RepInv; eapply refine_Empty_set_bempty.
    }

    hone method "Enumerate".
    {
      simplify with monad laws.
      refine pick val (benumerate r_n); intuition;
      simplify with monad laws; simpl.
      refine pick val r_n; intuition;
      simplify with monad laws; simpl.
      finish honing.
    }

    hone method "Count".
    {
      simplify with monad laws.
      refine pick val (benumerate r_n); intuition;
      simplify with monad laws; simpl.
      refine pick val r_n; intuition;
      simplify with monad laws; simpl.
      erewrite Permutation_length
        by (rewrite bfind_correct; eauto; reflexivity).
      rewrite bcount_correct; eauto.
      finish honing.
    }

    hone method "Insert".
    {
      simplify with monad laws; intuition.
      destruct_EnsembleIndexedListEquivalence.
      refine pick val bnd; eauto; simplify with monad laws.
      simpl; refine pick val (binsert r_n n).
      simplify with monad laws.
      finish honing.
      split; eauto using binsert_RepInv.
      eapply refine_Add_binsert; simpl; eauto.
    }

    hone method "Find".
    {
      simplify with monad laws.
      intuition.
      pose proof (bfind_correct r_n n H2).
      destruct (permutation_filter _ _ _ (bfind_correct r_n n H2)) as [l [l_eq Perm_l]].
      refine pick val l.
      simplify with monad laws; simpl.
      refine pick val r_n; eauto.
      simplify with monad laws; simpl.
      rewrite l_eq.
      finish honing.
      eapply Permutation_EnsembleIndexedListEquivalence; simpl; eauto.
    }

    hone method "Delete".
    {
      simplify with monad laws; intuition.
      destruct (bdelete_correct r_n n H2).
      rewrite partition_filter_eq in H3.
      rewrite partition_filter_neq in H0.
      symmetry in H0; symmetry in H3.
      destruct (permutation_filter _ _ _ H0) as [l [l_eq Perm_l]].
      destruct (permutation_filter _ _ _ H3) as [l' [l'_eq Perm_l']].
      refine pick val l'.
      simplify with monad laws; simpl.
      refine pick val (snd (bdelete r_n n)).
      simplify with monad laws; simpl.
      rewrite l'_eq.
      finish honing.
      intuition auto using bdelete_RepInv.
      eapply refine_Delete_bdelete; simpl; eauto.
      eapply Permutation_EnsembleIndexedListEquivalence; simpl; eauto.
    }

    Admitted.

  (*FullySharpenEachMethod (@nil ADTSig) (inil ADT); simpl.

  Defined.

  Definition BagADTImpl : ComputationalADT.cADT (BagSig (@Tuple heading) SearchTermTypePlus).
    extract implementation of SharpenedBagImpl using (inil _).
  Defined. *)

End SharpenedBagImplementation.
