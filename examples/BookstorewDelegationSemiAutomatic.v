Require Import AutoDB BagADT.

(* Our bookstore has two relations (tables):
   - The [Books] relation contains the books in the
     inventory, represented as a tuple with
     [Author], [Title], and [ISBN] attributes.
     The [ISBN] attribute is a key for the relation,
     specified by the [where attributes .. depend on ..]
     constraint.
   - The [Orders] relation contains the orders that
     have been placed, represented as a tuple with the
     [ISBN] and [Date] attributes.

   The schema for the entire query structure specifies that
   the [ISBN] attribute of [Orders] is a foreign key into
   [Books], specified by the [attribute .. of .. references ..]
   constraint.
 *)

(* Let's define some synonyms for strings we'll need,
 * to save on type-checking time. *)
Definition sBOOKS := "Books".
Definition sAUTHOR := "Authors".
Definition sTITLE := "Title".
Definition sISBN := "ISBN".
Definition sORDERS := "Orders".
Definition sDATE := "Date".

(* Now here's the actual schema, in the usual sense. *)

Definition BookStoreSchema :=
  Query Structure Schema
    [ relation sBOOKS has
              schema <sAUTHOR :: string,
                      sTITLE :: string,
                      sISBN :: nat>
                      where attributes [sTITLE; sAUTHOR] depend on [sISBN];
      relation sORDERS has
              schema <sISBN :: nat,
                      sDATE :: nat> ]
    enforcing [attribute sISBN for sORDERS references sBOOKS].

(* Aliases for the tuples contained in Books and Orders, respectively. *)
Definition Book := TupleDef BookStoreSchema sBOOKS.
Definition Order := TupleDef BookStoreSchema sORDERS.

(* Our bookstore has two mutators:
   - [PlaceOrder] : Place an order into the 'Orders' table
   - [AddBook] : Add a book to the inventory

   Our bookstore has two observers:
   - [GetTitles] : The titles of books written by a given author
   - [NumOrders] : The number of orders for a given author
 *)

(* So, first let's give the type signatures of the methods. *)
Definition BookStoreSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,
      (* Method "PlaceOrder" : rep x Order -> rep x bool, *)
      Method "DeleteOrder" : rep x nat -> rep x list Order,
      (* Method "AddBook" : rep x Book -> rep x bool, *)
      (* Method "DeleteBook" : rep x nat -> rep x list Book, *)
      Method "GetTitles" : rep x string -> rep x list string
      (* Method "NumOrders" : rep x string -> rep x nat *)
    }.

(* Now we write what the methods should actually do. *)

Definition BookStoreSpec : ADT BookStoreSig :=
  QueryADTRep BookStoreSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    (*update "PlaceOrder" ( o : Order ) : bool :=
        Insert o into sORDERS, *)

    update "DeleteOrder" ( oid : nat ) : list Order :=
        Delete o from sORDERS where o!sISBN = oid ,

    (*update "AddBook" ( b : Book ) : bool :=
        Insert b into sBOOKS , *)

    (* update "DeleteBook" ( id : nat ) : list Book :=
        Delete book from sBOOKS where book!sISBN = id , *)

    query "GetTitles" ( author : string ) : list string :=
      For (b in sBOOKS)
      Where (author = b!sAUTHOR)
      Return (b!sTITLE)

      (* query "NumOrders" ( author : string ) : nat :=
        Count (For (o in sORDERS) (b in sBOOKS)
               Where (author = b!sAUTHOR)
               Where (b!sISBN = o!sISBN)
               Return ()) *)
}.

(* Aliases for internal names of the two tables *)
Definition Books := GetRelationKey BookStoreSchema sBOOKS.
Definition Orders := GetRelationKey BookStoreSchema sORDERS.

(* Aliases for internal notions of schemas for the two tables *)
Definition BookSchema := QSGetNRelSchemaHeading BookStoreSchema Books.
Definition OrderSchema := QSGetNRelSchemaHeading BookStoreSchema Orders.

(* Now we define an index structure (delegate) for each table. *)

Definition OrderSearchTerm : list (@ProperAttribute OrderSchema).
  set (src := [ OrderSchema/sISBN  ]);
  autoconvert (@CheckType OrderSchema).
Defined.

Definition OrderSearchTermMatcher :=
  SearchTermFromAttributesMatcher OrderSearchTerm.

Definition BookSearchTerm : list (@ProperAttribute BookSchema).
  set (src := [ BookSchema/sAUTHOR; BookSchema/sISBN ]);
  autoconvert (@CheckType BookSchema).
Defined.

Definition BookSearchTermMatcher :=
  SearchTermFromAttributesMatcher BookSearchTerm.

Definition BookStorageDelegate := BagSpec BookSearchTermMatcher.
Definition OrderStorageDelegate := BagSpec OrderSearchTermMatcher.

(* In other words, index first on the author field, then the ISBN field.
 * Works especially efficiently for accesses keyed on author. *)

Definition BookStoreIndices :
  ilist (fun ns : NamedSchema => list (@ProperAttribute (schemaHeading (relSchema ns))))
        (qschemaSchemas BookStoreSchema) :=
  icons _ BookSearchTerm (icons _ OrderSearchTerm (inil _)).

Require Import BagsofTuplesADT.

Definition BookStore_AbsR := (@DelegateToBag_AbsR _ BookStoreIndices).

(* Lemma BookstorewDelegates_AbsR_Pick :
  forall (qs_schema : QueryStructureSchema)
         indices
         (r_o : UnConstrQueryStructure qs_schema)
         (r_n : IndexedQueryStructure qs_schema indices),
    refineEquiv {r_n' | DelegateToBag_AbsR (r_o) r_n} (ret r_o).
Proof.
  intros r_o; split; intros v Comp_v;
  inversion_by computes_to_inv; subst; unfold BookstorewDelegates_AbsR in *.
  constructor; eauto.
  erewrite ilist_eq;
    [constructor | eauto].
Qed. *)

Opaque CallBagMethod.

Theorem BookStoreManual :
  Sharpened BookStoreSpec.
Proof.

  unfold BookStoreSpec.

  (* First, we unfold various definitions and drop constraints *)
  start honing QueryStructure.

  hone representation using BookStore_AbsR.

  hone constructor "Init". {
    simplify with monad laws.
    rewrite refine_QSEmptySpec_Initialize_IndexedQueryStructure.
    simpl; simplify with monad laws.
    finish honing.
  }

  hone method "DeleteOrder". {
    startMethod BookStore_AbsR.

    match goal with
        [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
          |- context[Pick (QSDeletedTuples ?r_o ?idx ?DeletedTuples)] ] =>
        let dec := constr:(@DecideableEnsembles.dec _ DeletedTuples _) in
        let storage := eval simpl in (ith_Bounded relName indices idx) in
        let fs := fields storage in
        match type of fs with
        | list (@Attributes ?SC) =>
          findGoodTerm SC dec ltac:(fun fds tail =>
            let tail := eval simpl in tail in
              makeTerm storage fs SC fds tail
              ltac:(fun tm =>
                      rewrite (@refine_BagADT_QSDelete_fst _ _ r_o r_n H idx DeletedTuples _ tm)
                              by prove_extensional_eq))
      end
    end.

    simplify with monad laws; cbv beta; simpl.

    match goal with
        [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
          |- context[{r_n' | DelegateToBag_AbsR
                               (UpdateUnConstrRelation ?r_o ?idx
                                                       (EnsembleDelete (GetUnConstrRelation ?r_o ?idx)
                                                                       ?DeletedTuples)) r_n'}]] =>
        let dec := constr:(@DecideableEnsembles.dec _ DeletedTuples _) in
        let storage := eval simpl in (ith_Bounded relName indices idx) in
        let fs := fields storage in
        match type of fs with
        | list (@Attributes ?SC) =>
          findGoodTerm SC dec ltac:(fun fds tail =>
            let tail := eval simpl in tail in
              makeTerm storage fs SC fds tail
              ltac:(fun tm =>
                      let Eqv := fresh in
                      assert (ExtensionalEq (@DecideableEnsembles.dec (@Tuple SC) DeletedTuples _)
                                            (SearchTermFromAttributesMatcher storage tm))
                        as Eqv by prove_extensional_eq;
                      setoid_rewrite (@refine_BagADT_QSDelete_snd _ _ r_o r_n H idx DeletedTuples _ tm Eqv);
                      clear Eqv))
      end
    end.
    simplify with monad laws; cbv beta; simpl.

    finish honing.

  }

   hone method "GetTitles". {
    startMethod BookStore_AbsR.

    setoid_rewrite refine_Query_In_Enumerate; eauto.
    setoid_rewrite refine_List_Query_In_Where.

    match goal with
        [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
          |- context[For (l <- CallBagMethod ?idx {| bindex := "Enumerate"|} ?r_n0 ();
                          List_Query_In (filter (@DecideableEnsembles.dec _ ?DeletedTuples _) (snd l))
                                        ?resultComp)]] =>
        let dec := constr:(@DecideableEnsembles.dec _ DeletedTuples _) in
        let storage := eval simpl in (ith_Bounded relName indices idx) in
        let fs := fields storage in
        match type of fs with
        | list (@Attributes ?SC) =>
          findGoodTerm SC dec ltac:(fun fds tail =>
            let tail := eval simpl in tail in
              makeTerm storage fs SC fds tail
                       ltac:(fun tm =>
                               setoid_rewrite (@refine_Query_For_In_Find _ _ string _ _ H idx dec tm resultComp);
                      [ | prove_extensional_eq]
                    ))
      end
    end.
    simplify with monad laws.
    setoid_rewrite ListQueryRefinements.refine_List_Query_In_Return; simplify with monad laws.
    simpl.
    setoid_rewrite (refine_pick_val _ H0); simplify with monad laws.
    finish honing.
  }

  unfold cast, eq_rect_r, eq_rect, eq_sym; simpl.

  (* At this point our implementation is fully computational: we're done! *)

  Require Import ADTNotation.BuildComputationalADT.
  Require Import ADT.ComputationalADT.

  Ltac FullySharpenEachMethod delegateSigs delegateSpecs cRep' cAbsR' :=
    match goal with
        |- Sharpened (@BuildADT ?Rep ?consSigs ?methSigs ?consDefs ?methDefs) =>
        ilist_of_evar
          (ilist ComputationalADT.cADT delegateSigs)
          (fun DelegateImpl Sig => cMethodType (cRep' DelegateImpl) (methDom Sig) (methCod Sig))
          methSigs
          ltac:(fun cMeths => ilist_of_evar
                                (ilist ComputationalADT.cADT delegateSigs)
                                (fun DelegateImpl Sig =>
                                   cConstructorType (cRep' DelegateImpl) (consDom Sig))
                                consSigs
                                ltac:(fun cCons =>
                                        eapply Notation_Friendly_SharpenFully with
                                        (DelegateSpecs := delegateSpecs)
                                          (cConstructors := cCons)
                                          (cMethods := cMeths)
                                          (cAbsR := cAbsR')));
          unfold Dep_Type_BoundedIndex_app_comm_cons
    end.

  FullySharpenEachMethod [BagSig Book (BuildSearchTermFromAttributes BookSearchTerm);
                           BagSig Order (BuildSearchTermFromAttributes OrderSearchTerm)]
                         (icons _ (BagSpec (SearchTermFromAttributesMatcher BookSearchTerm))
                         (icons _ (BagSpec (SearchTermFromAttributesMatcher OrderSearchTerm))
                                (inil ADT)))
                         (fun DelegateImpl : ilist cADT
                                                [BagSig Book (BuildSearchTermFromAttributes BookSearchTerm);
                                                  BagSig Order (BuildSearchTermFromAttributes OrderSearchTerm)] => prod (cRep (ilist_hd DelegateImpl)) (cRep (ilist_hd (ilist_tl DelegateImpl))))
                         (fun (DelegateImpl : ilist cADT
                                                [BagSig Book (BuildSearchTermFromAttributes BookSearchTerm);
                                                  BagSig Order (BuildSearchTermFromAttributes OrderSearchTerm)])
                              (ValidImpl :
                                 forall n, Dep_Option_elim_T2
                                             (fun Sig adt adt' => @refineADT Sig adt (LiftcADT adt'))
                                             (ith_error (icons _ (BagSpec (SearchTermFromAttributesMatcher BookSearchTerm))
                         (icons _ (BagSpec (SearchTermFromAttributesMatcher OrderSearchTerm))
                                (inil ADT))) n)
                                             (ith_error DelegateImpl n))
                        (r_o : IndexedQueryStructure BookStoreSchema BookStoreIndices)
                        r_n =>
                      AbsR (ValidImpl 0)
                           (GetIndexedRelation r_o {| bindex := sBOOKS |})
                           (fst r_n) /\
                      AbsR (ValidImpl 1)
                           (GetIndexedRelation r_o {| bindex := sORDERS |})
                           (snd r_n)).
    simpl; split;
    intros; unfold GetIndexedRelation, i2th_Bounded, ith_Bounded_rect; simpl.

  - simplify with monad laws; simpl.

  let H := fresh in
  pose proof (Iterate_Dep_Type_BoundedIndex_equiv_2 _ (ADTRefinementPreservesConstructors (ValidImpl 1))) as H; simpl in H; intuition.
  let H := fresh in
  pose proof (Iterate_Dep_Type_BoundedIndex_equiv_2 _ (ADTRefinementPreservesConstructors (ValidImpl 0))) as H; simpl in H; intuition.

  rewrite refineEquiv_pick_pair.
  assert (refine
            {r_n : cRep (ilist_hd (ilist_tl DelegateImpl)) |
             AbsR (ValidImpl 1) (Empty_set IndexedElement) r_n}
            (r_o' <- ret (Empty_set IndexedElement);
             {r_n : cRep (ilist_hd (ilist_tl DelegateImpl)) |
              AbsR (ValidImpl 1) r_o' r_n})) as H' by
      (setoid_rewrite refineEquiv_bind_unit; reflexivity);
    setoid_rewrite H'; setoid_rewrite (a d); clear H'.

  assert (refine
            {r_n : cRep (ilist_hd DelegateImpl) |
             AbsR (ValidImpl 0) (Empty_set IndexedElement) r_n}
            (r_o' <- ret (Empty_set IndexedElement);
             {r_n : cRep (ilist_hd DelegateImpl) |
              AbsR (ValidImpl 0) r_o' r_n})) as H' by
      (setoid_rewrite refineEquiv_bind_unit; reflexivity);
    setoid_rewrite H'; setoid_rewrite (a0 d); clear H'.

  simplify with monad laws.

  Ltac higher_order_2_reflexivity'' :=
    let x := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(x) end in
    let f := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(f) end in
    let a := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(a) end in
    let b := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(b) end in
    let x' := (eval pattern a, b in x) in
    let f' := match x' with ?f' _ _ => constr:(f') end in
    unify f f';
      cbv beta;
      solve [apply reflexivity].

  higher_order_2_reflexivity''.
  - constructor.
  - simpl; split; intros; intuition.
    let H := fresh in
    pose proof (Iterate_Dep_Type_BoundedIndex_equiv_2 _ (ADTRefinementPreservesMethods (ValidImpl 1))) as H.
    Opaque Methods.
    simpl Iterate_Dep_Type_BoundedIndex in H. intuition.
    simplify with monad laws.
    setoid_rewrite refineEquiv_pick_pair; simplify with monad laws.
    simpl.

    Lemma refineEquiv_duplicate_bind {A B : Type}
    : forall (c : Comp A) (k : A -> A -> Comp B),
        refine (a <- c; a' <- c; k a a')
               (a <- c; k a a).
    Proof.
      unfold refine; intros; inversion_by computes_to_inv;
      repeat (econstructor; eauto).
    Qed.

    rewrite refineEquiv_duplicate_bind.
    setoid_rewrite get_update_indexed_eq.
    Check get_update_indexed_neq.
    simpl in *|-*.
    match goal with
        |- context[GetIndexedRelation (UpdateIndexedRelation ?r ?idx _ ) ?idx'] =>
        assert (idx <> idx') as H' by
                                 (unfold not; intros; discriminate);
          setoid_rewrite (fun n => @get_update_indexed_neq _ _ r idx idx' n H')
    end.
    setoid_rewrite (refine_pick_val _ H0); simplify with monad laws.

    match goal with
        |- context [CallBagMethod _ _ _ ?d] => pose proof (a3 _ _ d H1)
    end.

    Eval cbv beta in (snd r_n) .
    pose (@refineCallMethod _ (BagSpec (SearchTermFromAttributesMatcher
                                          (ith_Bounded relName BookStoreIndices
                                                       (GetRelationKey BookStoreSchema sORDERS))))
                            (ilist_hd (ilist_tl DelegateImpl)) (ValidImpl 1)
                            {| bindex := "Delete" |} _ _ _ H).
    destruct_ex; intuition.
    rewrite H3.
    simplify with monad laws.
    rewrite H2.
    simplify with monad laws.
    simpl.
    destruct x.
    simpl in *.
    rewrite H4; simpl.
    higher_order_2_reflexivity''.

    Opaque Methods.

    let H := fresh in
    pose proof (Iterate_Dep_Type_BoundedIndex_equiv_2 _ (ADTRefinementPreservesMethods (ValidImpl 0))) as H.
    simpl Iterate_Dep_Type_BoundedIndex in H. intuition.
    simplify with monad laws.
    setoid_rewrite refineEquiv_pick_pair; simplify with monad laws.
    simpl.

    simpl in *|-*.

    match goal with
        |- context [CallBagMethod _ _ _ ?d] => pose proof (a0 _ _ d H0)
    end.

    pose (@refineCallMethod _ (BagSpec (SearchTermFromAttributesMatcher
                                          (ith_Bounded relName BookStoreIndices
                                                       (GetRelationKey BookStoreSchema sBOOKS))))
                            (ilist_hd DelegateImpl) (ValidImpl 0)
                            {| bindex := "Find" |} _ _ _ H).
    destruct_ex; intuition.
    rewrite H3.
    simplify with monad laws.
    refine pick val a.
    simplify with monad laws.
    refine pick val b.
    simplify with monad laws.
    destruct x.
    simpl in H4; rewrite H4.
    simpl.
    let x := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(x) end in
    let f := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(f) end in
    let a := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(a) end in
    let b := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(b) end in
    let b' := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(b') end in
    let c := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(c) end in
    let x' := (eval pattern a, b, b', c in x) in
    let f' := match x' with ?f' _ _ _ _ => constr:(fun i a => f' i (fst a) (snd a)) end in
    unify f f';
      cbv beta;
      solve [apply reflexivity].
    eauto.
    eauto.
Defined.

(*Definition BookStoreImpl : ComputationalADT.cADT BookStoreSig.
  extract implementation of BookStoreManual using (inil _).
Defined.

Print BookStoreImpl. *)
