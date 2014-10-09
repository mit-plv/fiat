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

    pose refine_Query_For_In_Find.

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

  Ltac FullySharpenEachMethod delegateSigs delegateSpecs cRep'  :=
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
                                          (cAbsR := _)));
          unfold Dep_Type_BoundedIndex_app_comm_cons; simpl
    end.

  FullySharpenEachMethod [BagSig Book (BuildSearchTermFromAttributes BookSearchTerm);
                           BagSig Order (BuildSearchTermFromAttributes OrderSearchTerm)]
                         (icons _ (BagSpec (SearchTermFromAttributesMatcher BookSearchTerm))
                         (icons _ (BagSpec (SearchTermFromAttributesMatcher OrderSearchTerm))
                                (inil ADT)))
                         (fun DelegateImpl : ilist cADT
                                                [BagSig Book (BuildSearchTermFromAttributes BookSearchTerm);
                                                  BagSig Order (BuildSearchTermFromAttributes OrderSearchTerm)] => prod (cRep (ilist_hd DelegateImpl)) (cRep (ilist_hd (ilist_tl DelegateImpl)))).
  instantiate (2 := fun (DelegateImpl : ilist cADT
                                                [BagSig Book (BuildSearchTermFromAttributes BookSearchTerm);
                                                  BagSig Order (BuildSearchTermFromAttributes OrderSearchTerm)])
                              ValidImpl
                        (r_o : IndexedQueryStructure BookStoreSchema BookStoreIndices)
                        (r_n : cRep (ilist_hd DelegateImpl) *
                               cRep (ilist_hd (ilist_tl DelegateImpl))) =>
                      AbsR (ValidImpl 0)
                           (GetIndexedRelation r_o {| bindex := sBOOKS |})
                           (fst r_n) /\
                      AbsR (ValidImpl 1)
                           (GetIndexedRelation r_o {| bindex := sORDERS |})
                           (snd r_n)).
  simpl.
  intros; repeat econstructor; simpl;
  unfold GetIndexedRelation, i2th_Bounded, ith_Bounded_rect; simpl.

  instantiate (1 := fun (DI : ilist cADT
                                    [BagSig Book
                                            (BuildSearchTermFromAttributes BookSearchTerm);
                                      BagSig Order
                                             (BuildSearchTermFromAttributes OrderSearchTerm)])
                        d =>
          (CallConstructor (ilist_hd DI) "EmptyBag" d, CallConstructor (ilist_hd (ilist_tl DI)) "EmptyBag" d)); simpl.

  Lemma refine_ret_v {A : Type} :
    forall (a : A) c,
      refine c (ret a) -> c ↝ a.
    intros * H; apply (H _ (ReturnComputes a)).
  Qed.

  pose proof (refine_ret_v (ADTRefinementPreservesConstructors (ValidImpl 0)
              {| bindex := "EmptyBag" |} d)) as H'; simpl in H';
  apply computes_to_inv in H'; destruct_ex; intuition;
  apply computes_to_inv in H1; destruct_ex; intuition; 
  apply computes_to_inv in H0; subst; eauto.

  pose proof (refine_ret_v (ADTRefinementPreservesConstructors (ValidImpl 1)
              {| bindex := "EmptyBag" |} d)) as H'; simpl in H';
  apply computes_to_inv in H'; destruct_ex; intuition;
  apply computes_to_inv in H1; destruct_ex; intuition; 
  apply computes_to_inv in H0; subst; eauto.

  intros; split; 
  unfold GetIndexedRelation, i2th_Bounded, ith_Bounded_rect; simpl; intros. 
  intuition.
  pose proof (refine_ret_v 
                (ADTRefinementPreservesMethods
                   (ValidImpl 1)
                   {| bindex := "Delete" |} 
                   (GetIndexedRelation r_o {| bindex := sORDERS |})
                   (snd r_n)
                   (None, [fun a : Order => ?[eq_nat_dec a!sISBN d]]) 
                   H1)) as H'; simpl in H'.


)) as H'; simpl in H';
  apply computes_to_inv in H'; destruct_ex; intuition;
  apply computes_to_inv in H1; destruct_ex; intuition; 
  apply computes_to_inv in H0; subst; eauto.


  

  Show Existentials.
  instantiate (1 := fun (DI : ilist cADT
                                    [BagSig Book
                                            (BuildSearchTermFromAttributes BookSearchTerm);
                                      BagSig Order
                                             (BuildSearchTermFromAttributes OrderSearchTerm)])
                        d =>
                      (CallConstructor (ilist_hd DI) "EmptyBag" d, ()) ).
  unfold CallConstructor in H1.

  simpl in *;



  idtac.

  simpl in *.
  Check (fun (r_o : IndexedQueryStructure BookStoreSchema BookStoreIndices) =>
           GetIndexedRelation r_o {| bindex := sBOOKS |}).

                           (fst r_n)).

  eapply Notation_Friendly_SharpenFully
  with (DelegateSpecs := i1)
         (cConstructors := i)
         (cMethods := i0).
                 => ).

            (icons _ (BagSpec (SearchTermFromAttributesMatcher BookSearchTerm))
                   (icons _ (BagSpec (SearchTermFromAttributesMatcher OrderSearchTerm))
                          (inil ADT)))
         (cAbsR := fun _ _ _ => True).

  intros; pose (ADTRefinementPreservesMethods (X 1));
  pose (ADTRefinementPreservesMethods (X 0)); simpl in *.
  generalize (r1 {| bindex := "Delete" |}).
  simpl.
  intros; eapply SharpenIfComputesTo.
  Show Existentials.

pose (X 0); simpl in *.
  generalize (ADTRefinementPreservesConstructors d0).
  Print refineADT.
  eapply d0.
  intros; eapply SharpenIfComputesTo; repeat constructor.
  intros; eapply SharpenIfComputesTo; repeat constructor.
  intros; eapply SharpenIfComputesTo; repeat constructor.
Defined.
*)
Admitted.

(*Definition BookStoreImpl : ComputationalADT.cADT BookStoreSig.
  extract implementation of BookStoreManual using (inil _).
Defined.

Print BookStoreImpl. *)
