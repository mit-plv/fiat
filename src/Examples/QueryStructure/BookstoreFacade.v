Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import Bedrock.Memory.
Definition boolToWord (b : bool) : W :=
  if b then Word.natToWord _ 1 else Word.natToWord _ 0.

Instance : Query_eq (Word.word n) :=
  { A_eq_dec := @Word.weq n }.
Opaque Word.weq.
Opaque Word.natToWord.
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
              schema <sAUTHOR :: W,
                      sTITLE :: W,
                      sISBN :: W>
                      where UniqueAttribute ``sISBN;
      relation sORDERS has
              schema <sISBN :: W,
                      sDATE :: W> ]
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

(* Now we write what the methods should actually do. *)

Definition BookStoreSpec : ADT _ :=
  QueryADTRep BookStoreSchema {
    Def Constructor0 "Init" : rep := empty,

    Def Method1 "PlaceOrder" ( r : rep) (o : Order) : rep * bool :=
        Insert o into r!sORDERS,

    Def Method1 "AddBook" (r : rep) (b : Book) : rep * bool :=
        Insert b into r!sBOOKS ,

    Def Method1 "GetTitles" (r : rep) (author : W) : rep * list W :=
        titles <- For (b in r ! sBOOKS)
               Where (author = b!sAUTHOR)
               Return (b!sTITLE);
    ret (r, titles),

    Def Method1 "NumOrders" (r : rep) (author : W ) : rep * W :=
      count <- Count (For (o in r!sORDERS) (b in r!sBOOKS)
                              Where (author = b!sAUTHOR)
                              Where (o!sISBN = b!sISBN)
                              Return ());
      ret (r, Word.natToWord 32 count)
}%methDefParsing.

Theorem SharpenedBookStore :
  MostlySharpened BookStoreSpec.
Proof.

  start sharpening ADT.
  simpl; pose_string_hyps; pose_heading_hyps.
  start_honing_QueryStructure'.
  hone method "AddBook".
  { setoid_rewrite UniqueAttribute_symmetry.
    setoid_rewrite (@refine_uniqueness_check_into_query' BookStoreSchema Fin.F1 _ _ _ _).
    setoid_rewrite refine_For_rev.
    setoid_rewrite refine_Count.
    simplify with monad laws; simpl in *; subst.
    setoid_rewrite refine_pick_eq'.
    setoid_rewrite refine_bind_unit.
    setoid_rewrite refine_If_Then_Else_Duplicate.
    finish honing. }
  GenerateIndexesForAll EqExpressionAttributeCounter
  ltac:(fun attrlist =>
          let attrlist' := eval compute in (PickIndexes _ (CountAttributes' attrlist)) in
              make_simple_indexes attrlist'
                                  ltac:(LastCombineCase6 BuildEarlyEqualityIndex)
                                         ltac:(LastCombineCase5 BuildLastEqualityIndex)).
  + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + setoid_rewrite refine_For_rev; simplify with monad laws.
    plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + setoid_rewrite refine_For_rev; simplify with monad laws.
    plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + setoid_rewrite refine_For_rev; simplify with monad laws.
    plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + setoid_rewrite refine_For_rev; simplify with monad laws.
    plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + hone method "PlaceOrder".
    { simpl in *; subst.
      setoid_rewrite refine_Count; simplify with monad laws.
      setoid_rewrite app_nil_r;
        setoid_rewrite map_map; simpl.
      unfold ilist2_hd at 1; simpl.
      setoid_rewrite rev_length.
      setoid_rewrite map_length.
      setoid_rewrite refine_pick_eq'; simplify with monad laws.
      repeat setoid_rewrite refine_If_Then_Else_Bind.
      repeat setoid_rewrite refineEquiv_bind_bind.
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
      unfold H1.
      eapply refine_under_bind; intros; set_evars.
      rewrite (CallBagFind_fst H0); simpl.
      finish honing.
    }
    hone method "AddBook".
    { simpl in *; subst; simplify with monad laws.
      setoid_rewrite app_nil_r;
        setoid_rewrite map_map; simpl.
      unfold ilist2_hd at 1; simpl.
      repeat setoid_rewrite rev_length.
      setoid_rewrite map_length.
      setoid_rewrite refine_pick_eq'; simplify with monad laws.
      repeat setoid_rewrite refine_If_Then_Else_Bind.
      repeat setoid_rewrite refineEquiv_bind_bind.
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
      unfold H1; eapply refine_under_bind; intros; set_evars.
      rewrite (CallBagFind_fst H0); simpl.
      finish honing.
    }
    hone method "GetTitles".
    { simpl in *; subst; simplify with monad laws.
      setoid_rewrite refine_pick_eq'; simplify with monad laws.
      simpl.
      unfold H1; eapply refine_under_bind; intros; set_evars.
      rewrite app_nil_r, map_map; unfold ilist2_hd; simpl.
      rewrite (CallBagFind_fst H0); simpl.
      finish honing.
    }
    hone method "NumOrders".
    { simpl in *; subst.
      setoid_rewrite refine_Count; simplify with monad laws.
      setoid_rewrite refine_pick_eq'; simplify with monad laws.
      simpl.
      unfold H1; eapply refine_under_bind; intros; set_evars.
      setoid_rewrite app_nil_r.
      rewrite (CallBagEnumerate_fst H0); simpl.
            Definition flatten_CompList'
                 (A B : Type)
                 (c : list (B -> Comp (B * list A)))
                 (b : B)
        : Comp (B * list A) := 
        fold_right (fun a b =>
                      l <- b;
                    l' <- a (fst l);
                    ret (fst l', app (snd l') (snd l)))
                   (ret (b, [ ]))  c.

      Definition Join_Comp_Lists_prod
                 {n}
                 {A B : Type}
                 {f : A -> Type}
                 {As : Vector.t A n}
                 {a : A}
                 (b : B)
                 (l' : list (ilist2 (B := f) As))
                 (c : B -> ilist2 (B := f) As -> Comp (B * list (f a)))
        : Comp (B * list (ilist2 (B := f) (Vector.cons _ a _ As))) :=
            flatten_CompList' (map (fun a' b' => l <- c b' a'; (ret (fst l, map (fun fa : f a => icons2 fa a') (snd l)))) l') b.

              
      Lemma Join_Comp_Lists_eq qs_schema Index n A' B A :
        forall r_n a f' (f : ilist2 A -> B) l (z : _ -> B -> Comp (IndexedQueryStructure qs_schema Index * list _)),
        (forall r_n a, refine (u <- z r_n a; ret (fst u)) (ret r_n) )
        -> refine (Join_Comp_Lists (A := A' ) (f := f') (n := n) (a := a) l
                                  (fun a =>
                                     u <- z r_n (f a);
                                   ret (snd u)))
                 (r' <- Join_Comp_Lists_prod r_n l
                     (fun r_n' a =>
                        z r_n' (f a)) ;
                  ret (snd r')).
      Proof.
        intros.
        induction l; unfold Join_Comp_Lists, Join_Comp_Lists_prod; simpl.
        - intros v CompV.
          computes_to_inv; subst.
          computes_to_econstructor.
        - simplify with monad laws.
          setoid_rewrite IHl.
          repeat setoid_rewrite refineEquiv_bind_bind.
          intros v Comp_v; computes_to_inv; subst.
          repeat computes_to_econstructor; eauto.
          pose proof (H _ (f a0) _ (ReturnComputes r_n)).
          computes_to_inv; subst.
      Admitted.

      Lemma foo qs_schema Index
        : forall idx n h f r_n l,
          refine (Join_Comp_Lists (n := n) l
                                  (fun a0 : ilist2 h =>
                                     u <- @CallBagMethod qs_schema Index idx BagFind
                                       r_n
                                       (f a0);
                                   ret (snd u)))
                 (u <- Join_Comp_Lists_prod r_n l 
                                  (fun r_n (a0 : ilist2 h) =>
                                     @CallBagFind qs_schema Index idx
                                       r_n
                                       (f a0));
                 ret (snd u)) .
      Proof.
        intros.
      Admitted.
      Lemma foo' qs_schema Index
        : forall idx n h f r_n l a,
                 computes_to (Join_Comp_Lists_prod (n := n) r_n l 
                                  (fun r_n (a0 : ilist2 h) =>
                                     @CallBagFind qs_schema Index idx
                                       r_n
                                       (f a0))) a
                 -> r_n = (fst a).
      Proof.
        intros.
      Admitted.
      
      etransitivity.
      eapply refine_under_bind_both.
      eapply (@foo BookStoreSchema Index Fin.F1).
      intros; finish honing.
      simplify with monad laws.
      unfold H2; apply refine_under_bind.
      intros.
      apply foo' in H3; rewrite H3.
      finish honing.
    }
    simpl.
    eapply reflexivityT.
  + unfold CallBagFind, CallBagInsert.
    pose_headings_all.
Ltac FullySharpenQueryStructure' qs_schema Index :=
  let DelegateSigs := constr:(@Build_IndexedQueryStructure_Impl_Sigs _ (qschemaSchemas qs_schema) Index) in
  let DelegateSpecs := constr:(@Build_IndexedQueryStructure_Impl_Specs _ (qschemaSchemas qs_schema) Index) in
  let cRep' := constr:(@Build_IndexedQueryStructure_Impl_cRep _ (qschemaSchemas qs_schema) Index) in
  let cAbsR' := constr:(@Build_IndexedQueryStructure_Impl_AbsR qs_schema Index) in
  let ValidRefinements := fresh in
  let FullySharpenedImpl := fresh "FullySharpenedImpl" in
  match goal with
    |- @FullySharpenedUnderDelegates _ (@BuildADT ?Rep ?n ?n' ?consSigs ?methSigs ?consDefs ?methDefs) _ =>
    ilist_of_dep_evar n
                      (Fin.t (numRawQSschemaSchemas qs_schema) -> Type)
                      (fun D =>
                         forall idx,
                           ComputationalADT.pcADT (DelegateSigs idx) (D idx))
                      (fun
                          (DelegateReps : Fin.t _ -> Type)
                          (DelegateImpls : forall idx,
                              ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                          (Sig : consSig) =>
                          ComputationalADT.cConstructorType (cRep' DelegateReps)
                                                            (consDom Sig))
                      consSigs
                      ltac:(fun cCons =>
                              ilist_of_dep_evar n'
                                                (Fin.t (numRawQSschemaSchemas qs_schema) -> Type)
                                                (fun D =>
                                                   forall idx,
                                                     ComputationalADT.pcADT (DelegateSigs idx) (D idx))
                                                (fun (DelegateReps : Fin.t _ -> Type)
                                                     (DelegateImpls : forall idx,
                                                         ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                                     (Sig : methSig) =>
                                                   ComputationalADT.cMethodType (cRep' DelegateReps)
                                                                                (methDom Sig) (methCod Sig))
                                                methSigs
                                                ltac:(fun cMeths =>
                                                        assert
                                                          ((forall
                                                               (DelegateReps : Fin.t (numRawQSschemaSchemas qs_schema) -> Type)
                                                               (DelegateImpls : forall idx,
                                                                   ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                                               (ValidImpls
                                                                : forall idx : Fin.t (numRawQSschemaSchemas qs_schema),
                                                                   refineADT (DelegateSpecs idx)
                                                                             (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                                                               Iterate_Dep_Type_BoundedIndex
                                                                 (fun idx =>
                                                                    @refineConstructor _
                                                                      (cRep' DelegateReps) (cAbsR' _ _ ValidImpls)
                                                  (consDom (Vector.nth consSigs idx))
                                                  (getConsDef consDefs idx)
                                                  (ComputationalADT.LiftcConstructor _ _ (ith  (cCons DelegateReps DelegateImpls) idx))))
                                                           * (forall
                                                                 (DelegateReps : Fin.t (numRawQSschemaSchemas qs_schema) -> Type)
                                                                 (DelegateImpls : forall idx,
                                                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                                                 (ValidImpls
                                                                  : forall idx : Fin.t (numRawQSschemaSchemas qs_schema),
                                                                     refineADT (DelegateSpecs idx)
                                                                               (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                                                                 Iterate_Dep_Type_BoundedIndex
                                                                   (fun idx =>
                                                                      @refineMethod
                                                                        _ (cRep' DelegateReps)
                                                                        (cAbsR' _ _ ValidImpls)
                                                                        (methDom (Vector.nth methSigs idx))
                                                                        (methCod (Vector.nth methSigs idx))
                                                                        (getMethDef methDefs idx)
                                                                        (ComputationalADT.LiftcMethod (ith (cMeths DelegateReps DelegateImpls) idx))))) as ValidRefinements;
                                                      [ |
                                                        pose proof (@Notation_Friendly_SharpenFully'
                                                                      _
                                                                      _
                                                                      _
                                                                      consSigs
                                                                      methSigs
                                                                      consDefs
                                                                      methDefs
                                                                      _
                                                                      DelegateSigs
                                                                      cRep'
                                                                      cCons
                                                                      cMeths
                                                                      DelegateSpecs
                                                                      cAbsR'
                                                                      (fst ValidRefinements)
                                                                      (snd ValidRefinements))
                                                          as FullySharpenedImpl
                                                        ; clear ValidRefinements ] ))
  end;
    [ simpl; intros; split;
      [ repeat split; intros; try exact tt;
        try (etransitivity;
             [eapply (@Initialize_IndexedQueryStructureImpls_AbsR qs_schema Index)
             | ];
             cbv beta;
             unfold Initialize_IndexedQueryStructureImpls',
             CallBagImplConstructor; simpl;
             higher_order_reflexivity
            )
      | repeat split; intros; try exact tt;
        try implement_bag_methods
      ] | ].

    match goal with
      | |- appcontext[ @BuildADT (IndexedQueryStructure ?Schema ?Indexes) ] =>
        FullySharpenQueryStructure' Schema Indexes
      end.

  etransitivity;
  [ repeat (first [
             simpl; simplify with monad laws
           | remove_spurious_Dep_Type_BoundedIndex_nth_eq
           | Implement_If_Then_Else
           | Implement_If_Opt_Then_Else
           | Implement_Bound_Bag_Call
           | Implement_Bound_Join_Comp_Lists
           | Implement_AbsR_Relation
           | match goal with
               |- context[CallBagImplMethod _ _ _ _ _] =>
               unfold CallBagImplMethod; cbv beta; simpl
             end
           | higher_order_reflexivity ]; simpl) |].

  Definition Join_Comp_Lists_prod'
           {n} {A B : Type} {f : A -> Type} {As : Vector.t A n} {a : A}
           (b : B) (l : list (ilist2 (B := f) As)) (c : B -> ilist2 (B := f) As -> B * list (f a)) : B * list (ilist2 (B := f) (Vector.cons _ a _ As)) :=
    fold_right (fun a' b' => (fst (c (fst b') a'),
                              app (snd b')
                                  (flatten (map
                                              (fun l' => map (fun fa : f a => icons2 fa l') (snd (c (fst b') l'))) l))
                                  
               )) (b, [ ]) l.
  idtac.

  
  Lemma Join_Comp_Lists_Impl'
        qs_schema
        (n := numRawQSschemaSchemas qs_schema ) (schemas := qschemaSchemas qs_schema) (Index : ilist3 schemas)
        (DelegateReps : Fin.t n -> Type)
        (DelegateImpls : forall idx : Fin.t n,
            ComputationalADT.pcADT
              (Build_IndexedQueryStructure_Impl_Sigs Index idx)
              (DelegateReps idx)) (idx : Fin.t n)
  : forall (r_n : IndexedQueryStructure qs_schema Index) r_n' l f',
     refine (Join_Comp_Lists_prod r_n l
                                    (fun r_n b' =>
                                       br <- CallBagMethod idx BagFind r_n
                                          (f' b');
                                     ret
                                       (UpdateIndexedRelation qs_schema
                                                              Index r_n
                                                              idx (fst br), snd br))

              ) (ret (Join_Comp_Lists_prod' r_n' l (fun r_n b' =>
                                       let br := @CallBagImplMethod _ _ Index DelegateReps DelegateImpls _ BagFind r_n
                                                                    (f' b') in
                                     
                                       (Update_Build_IndexedQueryStructure_Impl_cRep qs_schema Index DelegateReps r_n
                                                              idx (fst br), snd br)) )).
Proof.
  induction l; unfold Join_Comp_Lists, Join_Comp_Lists'; simpl; intros.
  - reflexivity.
  - unfold Join_Comp_Lists_prod, Join_Comp_Lists_prod'; simpl.
Admitted.

(*setoid_rewrite IHl.
    setoid_rewrite refineEquiv_bind_unit.
    repeat setoid_rewrite refineEquiv_bind_bind.
    setoid_rewrite refineEquiv_bind_unit.
    simpl.
    rewrite H; simplify with monad laws.
    f_equiv.
    f_equal.
    unfold Join_Comp_Lists_prod'.
    instantiate (1 := c').
    repeat f_equal.
    repeat (apply functional_extensionality; intros).
    repeat f_equal.
    
    simpl.
    setoid_rewrite IHl; eauto; simplify with monad laws.
    reflexivity.
Qed. *)
idtac.

match goal with
  | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                               ?ValidImpls ?r_o ?r_n
    |- refine (Bind (@Join_Comp_Lists_prod _ _ ?B ?f ?As ?a ?b ?l ?c) _) _ =>
    makeEvar (B -> ilist2 (B := f) As -> B * list (f a))
             ltac:(fun c' =>
                     let refines_c' := fresh in
                     assert (forall b' a', refine (c a' b') (ret (c' a' b'))) as refines_c'; [ | pose proof (fun idx' f => @Join_Comp_Lists_Impl' _ B As a b l idx' f ); pose c'])
  end.
Focus 2.
Set Printing Implicit.
Print Schema.
      
assert (forall idx, (IndexedQueryStructure BookStoreSchema
                                          (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)
       heading 1 [heading0]%NamedSchema SearchUpdateTerm
       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)
          heading0 0 (VectorDef.nil RawHeading) SearchUpdateTerm0
          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) ->
  @ilist2 RawHeading (@RawTuple) 1 [heading0]%NamedSchema ->
  IndexedQueryStructure BookStoreSchema
    (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)
       heading 1 [heading0]%NamedSchema SearchUpdateTerm
       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)
          heading0 0 (VectorDef.nil RawHeading) SearchUpdateTerm0
          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) *
  list (@RawTuple heading)) = (IndexedQueryStructure BookStoreSchema
    (@icons3 RawSchema
       (fun ns : RawSchema => SearchUpdateTerms (rawSchemaHeading ns))
       (relSchema
          relation sBOOKS
          has (let headings :=
                 <sAUTHOR :: W, sTITLE :: W, sISBN :: W>%Heading in
               {|
               schemaRaw := {|
                            rawSchemaHeading := headings;
                            attrConstraints := @None
                                                 (@RawTuple headings -> Prop);
                            tupleConstraints := @Some
                                                  (@RawTuple headings ->
                                                  @RawTuple headings -> Prop)
                                                  (let hHint :=
                                                  {|
                                                  headingHint := headings |} in
                                                  @UniqueAttribute headings
                                                  ``(sISBN)) |};
               schemaHeadingNames := HeadingNames headings |})%NamedSchema) 1
       [schemaRaw (relSchema
          relation sORDERS
          has (let headings := <sISBN :: W, sDATE :: W>%Heading in
               {|
               schemaRaw := {|
                            rawSchemaHeading := headings;
                            attrConstraints := @None
                                                 (@RawTuple headings -> Prop);
                            tupleConstraints := @None
                                                  (@RawTuple headings ->
                                                  @RawTuple headings -> Prop) |};
               schemaHeadingNames := HeadingNames headings |}))]%NamedSchema
       SearchUpdateTerm
       (@icons3 RawSchema
          (fun ns : RawSchema => SearchUpdateTerms (rawSchemaHeading ns))
          (relSchema
             relation sORDERS
             has (let headings := <sISBN :: W, sDATE :: W>%Heading in
                  {|
                  schemaRaw := {|
                               rawSchemaHeading := headings;
                               attrConstraints := @None
                                                  (@RawTuple headings -> Prop);
                               tupleConstraints := @None
                                                  (@RawTuple headings ->
                                                  @RawTuple headings -> Prop) |};
                  schemaHeadingNames := HeadingNames headings |})%NamedSchema)
          0 (VectorDef.nil RawSchema) SearchUpdateTerm0
          (@inil3 RawSchema
             (fun ns : RawSchema => SearchUpdateTerms (rawSchemaHeading ns))))) ->
  @ilist2 RawHeading (@RawTuple) 1 [heading0]%NamedSchema ->
  IndexedQueryStructure BookStoreSchema
    (@icons3 RawSchema
       (fun ns : RawSchema => SearchUpdateTerms (rawSchemaHeading ns))
       (relSchema
          relation sBOOKS
          has (let headings :=
                 <sAUTHOR :: W, sTITLE :: W, sISBN :: W>%Heading in
               {|
               schemaRaw := {|
                            rawSchemaHeading := headings;
                            attrConstraints := @None
                                                 (@RawTuple headings -> Prop);
                            tupleConstraints := @Some
                                                  (@RawTuple headings ->
                                                  @RawTuple headings -> Prop)
                                                  (let hHint :=
                                                  {|
                                                  headingHint := headings |} in
                                                  @UniqueAttribute headings
                                                  ``(sISBN)) |};
               schemaHeadingNames := HeadingNames headings |})%NamedSchema) 1
       _
       SearchUpdateTerm
       (@icons3 RawSchema
          (fun ns : RawSchema => SearchUpdateTerms (rawSchemaHeading ns))
          (relSchema
             relation sORDERS
             has (let headings := <sISBN :: W, sDATE :: W>%Heading in
                  {|
                  schemaRaw := {|
                               rawSchemaHeading := headings;
                               attrConstraints := @None
                                                  (@RawTuple headings -> Prop);
                               tupleConstraints := @None
                                                  (@RawTuple headings ->
                                                  @RawTuple headings -> Prop) |};
                  schemaHeadingNames := HeadingNames headings |})%NamedSchema)
          0 (VectorDef.nil RawSchema) SearchUpdateTerm0
          (@inil3 RawSchema
             (fun ns : RawSchema => SearchUpdateTerms (rawSchemaHeading ns))))) *
  list
    (@RawTuple
       (rawSchemaHeading
          (@Vector.nth RawSchema (numRawQSschemaSchemas BookStoreSchema)
             (qschemaSchemas BookStoreSchema) idx)))))%type.
simpl.
intros. repeat f_equal.
reflexivity.

pose (fun idx f => H2 idx f p).
simplify with monad laws.

rewrite G'.
pose proof (Join_Comp_Lists_Impl' _ _ _ H1).
  

    Time Defined.

Time Definition BookstoreImpl :=
  Eval simpl in (fst (projT1 SharpenedBookStore)).

Print BookstoreImpl.
