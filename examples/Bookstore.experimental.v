Section BookStoreExamples.
  Require Import QueryStructureNotations.
  Require Import ListImplementation.
  Require Import AdditionalLemmas AdditionalMorphisms.

  Unset Implicit Arguments.

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

  Definition sBOOKS := "Books".
  Definition sAUTHOR := "Authors".
  Definition sTITLE := "Title".
  Definition sISBN := "ISBN".
  Definition sORDERS := "Orders".
  Definition sDATE := "Date".

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
      enforcing [attribute sISBN of sORDERS references sBOOKS].

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

  Definition BookStoreSig : ADTSig :=
    ADTsignature {
        "InitBookstore" : unit → rep,
        "PlaceOrder" : rep × Order → rep × unit,
        "AddBook" : rep × Book → rep × unit,
        "GetTitles" : rep × string → rep × list string,
        "NumOrders" : rep × string → rep × nat
      }.

  Definition BookStoreSpec : ADT BookStoreSig :=
    QueryADTRep BookStoreSchema {
      const "InitBookstore" (_ : unit) : rep := empty,

      update "PlaceOrder" ( o : Order ) : unit :=
          Insert o into sORDERS,

      update "AddBook" ( b : Book ) : unit :=
          Insert b into sBOOKS ,

      query "GetTitles" ( author : string ) : list string :=
        For (b in sBOOKS)
        Where (author = b!sAUTHOR)
        Return (b!sTITLE),

       query "NumOrders" ( author : string ) : nat :=
          Count (For (o in sORDERS) (b in sBOOKS)
                 Where (author = b!sAUTHOR)
                 Where (b!sISBN = o!sISBN)
                 Return o!sISBN)
  }.

  Require Import BagsOfTuples Bool.

  (* (* TODO *)
  Eval compute in 
      (
        let relation_key := 
            (fun (x : BoundedIndex (map relName (qschemaSchemas BookStoreSchema))) => x)
              {| bindex := sBOOKS; indexb := _ |} in
        let attribute_key := 
            (fun (x :  Attributes (GetNRelSchemaHeading (qschemaSchemas BookStoreSchema) relation_key)) => x)
              {| bindex := sISBN; indexb := _ |} in
        attribute_key
      ).
   *)
  
  Notation "qs_schema / rel_index" := (GetRelationKey qs_schema rel_index) (at level 40, left associativity).
  Notation "rel_key // attr_index" := (GetAttributeKey rel_key attr_index) (at level 50).

  Definition Books := BookStoreSchema/sBOOKS. 
  Definition Orders := BookStoreSchema/sORDERS.
  Definition BookSchema := QSGetNRelSchemaHeading BookStoreSchema Books.
  Definition OrderSchema := QSGetNRelSchemaHeading BookStoreSchema Orders.

  Definition BookStorage : @BagPlusBagProof Book.
    mkIndex BookSchema [ Books//sAUTHOR; Books//sISBN ].
  Defined.

  Definition OrderStorage : @BagPlusBagProof Order.
    mkIndex OrderSchema [ Orders//sISBN ].
  Defined.

  Definition TBookStorage := BagType BookStorage.
  Definition TOrderStorage := BagType OrderStorage.

  Definition BookStoreListImpl_AbsR
             (or : UnConstrQueryStructure BookStoreSchema)
             (nr : TBookStorage * TOrderStorage) : Prop :=
    or ! sBOOKS ≃ benumerate (fst nr) /\ or ! sORDERS ≃ benumerate (snd nr).

  Opaque Query_For.
  Opaque benumerate bfind_matcher bfind benumerate. (* TODO *)

  (* TODO: How to do the instantiations automatically? *)

  Definition BookStore :
    Sharpened BookStoreSpec.
  Proof.
    unfold BookStoreSpec.

    (* Step 1: Drop the constraints on the tables. From the perspective
      of a client of a sharpened ADT the invariants will still hold,
      since ADT refinement preserves the simulation relation. *)

    match goal with
        |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _] =>
        hone representation using (@DropQSConstraints_AbsR Rep)
    end.
    
    drop constraints from insert "PlaceOrder".
    drop constraints from insert "AddBook".
    drop constraints from query "GetTitles".
    drop constraints from query "NumOrders".

    (*TODO: start honing QueryStructure.*)

    hone representation using BookStoreListImpl_AbsR.

    hone constructor "InitBookstore". {
       unfold BookStoreListImpl_AbsR.

      repeat setoid_rewrite refineEquiv_pick_ex_computes_to_and;
      repeat setoid_rewrite refineEquiv_pick_eq';
      simplify with monad laws.

      rewrite (refine_pick_val' (bempty, bempty)) by (intuition; apply bempty_correct_DB).
      subst_body; higher_order_1_reflexivity. 
    }

    Notation "?[ A ]" := (if A then true else false) (at level 50).

    hone method "NumOrders". {
      unfold BookStoreListImpl_AbsR in H; split_and.

      setoid_rewrite refineEquiv_pick_ex_computes_to_and;
      setoid_rewrite refineEquiv_pick_pair;
      setoid_rewrite refineEquiv_pick_eq';
      simplify with monad laws; cbv beta;
      simpl.

      (* Step 1: Move to a concrete representation *)
      rewrite refine_List_Query_In by eassumption.
      rewrite refine_Join_List_Query_In by eassumption.
      rewrite refine_List_Query_In_Where; instantiate (1 := _).
      rewrite refine_List_Query_In_Where; instantiate (1 := _).
      rewrite refine_List_For_Query_In_Return_Permutation.
      simpl.

      (* Step 2: Make it more efficient *)
      rewrite (filter_join_snd (fun (a: Book) => ?[string_dec n (a!sAUTHOR)])).
      
      rewrite filter over BookStorage using search term
                (Some n, (@None nat, @nil (TSearchTermMatcher BookSchema))).

      setoid_rewrite swap_joins; trickle_swap; simpl.

      setoid_rewrite filter_join_lists; simpl.

      rewrite dependent filter 
                (fun (x: Book) (y : Order) => ?[eq_nat_dec x!sISBN y!sISBN]) 
              over OrderStorage using dependent search term 
                (fun (x: Book) => (Some x!sISBN, @nil (TSearchTermMatcher OrderSchema))).

      setoid_rewrite (bfind_correct _).

      setoid_rewrite map_flat_map.      
      setoid_rewrite map_map; simpl.
      
      setoid_rewrite refine_Permutation_Reflexivity.
      simplify with monad laws.

      (* Step 3: Pass the database, unmodified *)
      unfold BookStoreListImpl_AbsR.
      rewrite refine_pick_val by eauto.
      simplify with monad laws.

      (* Step 4: A few final tweaks *)
      setoid_rewrite length_flat_map.
      setoid_rewrite map_length.

      (* Step 5: All done *)
      finish honing.
    }

    hone method "GetTitles". {
      unfold BookStoreListImpl_AbsR in H; split_and.
      
      setoid_rewrite refineEquiv_pick_ex_computes_to_and;
      setoid_rewrite refineEquiv_pick_pair;
      setoid_rewrite refineEquiv_pick_eq';
      simplify with monad laws; cbv beta;
      simpl.
 
      rewrite refine_List_Query_In by eassumption.
      setoid_rewrite refine_List_Query_In_Where; instantiate (1 := _).
      rewrite refine_List_For_Query_In_Return_Permutation.

      rewrite filter over BookStorage using search term
              (Some n, (@None nat, @nil (TSearchTermMatcher BookSchema))).

      setoid_rewrite (bfind_correct _).

      setoid_rewrite refine_Permutation_Reflexivity.
      simplify with monad laws.

      unfold BookStoreListImpl_AbsR.
      rewrite refine_pick_val by eauto. 
      simplify with monad laws.
      finish honing.
    }

    hone method "PlaceOrder". {
      Lemma refine_trivial_if_then_else :
        forall x,
          refine 
            (If_Then_Else x (ret true) (ret false))
            (ret x).
      Proof.
        destruct x; reflexivity.
      Qed.

      Notation " A ! B " := (A ``(B)) (at level 2).
      setoid_rewrite refine_trivial_if_then_else.


      unfold BookStoreListImpl_AbsR in H; split_and.
      
      setoid_rewrite refineEquiv_pick_ex_computes_to_and;
      setoid_rewrite refineEquiv_pick_pair;
      setoid_rewrite refineEquiv_pick_eq';
      simplify with monad laws; cbv beta;
      simpl.

      rewrite refine_pick_val by eauto using EnsembleIndexedListEquivalence_pick_new_index.
      simplify with monad laws.


      Check refine_List_Query_In.
      
      Lemma in_indexed_in_list :
        forall {heading} table seq P,
          (@EnsembleIndexedListEquivalence heading table seq) ->
          ((exists itup, table itup /\ P (indexedTuple itup)) <-> 
           (exists tup,  List.In tup seq /\ P tup)).
      Proof.
        intros * ( indices & [ seq' ( map_correct & nodup & equiv ) ] ).
        split; subst; setoid_rewrite in_map_iff; intros [ tup' (_in & _P) ].

        - eexists; split; 
          [ eexists; split; [ reflexivity | apply equiv ] | ]; 
          eassumption. 
        - destruct _in as [ tup'' ( proj_eq & _in ) ];
          eexists; subst; split; [ apply equiv |  ];
          eassumption.
      Qed.        

      Show.
      Add Parametric Morphism :
        (decides)
          with signature (eq ==> iff ==> iff) 
            as decides_eq_iff_eq_morphism.
      Proof.
        intros b **; unfold decides; destruct b; intuition.
      Qed.

      Require Import Compare_dec.

      Definition gtb x y :=
        andb (leb y x) (negb (beq_nat x y)). 
  

        Lemma blah :
          forall {schm tbl} P,
          forall (c : UnConstrQueryStructure schm),
            refine
              (Pick (fun (b : bool) =>
               decides b
                       (exists tup2: @IndexedTuple _,
                          (GetUnConstrRelation c tbl tup2 /\ P (indexedTuple tup2)))))
              (Bind 
                 (Count (For (UnConstrQuery_In c tbl (fun tup => Where (P tup) Return 1))))
                 (fun count => ret (gtb count 0))).
        Proof.
          Transparent Query_For.

          unfold refine, decides, Count, Query_In, UnConstrQuery_In,  Query_Where, Query_Return; 
          unfold Query_For, QueryResultComp, flatten_CompList; intros.
          inversion_by computes_to_inv; subst.
          constructor.
 
          generalize (GetUnConstrRelation c tbl) H0.
          clear H0.
          induction x2.

          admit.

          intros.
          unfold EnsembleListEquivalence in H0.


          Lemma snif :
            forall {heading} P seq ens,
              computes_to (For (QueryResultComp (heading := heading) ens (fun tup => Where (P tup) Return tup))) seq ->
              forall x, 
                List.In x seq -> P x.
          Proof.
            unfold refine, decides, Count, Query_In, UnConstrQuery_In,  Query_Where, Query_Return; 
            unfold Query_For, QueryResultComp; induction seq as [ | head seq' IH ]; intros.
            
            intuition.

            inversion_by computes_to_inv.

            Require Import AdditionalPermutationLemmas.

            pose proof (permutation_cons_in H2) as in_x0.
            apply in_split in in_x0.
            destruct in_x0 as [ x0_before [ x0_after ? ] ]; subst. 
            symmetry in H2. apply Permutation_cons_app_inv in H2.

            rewrite map_map in H3.


            Definition boxed_option {heading} (P: _ -> Prop) (x: @IndexedTuple heading) :=
              Pick (fun l : list Tuple => (P x -> ret [indexedTuple x] ↝ l) /\ (~ P x -> l = [])).

            Require Import List.
            Lemma temp :
              forall {heading} P x1 x0_before (head: @Tuple heading) x0_after,
                flatten_CompList 
                  (map (boxed_option P) x1) ↝ (x0_before ++ head :: x0_after) ->
                exists x1_before head' x1_after,
                  x1 = x1_before ++ head' :: x1_after /\
                  flatten_CompList (map (boxed_option P) x1_before) ↝ x0_before /\
                  flatten_CompList (map (boxed_option P) [head']  ) ↝ [head]    /\
                  flatten_CompList (map (boxed_option P) x1_after ) ↝ x0_after.
            Proof.
            Admitted.

            Show.
            assert ( flatten_CompList
                       (map (boxed_option P) x1)
                       ↝ x0_before ++ head :: x0_after) as H3' by (clear; admit); clear H3.
            destruct (temp _ _ _ _ _ H3') as [ x1_before [ head' [ x1_after (_eq & before & middle & after) ] ] ]; subst.


            unfold boxed_option in middle; simpl in middle. 
            Unset Ltac Debug.
            apply computes_to_inv in middle.
            destruct middle as [head'' (middle1 & middle2)].
            apply computes_to_inv in middle1.
            apply computes_to_inv in middle2.
            destruct middle1 as ( spec1 & spec2 ).
            destruct middle2 as [ nil' (ret_nil & ret_cons) ].
            (* inversion_by computes_to_inv. (* broken *) *)

            apply computes_to_inv in ret_nil; subst.
            rewrite app_nil_r in *; subst.
            apply computes_to_inv in ret_cons; subst.

            Lemma singleton_neq_nil :
              forall {A} (a: A),
                [a] = [] <-> False.
            Proof.
              intuition discriminate.
            Qed.              

            rewrite singleton_neq_nil in spec2.
            assert (forall a, ~ ~ P a -> P a) as excl by (clear; admit).
            apply excl in spec2.
            specialize (spec1 spec2).

            apply computes_to_inv in spec1.
            injection spec1; intros; subst.

            destruct H0.

            subst x; intuition. (* deduce from H3 *)
            
            eapply IH; eauto.
            
            econstructor; [ | constructor; symmetry; eassumption ].
            econstructor.

            constructor.
            instantiate (1 := x1_before ++ x1_after).
            instantiate (1 := fun x => ens x /\ x <> head').

            admit. (*use non-duplication*)

            (* TODO: Montrer que head est dans x1, découper x1, découper ens *)
            
            Lemma flatten_CompList_app :
              forall {A} x1 x2 x1' x2',
                flatten_CompList x1 ↝ x1' ->
                flatten_CompList x2 ↝ x2' ->
                @flatten_CompList A (x1 ++ x2) ↝ (x1' ++ x2').
            Proof.
              induction x1; simpl; intros.
              inversion_by computes_to_inv; subst.

              rewrite !app_nil_l; assumption.
              inversion_by computes_to_inv.

              specialize (IHx1 x2 x0 x2' H2 H0). 
              econstructor; eauto.
              econstructor; eauto.
              subst; rewrite app_assoc; constructor.
            Qed.

            rewrite !map_app.
            apply flatten_CompList_app.


                                 
                                 flatten_CompList
  (map
        (fun tup : Tuple =>
           {l : list Tuple | P tup -> ret [tup] ↝ l /\ ~ P tup -> l = []})
        (map indexedTuple (x1_before ++ x1_after))) ↝ 
     x0_before ++ x0_after
            econstructor; try eassumption.
            
            destruct H0; subst.
            generalize x1, (GetUnConstrRelation c tbl), H1, H3.
            clear H1 H3 x1.

            induction x1 as [ | head_x1 x1' IHx1 ];
              simpl in *;
              intros;
              inversion_by computes_to_inv;
              subst.
            
            apply Permutation_length in H2; simpl in H2; discriminate.
            
            destruct inversion_by computes_to_inv.
            simpl in H.
            
          
        Admitted.

        Show.
        setoid_rewrite (blah (fun (b: Book) => n!sISBN = b!sISBN)).

      simplify with monad laws.
      
      rewrite refine_List_Query_In by eassumption.
      setoid_rewrite refine_List_Query_In_Where; instantiate (1 := _).
      rewrite refine_List_For_Query_In_Return_Permutation.

      rewrite filter over BookStorage using search term
              (@None string, (Some n!sISBN, @nil (TSearchTermMatcher BookSchema))).

      setoid_rewrite (bfind_correct _).
      setoid_rewrite refine_Permutation_Reflexivity.
      simplify with monad laws.

      setoid_rewrite map_length.
      unfold BookStoreListImpl_AbsR.
      
      Split Constraint Checks.

      
      set (aa := fun a:TBookStorage => EnsembleIndexedListEquivalence
              ((UpdateUnConstrRelation c ``(sORDERS)
                  (EnsembleInsert
                     {|
                     tupleIndex := Datatypes.length (benumerate (Bag := BagProof OrderStorage) (snd r_n));
                     indexedTuple := n |} c!sORDERS))!sBOOKS)%QueryImpl
              (benumerate (Bag := BagProof BookStorage) a)).
      set (bb := fun a: TOrderStorage => EnsembleIndexedListEquivalence
              ((UpdateUnConstrRelation c ``(sORDERS)
                  (EnsembleInsert
                     {|
                     tupleIndex := Datatypes.length (benumerate (Bag := BagProof OrderStorage)  (snd r_n));
                     indexedTuple := n |} c!sORDERS))!sORDERS)%QueryImpl
              (benumerate (Bag := BagProof OrderStorage) a)).

      Definition ID {A}  := fun (x: A) => x.

      Lemma ens_red :
        forall {heading TContainer TSearchTerm} x y (y_is_bag: Bag TContainer _ TSearchTerm),
          @EnsembleIndexedListEquivalence heading x (benumerate (Bag := y_is_bag) y) =
          (ID (fun y => EnsembleIndexedListEquivalence x (benumerate y))) y.
      Proof.
        intros; reflexivity.
      Qed.

      
      setoid_rewrite ens_red.
      setoid_rewrite refineEquiv_pick_pair.
      unfold ID; simpl.
      simplify with monad laws.
      
      (*
      pose proof (refineEquiv_pick_pair (fun a:TBookStorage => EnsembleIndexedListEquivalence
              ((UpdateUnConstrRelation c ``(sORDERS)
                  (EnsembleInsert
                     {|
                     tupleIndex := Datatypes.length (benumerate (Bag := BagProof OrderStorage) (snd r_n));
                     indexedTuple := n |} c!sORDERS))!sBOOKS)%QueryImpl
              (benumerate (Bag := BagProof BookStorage) a)) (fun a: TOrderStorage => EnsembleIndexedListEquivalence
              ((UpdateUnConstrRelation c ``(sORDERS)
                  (EnsembleInsert
                     {|
                     tupleIndex := Datatypes.length (benumerate (Bag := BagProof OrderStorage)  (snd r_n));
                     indexedTuple := n |} c!sORDERS))!sORDERS)%QueryImpl
              (benumerate (Bag := BagProof OrderStorage) a))).

      setoid_rewrite H3; clear H3.
      simplify with monad laws.
      *)

      rewrite (refine_pick_val' (fst r_n)) by ((*apply (fun id => @refine_list_insert_in_other_table _ c id _ (benumerate (Bag := BagProof BookStorage) (fst r_n)) H1);*) 
                                               intuition discriminate).
      simplify with monad laws.

      rewrite refine_pick_val by (apply (binsert_correct_DB (store_is_bag := BagProof OrderStorage) _ _ _ _ H2); eauto).
      simplify with monad laws.

      reflexivity.

      rewrite refine_pick_val by eauto.
      
      reflexivity.
      
      Transparent Query_For.

      clear.
      generalize_all.



      constructor.
      
      Lemma gtb_true_iff :
        forall x y, gtb x y = true <-> x > y.
      Proof.
        unfold gtb; intros;
        rewrite andb_true_iff, negb_true_iff, beq_nat_false_iff, leb_iff;
        intuition omega.
      Qed.          

      Lemma gtb_false_iff :
        forall x y, gtb x y = false <-> x <= y.
      Proof.
        unfold gtb; intros;
        rewrite andb_false_iff, negb_false_iff, beq_nat_true_iff, leb_iff_conv;
        intuition omega.
      Qed.

      destruct (gtb _ _) eqn:eq_gtb; [ rewrite gtb_true_iff in eq_gtb | rewrite gtb_false_iff in eq_gtb ].
      induction x2; simpl in *; intros;
      inversion_by computes_to_inv.

      Lemma EnsembleListEquivalence_nil_In_False :
        forall {heading} (ens: @IndexedTuple heading -> Prop),
          EnsembleListEquivalence ens (@nil (@IndexedTuple heading)) ->
          (forall x, ens x <-> False).
      Proof.
        intros * equiv ** .
        destruct equiv as ( ? & equiv ).
        rewrite equiv. 
        intuition.
      Qed.

      Lemma EnsembleIndexedListEquivalence_nil_In_False :
        forall {heading} ens,
          EnsembleIndexedListEquivalence ens (@nil (@Tuple heading)) ->
          (forall x, ens x <-> False).
      Proof.
        intros * equiv ** .
        destruct equiv as ( _ & [ ? ( map_nil & ? & equiv ) ] ).
        rewrite equiv. 
        apply map_eq_nil_inv in map_nil; subst.
        intuition.
      Qed.

      rewrite <- H3, <- H4 in eq_gtb;
      simpl in eq_gtb; exfalso; omega.

      Lemma count_query :
        forall {A sch} qs tbl F (P: Tuple -> A),
        forall n,
          computes_to
            (Count (For (UnConstrQuery_In (qsSchema := sch)  qs tbl (fun x => Where (F x) Return (P x) )))) n /\ n > 0 <->
          exists x, F x.
      Proof.
        intros.
        unfold Count, Query_For, UnConstrQuery_In, Query_Where, Query_Return, QueryResultComp, flatten_CompList.
        split; intros; inversion_by computes_to_inv.
        Print computes_to.

        rewrite <- H3 in H2.
        rewrite <- H2 in H1.
        subst. clear H3 x.
        


    (* TODO: Look into Typeclasses Opaque (BoundedString Attribute). *)
  Defined.
End BookStoreExamples.
