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
      rewrite (filter_by_equiv _ (bfind_matcher (Bag := BagProof BookStorage) (Some n, (None, [])))) 
        by prove_observational_eq.

      setoid_rewrite swap_joins; trickle_swap; simpl.

      setoid_rewrite filter_join_lists; simpl.
      setoid_rewrite (filter_by_equiv_meta
                 (fun (x: Book) (y : Order) => ?[eq_nat_dec x!sISBN y!sISBN]) 
                 (fun (x: Book) => bfind_matcher (Bag := BagProof OrderStorage) (Some x!sISBN, [])) _).

      setoid_rewrite map_flat_map.      
      setoid_rewrite map_map; simpl.
      
      setoid_rewrite (bfind_correct _).
      setoid_rewrite refine_Permutation_Reflexivity.
      simplify with monad laws.
      
      (* Step 3: Finish honing *)
      unfold BookStoreListImpl_AbsR.
      rewrite refine_pick_val by eauto.
      simplify with monad laws.
      
      (* Step 4: Final tweaks *)
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
      setoid_rewrite refine_List_Query_In_Where.
      rewrite refine_List_For_Query_In_Return_Permutation.

      rewrite (filter_by_equiv _ (bfind_matcher (Bag := BagProof BookStorage) (Some n, (None, [])))) by
          prove_observational_eq.
      
      setoid_rewrite (bfind_correct _).
      setoid_rewrite refine_Permutation_Reflexivity.
      simplify with monad laws.

      unfold BookStoreListImpl_AbsR.
      rewrite refine_pick_val by eauto. 
      simplify with monad laws.
      finish honing.
    }

      pose proof (fun f => filter_by_equiv f (bfind_matcher (Bag := BagProof BookStorage) (Some n, (None, []))) _ (Join_Lists (benumerate (snd r_n))
                          (benumerate (fst r_n)))). by
          prove_observational_eq.
      
      setoid_rewrite refineEquiv_pick_pair_pair.
      setoid_rewrite refineEquiv_pick_eq'.
      simplify with monad laws.
      rewrite refine_pick_val by eassumption.
      simplify with monad laws.
      rewrite refine_pick_val by eassumption.
      simplify with monad laws.
      finish honing.

      rewrite refine_List_Query_In by eassumption.
      setoid_rewrite refine_List_Query_In. by eassumption.
      setoid_rewrite refine_List_Query_In_Where.
      rewrite refine_List_For_Query_In_Return_Permutation.

      rewrite (filter_by_equiv _ (bfind_matcher (Bag := BagProof BookStorage) (Some n, (None, [])))) by
          prove_observational_eq.
      
      setoid_rewrite (bfind_correct _).
      setoid_rewrite refine_Permutation_Reflexivity.
      simplify with monad laws.

      unfold BookStoreListImpl_AbsR.
      rewrite refine_pick_val by eauto. 
      simplify with monad laws.
      finish honing.

    Class IsDecidableBinaryPredicate {A B: Type} (predicate: A -> B -> Prop) :=
      { 
        bool_predicate : A -> B -> bool; 
        is_decidable : 
          forall a b, 
            bool_predicate a b = true <-> predicate a b 
      }.

    Check @bool_predicate.
    Lemma CrossProduct :
      forall {TReturn TRecord1 TRecord2: Type},
      forall (table1: list TRecord1) (table2: list TRecord2) query_body,
      forall predicate (proof: IsDecidableBinaryPredicate predicate),
        Equivalent_Ensembles
          (fun retval : TReturn =>
             exists joined_records : TRecord1 * TRecord2,
               List.In joined_records (Join_Lists table1 table2)
               /\ Where (predicate (fst joined_records) (snd joined_records)) 
                        (query_body (fst joined_records) (snd joined_records)) retval)
          (fun retval : TReturn =>
             exists joined_records : TRecord1 * TRecord2,
               List.In joined_records (Join_Lists table1 (List.filter (fun record2 => bool_predicate (fst joined_records) record2) table2))
               /\ (query_body (fst joined_records) (snd joined_records) retval)).
    Proof.
      unfold Equivalent_Ensembles, Query_Where; intros.
      apply Morphisms_Prop.ex_iff_morphism.
      unfold pointwise_relation.
      intros (rec1 & rec2); simpl.
      unfold Join_Lists; simpl.

      rewrite <- and_assoc.
      apply and_iff_compat_r.
      setoid_rewrite flat_map_flatten.
      setoid_rewrite in_flatten_iff.

      split; intro H;
      [ destruct H as ( [ seq (rec12_in_seq & seq_in_map) ] & pred12) |
        destruct H as [ seq (rec12_in_seq & seq_in_map) ] ];
      rewrite in_map_iff in seq_in_map;
      destruct seq_in_map as [ rec1' (eq_ & in1) ]; subst;
      rewrite in_map_iff in rec12_in_seq;
      destruct rec12_in_seq as [ rec2' (eq_ & in2) ]; inversion eq_; subst; clear eq_.
      {
        eexists; split;
        [ | rewrite in_map_iff; eexists]; eauto.
        rewrite in_map_iff; eexists; split; eauto.
        rewrite filter_In; split; try apply is_decidable; eauto.
      } {
        rewrite filter_In in in2.
        destruct in2 as (in2 & pred_satisfied).
        eexists; [ eexists; split; [ | rewrite in_map_iff ] | apply is_decidable; assumption ]; eauto.
        rewrite in_map_iff; eexists; split; eauto.
      }
    Qed.

    assert (IsDecidableBinaryPredicate
              (fun (rec1 : Book) (rec2 : Order) => rec1!sISBN = rec2!sISBN)).
    econstructor.
    intros.
    rewrite <- beq_nat_true_iff.
    instantiate (1 := fun a b => _ a!sISBN b!sISBN).
    cbv beta.
    reflexivity. (* congruence here crashes *)

    Lemma CrossProduct' :
      forall {TReturn TRecord1 TRecord2: Type},
      forall (table1: list TRecord1) (table2: list TRecord2) query_body,
      forall bpredicate,
        Equivalent_Ensembles
          (fun retval : TReturn =>
             exists joined_records : TRecord1 * TRecord2,
               List.In joined_records 
                       (Join_Lists 
                          table1 
                          (List.filter 
                             (fun record2 => bpredicate (fst joined_records) record2) table2))
               /\ (query_body (fst joined_records) (snd joined_records) retval))
          (fun retval : TReturn =>
             exists joined_records : TRecord1 * TRecord2,
               List.In joined_records 
                       (flat_map
                          (fun a =>
                             map (fun b => (a, b))
                                 (filter
                                    (fun b => bpredicate a b) table2))
                          table1)
               /\ (query_body (fst joined_records) (snd joined_records) retval)).
    Proof.
      unfold Equivalent_Ensembles, Join_Lists.
      setoid_rewrite flat_map_flatten.
      intros.
      
      split; intro H;
      destruct H as [ rec12 (in_join & qbody) ];

      rewrite in_flatten_iff in in_join;
      destruct in_join as [ seq (in_seq & seq_in_map) ];
      rewrite in_map_iff in seq_in_map;
      destruct seq_in_map as [ rec1' (seq_eq & in1) ];
      subst seq;
      rewrite in_map_iff in in_seq;
      destruct in_seq as [ rec2' (eq_12_1'2' & in_filter) ];
      rewrite <- eq_12_1'2' in *;
      rewrite filter_In in in_filter;
      destruct in_filter as (in2 & pred_satisfied);
      
      eexists;
      rewrite in_flatten_iff;
      (split;
       [ eexists; split; [ | rewrite in_map_iff; eexists ] | eassumption ]; eauto;
       rewrite in_map_iff; eexists; split; eauto; rewrite filter_In; split; tauto
      ).
    Qed.


      Add Parametric Morphism {A B: Type} (seq: list B) :
        (fun pred a => List.filter (fun b => pred a b) seq)
          with signature (pointwise2_relation A B (@eq bool) ==> (pointwise_relation _ (@eq (list B))))
            as filter_morphism_2.
      Proof.
        unfold pointwise_relation, pointwise2_relation.
        intros.
        apply filter_eq_morphism; unfold pointwise_relation; trivial.
      Qed.

    Set Printing All.
    Show.
    
    (* TODO: Look into this 
    Typeclasses Opaque BoundedString Attribute. *)

    hone method "NumOrders". {
      unfold equivalence, UnConstrRelationAbsR, EnsembleListEquivalence_AbsR in H.
      destruct H.

      setoid_rewrite refineEquiv_pick_ex_computes_to_and;
      setoid_rewrite refineEquiv_pick_pair;
      setoid_rewrite refineEquiv_pick_eq';
      simplify with monad laws; cbv beta;
      simpl.

      rewrite Equivalent_UnConstr_In_EnsembleListEquivalence by eassumption.
      setoid_rewrite Equivalent_List_In_Where.

      rewrite (filter_eq_restricted_morphism _ (y := bfind_matcher (Bag := BagProof BookStorage) (Some n, (None, [])))) by (clear; admit).

      rewrite Equivalent_Join_Lists by eassumption.

      setoid_rewrite (@CrossProduct nat Book Order _ _ (fun b1 b2 a => Return b2!sISBN a) (fun (rec1: Book) (rec2: Order) => rec1!sISBN = rec2!sISBN) _).

      setoid_rewrite (@CrossProduct' nat Book Order _ _ (fun b1 b2 a => Return b2!sISBN a)).

      setoid_rewrite flat_map_flatten.
      setoid_rewrite (bfind_correct _). 
      setoid_rewrite <- flat_map_flatten.

      pose proof filter_morphism_2.
      specialize (fun pred => H2 _ _ (benumerate (snd r_n)) (fun (a: Book) (b : Order) => pred a b)  (fun (a: Book) (b: Order) => bfind_matcher (Bag := BagProof OrderStorage) (Some a!sISBN, []) b) ).
      unfold pointwise_relation, pointwise2_relation in H2.

      assert (forall (a : Book) (a' : Order),
                @bool_predicate _ _ _ X a a' = bfind_matcher (Bag := BagProof OrderStorage) (Some a!sISBN, []) a').
      clear; admit.

      specialize (H2 (@bool_predicate _ _ _ X) H3).
      setoid_rewrite H2. 

      (* More morphism needed
      setoid_rewrite flat_map_flatten.
      setoid_rewrite (bfind_correct _). 
      setoid_rewrite <- flat_map_flatten.
       *) 
      Require Import Permutation.
      assert (forall a: Book,
          Permutation
                            (map (fun b : Order => (a, b))
                              (filter
                                 (fun b : Order =>
                                  bfind_matcher (Bag:=BagProof OrderStorage)  (Some a!sISBN, []) b)
                                 (benumerate (Bag:=BagProof OrderStorage) (snd r_n))))
          nil) by (clear; admit).

      assert (
          Permutation 
            (flatten (map
               (fun a : Book =>
                  map (fun b : Order => (a, b))
                      (filter
                         (fun b : Order =>
                            bfind_matcher (Bag:=BagProof OrderStorage)  (Some a!sISBN, []) b)
                         (benumerate (Bag:=BagProof OrderStorage) (snd r_n))))
               (bfind (fst r_n) (Some n, (None, [])))))
            (flatten (map
               (fun a : Book => [])
               (bfind (fst r_n) (Bag:=BagProof BookStorage) (Some n, (None, [])))))).

      Check flatten_map_permutation_permutation_permutation_morphism.

      Unset Ltac Debug.
      setoid_rewrite H4.
      
      apply flatten_map_permutation_permutation_permutation_morphism; eauto.

      

      
            
      setoid_rewrite H4.


      assert ( forall bag (search_term : SearchTermType OrderStorage),
       Permutation (filter (bfind_matcher (Bag:=BagProof OrderStorage) search_term) (benumerate (Bag:=BagProof OrderStorage) bag))
         (bfind (Bag:=BagProof OrderStorage) bag search_term)).
      clear; admit.


      Require Import SetoidList.

      Add Parametric Morphism {A B: Type} (seq: list A) :
        (fun comp => List.map comp seq)
          with signature (pointwise_relation A (@eq B) ==> (@eq (list B)))
            as restricted_map_morphism.
      Proof.
        intros.
        setoid_rewrite H; trivial.
      Qed.

      setoid_rewrite H5.

      Check (bfind_correct (Bag:= BagProof (OrderStorage)) _).
setoid_rewrite (bfind_correct _).
      intros.

      etransitivity.
      

      setoid_rewrite H2.
      setoid_rewrite filter_morphism_2.


      rewrite (filter_morphism).
      
Require Import Setoid.

Typeclasses eauto := debug. (* 5 *)

Goal (forall {A B} (P Q: B -> A -> Prop) (R: B -> Prop), (forall x a, P x a <-> Q x a) -> (refine (For (fun a => exists b, R b /\ P b a)) (For (fun a => exists b, R b /\ Q b a)))).
intros.
setoid_rewrite H.
reflexivity.
Qed.


Show.

      rewrite Equivalent_UnConstr_In_EnsembleListEquivalence by eassumption.
      rewrite Equivalent_List_In_Where.

      unfold dec.

      Show Existentials.

      assert (DecideableEnsemble (fun b : Book => n = b!sAUTHOR)).
      eauto with typeclass_instances.
      
      pose (decider := fun (b: Book) (c: Order) => if eq_nat_dec b!sISBN c!sISBN then true else false).
      assert (forall (b: Book) (c: Order), decider b c = true <-> b!sISBN = c!sISBN) 
        as P_dec
          by (clear; unfold decider; intros; destruct (eq_nat_dec _ _); intuition).

      Lemma Equivalent_List_In_Where' :
        forall (A B C: Type) (l : list C) (P : B -> C -> Prop)
               (bod : B -> C -> Ensemble A) decider (P_dec : forall b c, decider b c = true <-> P b c),
          forall a b c,
            (List.In c l /\ Where (P b c) (bod b c) a) <->
            (List.In c (filter (decider b) l) /\ (bod b c) a).
        unfold Query_Where; intros;
        rewrite filter_In; split; intuition;
        apply P_dec; intuition.
      Qed.

      assert (refine For (fun a : nat =>
                          exists b : Book,
                            List.In b
                                    (filter
                                       (let (dec, _) :=
                                            DecideableEnsemble_EqDec Astring_eq
                                                                     (fun _ : Tuple => n)
                                                                     (fun a0 : Book => a0!sAUTHOR) in
                                        dec) (benumerate (fst r_n))) /\
                            UnConstrQuery_In c Orders
                                             (fun tup : Tuple =>
                                                Where (b!sISBN = tup!sISBN)
                                                      Return tup!sISBN ) a)
                     For (fun a : nat =>
                            exists b : Book,
                              List.In b
                                      (filter
                                         (let (dec, _) :=
                                              DecideableEnsemble_EqDec Astring_eq
                                                                       (fun _ : TupleDef BookStoreSchema sBOOKS => n)
                                                                       (fun a0 : Book => a0!sAUTHOR) in
                                          dec) (benumerate (fst r_n))) /\
                              (exists tup : Order,
                                 List.In tup (filter (decider b) (benumerate (snd r_n))) /\
                                 Return tup!sISBN a))).
      clear H0.

      (*setoid_rewrite Equivalent_UnConstr_In_EnsembleListEquivalence.*)


      About Equivalent_UnConstr_In_EnsembleListEquivalence.
      pose proof (fun bod => @Equivalent_UnConstr_In_EnsembleListEquivalence nat _ c Orders (benumerate (snd r_n)) bod) as equiv. 
      unfold Equivalent_Ensembles in equiv.
      setoid_rewrite (fun bod => equiv bod _).

      Hint Unfold pointwise_relation Equivalent_Ensembles.
      setoid_rewrite Equivalent_UnConstr_In_EnsembleListEquivalence.

 

      etransitivity.

      apply refine_Query_For.
      unfold pointwise_relation; intros.
      apply exists_iff.
      unfold pointwise_relation; intros.

      apply and_iff_compat_l.

      apply Equivalent_UnConstr_In_EnsembleListEquivalence.
      eassumption.

       *)

      apply exists_iff.
      unfold pointwise_relation; intros.

      pose proof (fun P bod decider P_dec => @Equivalent_List_In_Where' nat Book Order (benumerate (snd r_n)) P bod decider P_dec a a0 a1) as specialized.

      apply (specialized (fun book order => book!sISBN = order!sISBN) (fun book order => Return order!sISBN)).
      assumption.
eauto.
      
      setoid_rewrite equiv.

      Lemma ugh : forall (A B B': Prop), (B <-> B') -> (A /\ B <-> A /\ B').
        intros. tauto.
      apply exi


      setoid_rewrite equiv.

      pose proof (fun a b c P bod decider P_dec => @Equivalent_List_In_Where' nat Book Order (benumerate (snd r_n)) P bod decider P_dec a b c) as where''.

      pose proof (fun a b c bod => where'' a b c _ bod decider P_dec) as where'''.

      assert (forall (a: nat) (b: Book), 
                (exists tup : Tuple,
                   List.In tup (benumerate (snd r_n)) /\
                   Where (b!sISBN = tup!sISBN)
                         Return tup!sISBN  a) <->
                (exists tup : Order, 
                   List.In tup (filter (decider b) (benumerate (snd r_n))) 
                   /\ Return tup!sISBN a)) as where''''.
      intros.
      (*setoid_rewrite (fun c => where''' _ _ c _).*)
      setoid_rewrite (fun c => where''' a b c (fun b c a => Return c!sISBN a)).
      reflexivity.
 
      setoid_rewrite where''''.
      reflexivity.

      setoid_rewrite H2.
      unfold decider.

      apply refine_Query_For.

      setoid_rewrite H4.
      
      setoid_rewrite H3.
        
      unfold Query_Where.
      unfold Query_Return.
      pose proof (Equivalent_List_In_Where (A := nat)).
      clear.

      
      

      admit.

      rewrite H2.

      (* TODO: Why doesn't this rewrite work? *)      

      pose proof  (fun (a: Book) => Equivalent_UnConstr_In_EnsembleListEquivalence c _ (fun tup0 : Order =>
                      Where (a!sISBN = tup0!sISBN)
                      Return tup0!sISBN) H1).





Add Parametric Morphism {A: Type} {h1: Heading}
    qsSchema qs R P
:
  (fun (bod: Tuple -> Tuple -> Ensemble A) => Query_For (fun a => exists (b: @Tuple h1), (P b) /\ @UnConstrQuery_In qsSchema qs A R (bod b) a))
    with signature ((pointwise2_relation (@Tuple h1) (@Tuple _) (@Equivalent_Ensembles A) ==> refine ))
      as refine_Query_For_In_Equivalent.
Proof.
  admit.
Qed.



Add Parametric Morphism {A: Type} {h1: Heading}
     P
:
  (fun (Q: Tuple -> Ensemble A) => Query_For (fun a => exists (b: @Tuple h1), (P b) /\ (Q b a)))
    with signature ((pointwise_relation (@Tuple _) (@Equivalent_Ensembles A) ==> refine ))
      as refine_Query_For_In_Equivalent'.
Proof.
  admit.
Qed.

Show.

assert (forall {A qsSchema} heading c orders f, pointwise_relation (@Tuple heading) Equivalent_Ensembles
                                            (fun b => fun a => UnConstrQuery_In (A := A) (qsSchema := qsSchema) c orders (f b) a)
                                            (fun b => fun a => True)) by (clear; admit).

Typeclasses eauto := debug. (* 5 *)

pose proof (H3 nat _ _ c Orders (fun (b: @Tuple
               (schemaHeading
                  (relSchema
                     (@nth_Bounded NamedSchema string relName
                        (qschemaSchemas BookStoreSchema) Books)))) tup => Where (b!sISBN = tup!sISBN)
        Return tup!sISBN)).

(*Focus 2.*)

About refine_Query_For_In_Equivalent'.
set (a := benumerate (fst r_n)).
rewrite refine_Query_For_In_Equivalent.
rewrite (refine_Query_For_In_Equivalent' (fun b => List.In b (filter dec a)) H4).



setoid_rewrite H4.

      setoid_rewrite H2.  (fun a => Equivalent_UnConstr_In_EnsembleListEquivalence).

 
rewrite H2.

      assert (
          forall aa,
            Equivalent_Ensembles
              (UnConstrQuery_In c (BookStoreSchema / sORDERS)
                                (fun tup0 : Order =>
                                   Where (aa = tup0!sISBN)
                                         Return tup0!sISBN ))
              (fun
                  a : _ =>
                  exists tup : Tuple,
                    List.In tup (benumerate (snd r_n)) /\
                    (fun tup0 : Order =>
                       Where (aa = tup0!sISBN)
                             Return tup0!sISBN ) tup a)).
      clear H0; admit.

       setoid_rewrite H2.

      rewrite (filter_by_equiv _ (bfind_matcher (Bag := BagProof BookStorage) (Some n, (None, [])))) by (clear; admit).

      setoid_rewrite (bfind_correct _).
      assert (forall a b, a/\ b <-> b /\ a) as sym by (clear H0; admit).
*)
      About Equivalent_Join_Lists.
      
 
      Lemma Equivalent_Join_Lists' :
        forall (A B : Type) (qsSchema : QueryStructureSchema)
               (qs : UnConstrQueryStructure qsSchema) (R : BoundedString) 
               (l : list B) (l' : list Tuple) (bod : B -> Tuple -> Ensemble A),
          EnsembleListEquivalence (GetUnConstrRelation qs R) l' ->
          Equivalent_Ensembles
            (fun a : A => exists b : B, List.In b l /\ UnConstrQuery_In qs R (bod b) a)
            (fun a : A =>
               exists b : B * Tuple, List.In b (Join_Lists l l') /\ bod (fst b) (snd b) a).
        admit.
      Qed.
      
      rewrite Equivalent_Join_Lists by eassumption.


      assert (forall {A} (seq: list (list A)), SetEq (fold_left (@app A) seq []) (flatten seq)) by (clear; admit).

      assert (
          Equivalent_Ensembles
            (fun a : nat =>
               exists b : Book * Order,
                 List.In b
                         (Join_Lists (bfind (fst r_n) (Some n, (None, [])))
                                     (benumerate (snd r_n))) /\
                 Where ((fst b)!sISBN = (snd b)!sISBN)
                       Return (snd b)!sISBN  a)
            (fun a => 
               exists b : Book * Order,
                 let snd_db := (benumerate (snd r_n)) in
                 List.In b
                         (flatten
                            (map
                               (fun a0 : Book =>
                                  map (fun b0 : Order => (a0, b0)) (filter (fun (b0: Order) => beq_nat a0!sISBN b0!sISBN) snd_db)
                               )
                               (bfind (fst r_n) (Some n, (None, []))))) /\
                         Return (snd b)!sISBN  a)
        ).
      clear; admit.


      setoid_rewrite H3.

      clear sym H2 H3.
      Check filter_by_equiv.
      rewrite (filter_by_equiv _ (bfind_matcher (Bag := BagProof OrderStorage) (Some _, []))). by (clear; admit).


      unfold Join_Lists.
      setoid_rewrite H2.


      setoid_rewrite H2.
      setoid_rewrite in_flatten_iff.
      setoid_rewrite in_map_iff.
      rewrite flatten_filter.

      unfold Join_Lists.
Show.
      
      
      setoid_rewrite Equivalent_List_In_Where.
      unfold Join_Lists.

      unfold dec. unfold DecideableEnsemble_EqDec.

      rewrite (filter_by_equiv _ (bfind_matcher (Bag := BagProof BookStorage) (Some n, (None, [])))) by (clear; admit).

      SearchAbout filter flatten.

      rewrite filter

      rewrite (filter_by_equiv _ (bfind_matcher (Bag := BagProof BookStorage) (Some n, (None, [])))) by (clear H0; admit). (* TODO: Handle strings in prove_observational_eq, and use rewrites *)

      setoid_rewrite (bfind_correct _).


      setoid_rewrite refine_For_List_Return.
      simplify with monad laws.

      unfold equivalence.
      rewrite refine_pick_val by eauto. 
      simplify with monad laws.
      finish honing.
    }
      


    (* Step 2: We first swap the order of the 'For's to make the
         implementation more efficient. *)


    (* Step 3: Switch to an implementation of the representation
       type as a pair of lists of tuples. *)

    implement using lists under BookStoreListImpl_SiR.

    (* Step 4: Profit. :) *)

    finish sharpening.
  Defined.
End BookStoreExamples.
