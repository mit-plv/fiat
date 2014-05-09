Require Import String Omega List FunctionalExtensionality Ensembles.

Ltac typeof' pf := type of pf.
Ltac simpl_typeof pf := cbv delta in (type of pf).

Require Import Computation ADT ADTRefinement ADT.Pick
        ADTRefinement.BuildADTRefinements ADTNotation
        QueryStructureSchema QueryQSSpecs InsertQSSpecs QueryStructure.

Generalizable All Variables.
Set Implicit Arguments.

Section BookStoreExamples.

  Arguments Tuple [Heading] .
  Arguments BoundedString [_].

  (* Our bookstore has two relations (tables):
     - The books in the inventory
     - The orders that have been placed *)

Open Scope QSSchema.

  Definition BookStoreSchema :=
    query structure schema
      [ relation "Books" has
                schema <"Author" : string,
                        "Title" : string,
                        "ISBN" : nat>
                where attributes ["Title"; "Author"] depend on ["ISBN"];
        relation "Orders" has
                schema <"ISBN" : nat,
                        "Date" : nat> ]
      enforcing [attribute "ISBN" of "Orders" references "Books"].

Definition Books := GetRelationKey BookStoreSchema "Books".
Definition Orders := GetRelationKey BookStoreSchema "Orders".

Definition Author := GetAttributeKey Books "Author".
Definition Title := GetAttributeKey Books "Title".
Definition ISBN := GetAttributeKey Books "ISBN".

Definition oISBN := GetAttributeKey Orders "ISBN".
Definition Date := GetAttributeKey Orders "Date".


  (* Sanity check to show that the definitions produced
     can be efficiently evaluated. *)
  Goal (forall b,
          BuildQueryStructureConstraints
            BookStoreSchema Orders Books = b).
  Time simpl.
  Abort.

  Definition BookStoreRefRep := QueryStructure BookStoreSchema.

  Definition BookSchemaHeading :=
    QSGetNRelSchemaHeading BookStoreSchema Books.
  Definition OrderSchemaHeading :=
    QSGetNRelSchemaHeading BookStoreSchema Orders.

  Definition Book := @Tuple BookSchemaHeading.
  Definition Order := @Tuple OrderSchemaHeading.

  (* Our bookstore has two mutators:
     - [PlaceOrder] : Place an order into the 'Orders' table
     - [AddBook] : Add a book to the inventory

     Our bookstore has two observers:
     - [GetTitles] : The titles of books written by a given author
     - [NumOrders] : The number of orders for a given author
   *)

  Local Open Scope ADTSig_scope.
  Local Open Scope QueryStructureParsing_scope.
  Local Open Scope Schema.
  Local Open Scope QuerySpec.

  Definition PlaceOrder := "P"%string.
  Definition AddBook := "A"%string.
  Definition GetTitles := "G"%string.
  Definition NumOrders := "N"%string.

  Definition BookStoreSig : ADTSig :=
    ADTsignature {
        PlaceOrder : rep × Order → rep,
        AddBook : rep × Book → rep ;
        GetTitles : rep × string → list string,
        NumOrders : rep × string → nat
      }.

  Definition BookStoreSpec : ADT BookStoreSig :=
    QueryADTRep BookStoreRefRep {
             (* [PlaceOrder] : Place an order into the 'Orders' table *)
                  def update PlaceOrder ( o : Order ) : rep :=
                    Insert o into Orders,

             (* [AddBook] : Add a book to the inventory *)
             def update AddBook ( b : Book ) : rep :=
                 Insert b into Books ;

             (* [GetTitles] : The titles of books written by a given author *)
             def query GetTitles ( author : string ) : list string :=
               For (b in Books)
               Where (author = b!Author)
               Return (b!Title),

             (* [NumOrders] : The number of orders for a given author *)
             def query NumOrders ( author : string ) : nat :=
                 Count (For (o in Orders) (b in Books)
                        Where (author = b!Author)
                        Where (b!ISBN = o!oISBN)
                        Return o!oISBN)
         } .

  Local Close Scope QueryStructureParsing_scope.
  Local Close Scope QuerySpec.
  Local Open Scope QueryStructure_scope.

  Open Scope updateDef.

  Require Import ProcessScheduler.AdditionalLemmas SetEq.

  Lemma refine_SetEq_self {A} :
    forall l : list A,
      refine {l' | SetEq l' l}%comp
             (ret l).
  Proof.
    unfold SetEq, refine; intros; inversion_by computes_to_inv.
    econstructor; subst; split; eauto.
  Qed.

  Definition Equivalent_Ensembles {A : Type}
             (P Q : Ensemble A) := forall a, P a <-> Q a.

  Lemma Equivalent_In_EnsembleListEquivalence {A}
        (qs : QueryStructureHint) (R : _)
        (l : list _)
        bod
  : EnsembleListEquivalence (GetRelation qsHint R) l ->
    Equivalent_Ensembles
      (@Query_In qs A R bod)
      (fun a => exists tup, List.In tup l /\ bod tup a).
  Proof.
    split; intros; unfold In in *.
    destruct H0; eexists; intuition; eauto.
    eapply H; eauto.
    destruct H0; intuition; eexists; split; eauto.
    eapply H; eauto.
  Qed.

  Definition Join_Lists {A B}
             (l : list A)
             (l' : list B)
  : list (A * B) :=
    fold_left (@app _) (map (fun a => map (fun b => (a, b)) l') l) nil.

  Lemma In_fold_left_app {A}
  : forall (l : list (list A))
           (l'' : list A)
           (a : A),
      List.In a (fold_left (@app _) l l'') <->
      (List.In a l'' \/ (exists l', List.In l' l /\ List.In a l')).
  Proof.
    induction l; simpl; intuition.
    destruct_ex; intuition.
    destruct (proj1 (IHl _ _) H).
    apply in_app_or in H0; intuition; eauto.
    destruct_ex; intuition; eauto.
    eapply IHl; eauto using in_or_app.
    destruct_ex; intuition; subst; eauto.
    eapply IHl; eauto using in_or_app.
    eapply IHl; eauto using in_or_app.
  Qed.

  Lemma In_Join_Lists {A B}
  : forall (l : list A)
           (l' : list B)
           (a : A)
           (b : B),
      List.In (a, b) (Join_Lists l l') <->
      (List.In a l /\ List.In b l').
  Proof.
    unfold Join_Lists; split; intros.
    apply In_fold_left_app in H; simpl in *; intuition;
    destruct_ex; intuition;
    apply in_map_iff in H0; destruct_ex; intuition; subst;
    apply in_map_iff in H1; destruct_ex; intuition; subst;
    simpl; congruence.
    intuition.
    apply In_fold_left_app; right.
    exists (map (fun b : B => (a, b)) l'); split;
    apply in_map_iff; eexists; intuition; eauto.
  Qed.

  Lemma Equivalent_Join_Lists {A B}
        (qs : QueryStructureHint) (R : _)
        (l : list B)
        (l' : list _)
        bod
  : EnsembleListEquivalence (GetRelation qsHint R) l' ->
    Equivalent_Ensembles
      (fun a => exists b, List.In b l /\
                            (@Query_In qs A R (bod b) a))
      (fun a => exists b, List.In b (Join_Lists l l') /\
                          (bod (fst b) (snd b) a)).
  Proof.
    split; intros; unfold In in *.
    - destruct H0; intuition; destruct H2; eexists; intuition; eauto.
      unfold EnsembleListEquivalence in H.
      apply In_Join_Lists; split; eauto.
      eapply H; unfold In; apply H2.
      simpl; auto.
    - destruct_ex; intuition; destruct x; eexists; intuition.
      eapply (In_Join_Lists l l'); eauto.
      unfold Query_In; eexists; intuition; eauto.
      apply H; eapply (In_Join_Lists l l'); eauto.
  Qed.

  Lemma Equivalent_List_In_Where {A B}
        (l : list B)
        (P : Ensemble B)
        (bod : B -> Ensemble A)
        (cond : B -> bool)
        : (forall a, cond a = true <-> P a)
          ->
    Equivalent_Ensembles
      (fun a : A => exists b, List.In b l /\ Query_Where (P b) (bod b) a)
      (fun a : A => exists b, List.In b (filter cond l) /\ (bod b) a)
  .
  Proof.
    split; intros; unfold In, Query_Where in *.
    destruct H0; eexists; intuition; eauto.
    eapply filter_In; split; eauto.
    eapply H; eauto.
    destruct H0; intuition; eexists; split; eauto.
    eapply filter_In; eauto.
    intuition; eauto using filter_In.
    eapply H; eapply filter_In; eauto.
  Qed.

  Lemma Equivalent_Swap_In {A}
        (qs : QueryStructureHint) (R R' : _)
        (bod : Tuple -> Tuple -> Ensemble A)
  :
    Equivalent_Ensembles
      (@Query_In qs _ R (fun tup => @Query_In qs _ R' (bod tup)))
      (@Query_In qs _ R' (fun tup => @Query_In qs _ R
                                               (fun tup' => bod tup' tup))).
  Proof.
    unfold Equivalent_Ensembles, Query_In; split; intros;
    repeat (progress (destruct_ex; intuition)); eexists;
    split; eauto.
  Qed.

  Lemma Equivalent_Swap_In_Where {A}
        (qs : QueryStructureHint) (R : _)
        {heading}
        (bod : @Tuple heading -> Tuple -> Ensemble A)
        (P : @Tuple heading -> Prop)
  :
    pointwise_relation
      Tuple Equivalent_Ensembles
      (fun tup' : Tuple =>
         (@Query_In qs _ R
                    (fun tup => Query_Where (P tup') (bod tup' tup))))
      (fun tup' : Tuple =>
         Query_Where (P tup') (@Query_In qs _ R (bod tup'))).
  Proof.
    unfold Equivalent_Ensembles, Query_In, Query_Where; split; intros;
    repeat (progress (destruct_ex; intuition)); eexists;
    split; eauto.
  Qed.

  Lemma refine_For_List_Return {A B}
        (l : list B)
        (extract : B -> A)
  : refine
      (For (fun a : A =>
              exists b : B,
                List.In b l /\ Return (extract b) a))%QuerySpec
      (ret (map extract l)).
  Proof.
    unfold refine; intros; inversion_by computes_to_inv; subst.
    econstructor; unfold In, Query_Return; split; intros.
    eapply in_map_iff in H; destruct_ex; intuition; eauto.
    eapply in_map_iff; destruct_ex; intuition; eauto.
  Qed.

  Add Parametric Morphism {A: Type} :
    (Query_For)
      with signature (@Equivalent_Ensembles A ==> refine)
        as refine_Query_For_Equivalent.
  Proof.
    unfold impl, Query_For, refine; intros.
    inversion_by computes_to_inv.
    econstructor; split_iff; split; intros; eauto.
    apply H; apply H1; auto.
    apply H2; apply H; auto.
  Qed.

  Add Parametric Morphism {A: Type}
      (qs : QueryStructureHint) (R : _)
  :
    (fun bod => Query_For (@Query_In qs _ R bod))
      with signature ((pointwise_relation Tuple (@Equivalent_Ensembles A) ==> refine ))
        as refine_Query_For_In_Equivalent.
  Proof.
    unfold impl, Query_For, pointwise_relation, Query_In, In, refine.
    intros; inversion_by computes_to_inv.
    econstructor; split_iff; split; intros; eauto.
    destruct (H1 _ H0); eexists; intuition; eauto.
    apply H; auto.
    destruct_ex; apply H2; eexists; intuition; eauto.
    apply H; auto.
  Qed.

  Lemma tupleAgree_refl :
    forall (h : Heading)
           (tup : @Tuple h)
           (attrlist : list (Attributes h)),
      tupleAgree tup tup attrlist.
  Proof.
    unfold tupleAgree; auto.
  Qed.

  Lemma refine_tupleAgree_refl_True :
    forall (h : Heading)
           (tup : @Tuple h)
           (attrlist attrlist' : list (Attributes h)),
      refine {b |
              decides b (tupleAgree tup tup attrlist'
                         -> tupleAgree tup tup attrlist)}
             (ret true).
  Proof.
    unfold refine; intros; inversion_by computes_to_inv.
    subst; econstructor; simpl; auto using tupleAgree_refl.
  Qed.

  Definition decideable_Heading_Domain
             (h : Heading) :=
    forall (idx : Attributes h)
           (t t' : Domain h idx), {t = t'} + {t <> t'}.

  Fixpoint Tuple_Agree_dec
             (h : Heading)
             (h_dec_eq : decideable_Heading_Domain h)
             (attrlist : list (Attributes h))
  : forall (tup tup' : Tuple),
      {tupleAgree tup tup' attrlist} + {~tupleAgree tup tup' attrlist}.
  Proof.
  Admitted.

  Lemma BookSchemaHeading_dec 
    : decideable_Heading_Domain BookSchemaHeading.
  Proof.
  Admitted.

  Fixpoint Check_List_Prop {A}
           (cond : A -> bool)
           (l : list A)
  : bool :=
    match l with
        | [] => true
        | a :: l' => if (cond a) then
                          Check_List_Prop cond l'
                        else false
    end.

  Definition In_List_Key 
           (h : Heading)
           (h_dec_eq : decideable_Heading_Domain h)
           (attrlist : list (Attributes h))
           (tup : Tuple)
           (l : list Tuple) :=
    Check_List_Prop (fun tup' => 
                       if (Tuple_Agree_dec h_dec_eq attrlist tup tup')
                       then true
                       else false) l.

  Lemma refine_unused_key_check
  : forall (h : Heading)
           (h_dec_eq : decideable_Heading_Domain h)
           (attrlist attrlist' : list (Attributes h))
           (tup : Tuple)
           (rel : Ensemble Tuple)
           (l : list Tuple),
      EnsembleListEquivalence rel l
      -> refine {b | decides b
                             (forall tup' : Tuple,
                                rel tup' ->
                                tupleAgree tup tup' attrlist' ->
                                tupleAgree tup tup' attrlist)}
                (ret (In_List_Key h_dec_eq attrlist tup l)).
  Admitted.

  Lemma refine_unused_key_check'
  : forall (h : Heading)
           (h_dec_eq : decideable_Heading_Domain h)
           (attrlist attrlist' : list (Attributes h))
           (tup : Tuple)
           (rel : Ensemble Tuple)
           (l : list Tuple),
      EnsembleListEquivalence rel l
      -> refine {b | decides b
                             (forall tup' : Tuple,
                                rel tup' ->
                                tupleAgree tup' tup attrlist' ->
                                tupleAgree tup' tup attrlist)}
                (ret (In_List_Key h_dec_eq attrlist tup l)).
  Admitted.

  Lemma refine_foreign_key_check 
  : forall (h : Heading)
           (rel : Ensemble Tuple)
           (l : list Tuple)
           (P : Ensemble Tuple)
           (cond : Tuple -> bool),
      EnsembleListEquivalence rel l
      -> refine {b  |
                 decides b
                         (exists tup' : @Tuple h,
                            rel tup' /\
                            P tup')}
                (ret (Check_List_Prop cond l)).
    Admitted.

  Lemma refine_pick_eq_ex_bind {A B : Type}
        (P : A -> B -> Prop)
        (a : A)
  : refine (a' <- {a' | a' = a /\ exists b, P a' b};
            {b | P a' b})
           {b | P a b}.
  Proof.
    unfold refine; intros; inversion_by computes_to_inv;
    econstructor; eauto.
  Qed.

  Lemma refine_under_if {A B} 
        (P : A -> B -> Prop) : 
    forall (cond : bool) (ta ea : A) ta' ea', 
      refine {b | P ta b} ta'
      -> refine {b | P ea b} ea'
      -> refine {b | P (if cond then ta else ea) b}
                (if cond then ta' else ea').
  Proof.
    intros; destruct cond; eauto.
  Qed.

  Lemma refine_if_ret {A}
  : forall (cond : bool) (ta ea : A), 
      refineEquiv (ret (if cond then ta else ea))
                  (if cond then ret ta else ret ea).
  Proof.
    split; destruct cond; reflexivity.
  Qed.

  Definition BookStoreListImpl_SiR or (nr : (list Book) * (list Order)) : Prop :=
    (EnsembleListEquivalence (GetUnConstrRelation or Books) (fst nr))
    /\ (EnsembleListEquivalence (GetUnConstrRelation or Orders) (snd nr)).

  Definition BookStore :
    Sharpened BookStoreSpec.
  Proof.
    unfold BookStoreSpec.

    hone representation' using (@DropQSConstraints_SiR _).

    (* Step 1: Decide what to do when inserting a book that
       violates the key constraints of Books. I think
       we will leave table unchanged when a 'bad' book is
       inserted. *)
    hone' mutator PlaceOrder.
    {
      setoid_rewrite refineEquiv_pick_eq'.
      simplify with monad laws.
      apply refine_pick_forall_Prop with
      (P := fun r_n or (n' : _) => _).
      intros; setoid_rewrite QSInsertSpec_UnConstr_refine; simpl; eauto.
      setoid_rewrite decides_True.
      setoid_rewrite decides_3_True.
      (* This takes 24 seconds on my machine.
         The term size isn't the problem, as non of the goals
         along the way are particularly large.

         Time (setoid_rewrite refineEquiv_bind_unit;
         setoid_rewrite refineEquiv_bind_unit;
         setoid_rewrite refineEquiv_bind_unit;
         setoid_rewrite refineEquiv_bind_unit) *)
      simplify with monad laws.
      unfold If_Then_Else; simpl.
      setoid_rewrite refine_if_bool_eta.
      simplify with monad laws.
      unfold SatisfiesSchemaConstraints; simpl; intros.
      setoid_rewrite decides_2_True.
      simplify with monad laws.
      finish honing.
    }
    (* Step 2: Decide what to do when adding an order that
       violates foreign key constraints of Orders. *)
    hone' mutator AddBook.
    {
      setoid_rewrite refineEquiv_pick_eq'.
      simplify with monad laws.
      apply refine_pick_forall_Prop with
      (P := fun r_n or (n' : _) => _).
      intros; setoid_rewrite QSInsertSpec_UnConstr_refine; simpl; eauto.
      setoid_rewrite decides_True.
      setoid_rewrite decides_3_True.
      setoid_rewrite refineEquiv_bind_unit.
      unfold If_Then_Else; simpl.
      setoid_rewrite refine_if_bool_eta.
      simplify with monad laws.
      unfold SatisfiesSchemaConstraints; simpl; intros.
      rewrite refine_tupleAgree_refl_True.
      simplify with monad laws.
      remove_trivial_insertion_constraints r_n n Orders Books oISBN ISBN H0.
      finish honing.
    }

    hone representation' using BookStoreListImpl_SiR.

    (* honing Get Titles. *)
    hone' observer GetTitles using _.
    { intros; subst.
      set_evars; cbv delta [obsCod obsDom observerMethodType] beta in H; simpl in H.
      apply refine_pick_forall_Prop with
      (P := fun r_n or (n' : list string) => _).
      intros; rewrite refine_pick_computes_to.
      apply refine_pick_forall_Prop with
      (P := fun r_n or (n' : list string) => _).
      destruct H0; unfold DropQSConstraints_SiR; intros; subst.
      intros; rewrite refine_pick_computes_to.
      repeat rewrite GetRelDropConstraints in *.
      setoid_rewrite Equivalent_In_EnsembleListEquivalence; simpl; eauto.
      setoid_rewrite Equivalent_List_In_Where with
      (cond := fun (a0 : Book) => if (string_dec (GetAttribute a0 Author) n) then true else false); simpl.
      rewrite refine_For_List_Return.
      unfold H; exact (reflexivity _).
      intros; destruct (string_dec (a!Author)%Tuple n); split; intros;
      auto; congruence.
    }

    (* honing Num Orders *)

    hone' observer NumOrders using _.
    {
      intros; subst.
      set_evars; cbv delta [obsCod obsDom observerMethodType] beta in H; simpl in H.
      apply refine_pick_forall_Prop with
      (P := fun r_n or (n' : _) => _).
      intros; rewrite refine_pick_computes_to.
      apply refine_pick_forall_Prop with
      (P := fun r_n or (n' : _) => _).
      unfold Count, DropQSConstraints_SiR; destruct H0; intros; subst.
      repeat rewrite GetRelDropConstraints in *.
      rewrite refine_pick_computes_to; eauto.
      rewrite Equivalent_Swap_In.
      rewrite refine_Query_For_In_Equivalent;
        [ | apply Equivalent_Swap_In_Where with (qs := _)].
      setoid_rewrite Equivalent_In_EnsembleListEquivalence; eauto.
      setoid_rewrite Equivalent_List_In_Where with
      (cond := fun a =>
                 if (string_dec (a!Author)%Tuple n)
                 then true
                 else false); simpl.
      setoid_rewrite Equivalent_Join_Lists; eauto.
      setoid_rewrite Equivalent_List_In_Where with
      (cond := fun ab =>
               if (eq_nat_dec ((fst ab)!ISBN)%Tuple
                              ((snd ab)!oISBN)%Tuple)
               then true else false); simpl.
    rewrite refine_For_List_Return.
    simplify with monad laws.
    unfold H; exact (reflexivity _).
    { intros; destruct (eq_nat_dec ((fst a)!ISBN)%Tuple ((snd a)!oISBN)%Tuple);
      split; intros; auto; congruence. }
    { intros; destruct (string_dec (a!Author)%Tuple n); split; intros;
    auto; congruence. }
    }

    hone' mutator AddBook.
    {
      setoid_rewrite refineEquiv_pick_eq'.
      setoid_rewrite refineEquiv_unit_bind.
      apply refine_pick_forall_Prop with
      (P := fun r_n or (b : _)  => _).
      setoid_rewrite refineEquiv_split_ex.
      setoid_rewrite refineEquiv_pick_computes_to_and.
      simplify with monad laws.
      unfold SatisfiesSchemaConstraints; simpl; intros.
      destruct H0.
      setoid_rewrite refine_unused_key_check with 
      (h_dec_eq := BookSchemaHeading_dec ); eauto.
      simplify with monad laws. 
      setoid_rewrite refine_unused_key_check' with
      (h_dec_eq := BookSchemaHeading_dec ); eauto.
      simplify with monad laws.
      rewrite refine_pick_eq_ex_bind.
      rewrite refine_under_if with (ea' := ret r_n); 
        [ | reflexivity |
          econstructor; inversion_by computes_to_inv; subst; 
          constructor; eauto] .


      Add Parametric Morphism {A: Type} (b : bool):
        (If_Then_Else b)
          with signature (
            @refine A ==> @refine A ==> refine)
            as refine_refine_if.
      Proof.
        unfold refine, If_Then_Else; intros.
        destruct b; eauto.
      Qed.

      apply refine_refine_if; [ | reflexivity ].

      apply refine_under_if with (ea' := ret r_n); 
        [ | econstructor; inversion_by computes_to_inv; subst; 
          constructor; eauto] .
      unfold BookStoreListImpl_SiR; 
        unfold GetUnConstrRelation, ith_Bounded; simpl.
      erewrite refine_pick with (c := ret (n :: fst r_n, snd r_n)).
      reflexivity.
      intros x H3; apply computes_to_inv in H3; subst; eauto.
      unfold GetUnConstrRelation, ith_Bounded,
      EnsembleListEquivalence, RelationInsert, In in *; simpl in *;
      split; intuition; eauto.
      right; eapply H0; eauto.
      right; eapply H0; eauto.
    }

    hone' mutator PlaceOrder.
    {
      setoid_rewrite refineEquiv_pick_eq'.
      setoid_rewrite refineEquiv_unit_bind.
      apply refine_pick_forall_Prop with
      (P := fun r_n or (b : _)  => _).
      setoid_rewrite refineEquiv_split_ex.
      setoid_rewrite refineEquiv_pick_computes_to_and.
      simplify with monad laws.
      intros.
      destruct H0; rewrite refine_foreign_key_check
                   with (cond := fun a =>
                                   if (eq_nat_dec (a!ISBN)%Tuple (n!oISBN)%Tuple)
                                   then true
                                   else false)

; eauto.
      simplify with monad laws.
      rewrite refine_pick_eq_ex_bind.
      rewrite refine_under_if with (ea' := ret r_n); 
        [ | reflexivity |
          econstructor; inversion_by computes_to_inv; subst; 
          constructor; eauto] .
      apply refine_refine_if; [ | reflexivity ].
      unfold BookStoreListImpl_SiR; 
        unfold GetUnConstrRelation, ith_Bounded; simpl.
      erewrite refine_pick with (c := ret (fst r_n, n :: snd r_n)).
      reflexivity.
      intros x H3; apply computes_to_inv in H3; subst; eauto.
      unfold GetUnConstrRelation, ith_Bounded,
      EnsembleListEquivalence, RelationInsert, In in *; simpl in *;
      split; intuition; eauto.
      right; eapply H1; eauto.
      right; eapply H1; eauto.
    }      

    (* Step 4: Profit. :)*)

    finish sharpening. 
  Defined.

    (* Alternate 'simple' steps. *)
    (* Step 3: Add the '#Orders' attribute to Books schema. *)


    (* Step 3.1: Hone GetTitles to ignore the new field. *)
    (* Step 3.2: Hone AddBook to set '#Orders' to 0. *)
    (* Step 3.3: Hone PlaceOrder to increment '#Orders'. *)
    (* Step 3.4: Hone NumOrders to use said field. *)

    (* Step 4: Switch to implementation of Books to a
               hashmap from authors to lists of titles. *)
    (* Step 4.1: Update mutators *)
    (* Step 4.2: Update observers *)

  (* Definition BookStoreSchema' :=
    query structure schema
      [ relation "Books" has
                schema <"Author" : string,
                        "Title" : string,
                        "ISBN" : nat,
                        "#Orders" : nat>
                where attributes ["Title" ; "Author"] depend on ["ISBN"];
        relation "Orders" has
                schema <"ISBN" : nat,
                        "Date" : nat> ]
      enforcing [attribute "ISBN" of "Orders" references "Books"]. *)

  (*Definition AddAttribute_SiR
             (or : BookStoreRefRep)
             (nr : QueryStructure BookStoreSchema') :=
    (GetRelation or Orders = GetRelation nr Orders /\
     GetRelation or Books = map (fun tup => <"Author" : tup!Author,
                                             "Title" : tup!Title,
                                             "ISBN" : tup!ISBN>%Tuple)
                                (GetRelation nr Books)). *)


  (* Definition Ref_SiR
             (or : BookStoreRefRep)
             (nr : list Book * list Order) :=
    (forall o : Order, List.In o (snd nr)  (or 's Orders) rel' /\ rel rel' o) /\
    (forall b : Book, List.In b (fst nr) <-> exists rel', (or 's Books) rel' /\ rel rel' b). *)

  (* Still need to reimplement specs using a better query notation.

  Definition PlaceOrderSpec
             (r : BookStoreRefRep) (n : nat) (r' : BookStoreRefRep) :=
    (* The Book tables are the same. *)
    Books r = Books r'
    (* If the ordered book is in the inventory (i.e. is a foreign
            key), the updated set of orders is a subset of the
            original set of orders. *)
    /\
    forall b,
      In (Books r) b /\ ISBN b = n ->
      Orders r' = @cons Order n (Orders r).

  Definition AddBookSpec
             (r : BookStoreRefRep) (b : Book) (r' : BookStoreRefRep) :=
         (* The Order tables are the same.*)
         Orders r = Orders r'
         (* If the new book's ISBN isn't already in the inventory,
            the updated set of books now includes it
            (i.e. ISBN is a primary key). *)
         /\
         (forall b', ISBN b = ISBN b' -> ~ In (Books r) b') ->
         Books r' = union (Books r) (Coq.Sets.Uniset.Singleton _ Book_eq_dec b).

  Definition GetTitlesSpec
             (r : BookStoreRefRep) (author : string) (titles : list string) :=
         (* Every element in the returned list iff a corresponding book
            in the original inventory. *)
         forall title, List.In title titles <->
                       exists b, In (Books r) b /\ Title b = title.

  Inductive NumOrdersSpec
  : BookStoreRefRep -> string -> nat -> Prop :=
    numOrderSpec :
      forall inventory author (l : list nat) (f : Order -> bool),
        (* The number of orders for a *)
        (forall o, f o = true <->
                   exists book, In (Books inventory) book
                              /\ ISBN book = oISBN o
                              /\ Author book = author) ->
        NumOrdersSpec inventory author
                      (length (filter f (Orders inventory))).

  Definition BookStorePick : ADT BookStoreSig :=
    ADTRep BookStoreRefRep {
             def mut "PlaceOrder" ( r : rep , n : nat ) : rep :=
               {r' | PlaceOrderSpec r n r'},
             def mut AddBook ( r : rep , b : Book ) : rep :=
               {r' | AddBookSpec r b r'} ;
             def obs GetTitles ( r : rep , author : string ) : (list string) :=
               {titles | GetTitlesSpec r author titles} ,
             def obs NumOrders ( r : rep , author : string ) : nat :=
               {numtitles | NumOrdersSpec r author numtitles}
         } .

Definition Ref_SiR
           (or : BookStoreRefRep)
           (nr : list Book * list Order) :=
  List.incl (snd nr) (Orders or) /\ (* The orders in the new rep are a subset
                                           of the orders in the old rep. *)
  List.incl (Orders or) (snd nr) /\ (* and vice-versa. *)
  forall b, In (Books or) b <-> List.In b (fst nr).

  Definition BookStore :
    Sharpened BookStorePick.
  Proof.
    hone representation' using Ref_SiR.
  Admitted. *)

End BookStoreExamples.
