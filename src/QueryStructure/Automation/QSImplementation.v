(* Tactics for extracting Query Structure Implementations. *)
Require Import Coq.Strings.String.
Require Export
ADTSynthesis.Common.i2list2
ADTSynthesis.QueryStructure.Implementation.DataStructures.Bags.BagsOfTuples
ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureNotations
ADTSynthesis.QueryStructure.Automation.AutoDB.

Ltac list_of_evar B As k :=
  match As with
    | nil => k (@nil B)
    | cons ?a ?As' =>
      makeEvar B ltac:(fun b =>
                         list_of_evar
                           B As' ltac:(fun Bs => k (cons b Bs)))
  end.

Definition LookupQSDelegateReps
           {schemas : list NamedSchema}
           (Reps : ilist (fun ns => Type) schemas)
           (idx : @BoundedString (map relName schemas))
: Type := ith_Bounded relName Reps idx.

Definition LookupQSDelegateImpls
           {schemas : list NamedSchema}
           (SearchTerms : ilist (fun ns => SearchUpdateTerms (schemaHeading (relSchema ns))) schemas)
           (Reps : ilist (fun ns => Type) schemas)
           (DelegateImpls :
              i2list2 (fun ns (SearchTerm : SearchUpdateTerms (schemaHeading (relSchema ns)))
                           (Rep : Type)=>
                         ComputationalADT.pcADT
                           (BagSig (@Tuple (schemaHeading (relSchema ns)))
                                   (BagSearchTermType SearchTerm)
                                   (BagUpdateTermType SearchTerm))
                           Rep) SearchTerms Reps)
: forall (idx : @BoundedString (map relName schemas)),
    ComputationalADT.pcADT
      (Build_IndexedQueryStructure_Impl_Sigs SearchTerms idx)
      (LookupQSDelegateReps Reps idx) := i2th2_Bounded relName DelegateImpls.

Ltac BuildQSDelegateSigs QSImpl :=
      let p := eval unfold QSImpl in QSImpl in
          let p := eval simpl in (Sharpened_DelegateSigs p) in
              match p with
                  Build_IndexedQueryStructure_Impl_Sigs ?SearchTerms =>
                  pose SearchTerms
              end;
        repeat match goal with
                 | H : ilist _ (?sch :: ?schemas')
                   |- ilist _ (?sch :: ?schemas') =>
                   let SearchTerm := fresh "SearchTerm" in
                   econstructor 1;
                     [let SearchTerm := eval simpl in (ilist_hd H) in
                          exact SearchTerm |
                      let SearchTerm := eval simpl in (ilist_tl H) in
                          pose SearchTerm; clear H ]
                 | |- _ => econstructor 2
               end.


Ltac BuildQSDelegateReps QSImpl :=
  let p := eval unfold QSImpl in QSImpl in
      let p := eval simpl in (Sharpened_DelegateSigs p) in
          match p with
              Build_IndexedQueryStructure_Impl_Sigs ?SearchTerms =>
              pose SearchTerms
          end;
          repeat match goal with
                   | H : ilist _ (?sch :: ?schemas')
                     |- ilist _ (?sch :: ?schemas') =>
               let SearchTerm := fresh "SearchTerm" in
               econstructor 1;
                 [let SearchTerm := eval simpl in (BagSearchTermType (ilist_hd H)) in
                      match SearchTerm
                      with
                        | BuildIndexSearchTerm ?AttrList =>
                           pose AttrList;
                             clear H;
                             list_of_evar (@ProperAttribute (schemaHeading (relSchema sch))) AttrList
                             ltac:(fun PAttrList =>
                                     assert (map BagsOfTuples.Attribute PAttrList = AttrList)
                                     by (simpl; repeat f_equal;
                                         match goal with
                                             |- @BagsOfTuples.Attribute ?heading ?h = ?g =>
                                             instantiate (1 := @Build_ProperAttribute heading g _);
                                             first [instantiate (1 := inright (eq_refl _))
                                                   | instantiate (1 := inleft (inright (eq_refl _)))
                                                   | instantiate (1 := inleft (inleft (right (eq_refl _))))
                                                   | instantiate (1 := inleft (inleft (left (eq_refl _))))
                                                   ]; reflexivity
                                         end);
                                   let p := eval simpl in (@NestedTreeFromAttributes _ PAttrList)
                               in exact p)

                                    (* Other SearchTerm types go here. *)
                      end
                 | let SearchTerm := eval simpl in (ilist_tl H) in
                       pose SearchTerm; clear H ]
             | |- _ => econstructor 2
           end.

Ltac BuildQSDelegateImpls QSImpl :=
      repeat match goal with
        | |- @i2list2 _ _ _ _
                      (?sch :: ?schemas)
                      (icons ?ST ?STs)
                      (icons ?Rep ?Reps) =>
          econstructor 1; simpl
        | |- _ => econstructor 2
      end;
        match goal with
            |- ComputationalADT.pcADT
                 (BagSig (@Tuple ?heading)
                         (BuildIndexSearchTerm ?AttrList) _) _ =>
            list_of_evar (@ProperAttribute heading) AttrList
                         ltac:(fun PAttrList =>
                                 let H := fresh in
                               try assert (map BagsOfTuples.Attribute PAttrList = AttrList) as H
                               by (simpl; repeat f_equal;
                                   match goal with
                                       |- @BagsOfTuples.Attribute ?heading ?h = ?g =>
                                       instantiate (1 := @Build_ProperAttribute heading g _);
                                       first [instantiate (1 := inright (eq_refl _))
                                             | instantiate (1 := inleft (inright (eq_refl _)))
                                             | instantiate (1 := inleft (inleft (right (eq_refl _))))
                                             | instantiate (1 := inleft (inleft (left (eq_refl _))))
                                             ]; reflexivity
                                   end);
                             let p :=
                                 eval simpl in (projT2 (@BagADTImpl _ _ _ _ (fun _ => true)
                                                                     (@NestedTreeFromAttributesAsBag' _ PAttrList))) in clear H; exact p )
      end.

Definition LookupQSDelegateImpls'
             {schemas : list NamedSchema}
             (SearchTerms : ilist (fun ns => SearchUpdateTerms (schemaHeading (relSchema ns))) schemas)
             (DelegateImpls :
                i2list
                  (fun ns (SearchTerm : SearchUpdateTerms (schemaHeading (relSchema ns))) =>
                     FullySharpened
                       (@BagSpec (@Tuple (schemaHeading (relSchema ns)))
                                 (BagSearchTermType SearchTerm)
                                 (BagUpdateTermType SearchTerm)
                                 (BagMatchSearchTerm SearchTerm)
                                 (BagApplyUpdateTerm SearchTerm)))
                  SearchTerms)
  : forall (idx : @BoundedString (map relName schemas)),
      refineADT
        (Build_IndexedQueryStructure_Impl_Specs SearchTerms idx)
        (ComputationalADT.LiftcADT (projT1 (i2th_Bounded relName DelegateImpls idx))).
  Proof.
    intro.
    unfold Build_IndexedQueryStructure_Impl_Specs.
    eapply (@i2th_Bounded_rect _ _ relName _ _ _ (fun schemas SearchTerms DelegateImpls idx
                                                      a b (c c' :
                                                             FullySharpened (BagSpec (BagMatchSearchTerm (heading := schemaHeading (relSchema a )) b)
                                          (BagApplyUpdateTerm b)))
                                                             =>
                                                           refineADT
                                                             (BagSpec (BagMatchSearchTerm (heading := schemaHeading (relSchema a )) b)
                                          (BagApplyUpdateTerm b))
                                 (ComputationalADT.LiftcADT
                                    (projT1 c))) schemas idx SearchTerms DelegateImpls
                             (i2th_Bounded relName DelegateImpls idx)).
    unfold Dep_Option_elim2_T2; simpl.
    destruct idx as [idx [n In_n ]]; simpl in *.
    revert schemas SearchTerms DelegateImpls idx In_n.
    induction n; destruct schemas; simpl; eauto.
    - intros; destruct (ilist_invert' SearchTerms) as [b [il' SearchTerms_eq]]; subst.
      destruct (i2list_invert' DelegateImpls) as [c [Cs' DelegateImpls_eq]]; subst.
      exact (projT2 c).
    - intros; destruct (ilist_invert' SearchTerms) as [b [il' SearchTerms_eq] ]; subst.
      destruct (i2list_invert' DelegateImpls) as [c [Cs' DelegateImpls_eq]]; subst.
      eapply (IHn schemas il' Cs' idx In_n).
  Defined.

  Ltac BuildQSIndexedBag heading AttrList k :=
    match AttrList with
      | ?Attr :: [ ] =>
        let AttrKind := eval simpl in (KindIndexKind Attr) in
            let AttrIndex := eval simpl in (KindIndexIndex Attr) in
                let is_equality := eval compute in (string_dec AttrKind "EqualityIndex") in

                    match is_equality with
                  | left _ =>
                    let AttrType := eval compute in (Domain heading AttrIndex) in
                        match AttrType with
                          | BinNums.N =>
                            k (@NTreeBag.IndexedBagAsCorrectBag
                                 _ _ _ _ _ _ _
                                 (@CountingListAsCorrectBag
                                    (@Tuple heading)
                                    (IndexedTreeUpdateTermType heading)
                                    (IndexedTreebupdate_transform heading))
                                 (fun x => GetAttribute (heading := heading) x AttrIndex)
                                 )
                          | BinNums.Z =>
                            k (@ZTreeBag.IndexedBagAsCorrectBag
                                 _ _ _ _ _ _ _
                                 (@CountingListAsCorrectBag
                                    (@Tuple heading)
                                    (IndexedTreeUpdateTermType heading)
                                    (IndexedTreebupdate_transform heading))
                                 (fun x => GetAttribute (heading := heading) x AttrIndex)
                              )
                          | nat =>
                            k (@NatTreeBag.IndexedBagAsCorrectBag
                                 _ _ _ _ _ _ _
                                 (@CountingListAsCorrectBag
                                    (@Tuple heading)
                                    (IndexedTreeUpdateTermType heading)
                                    (IndexedTreebupdate_transform heading))
                                 (fun x => GetAttribute (heading := heading) x AttrIndex)
                              )
                          | string =>
                            k (@StringTreeBag.IndexedBagAsCorrectBag
                                 _ _ _ _ _ _ _
                                 (@CountingListAsCorrectBag
                                    (@Tuple heading)
                                    (IndexedTreeUpdateTermType heading)
                                    (IndexedTreebupdate_transform heading))
                                 (fun x => GetAttribute (heading := heading) x AttrIndex)
                              )
                        end
                    end
      | ?Attr :: ?AttrList' =>
        let AttrKind := eval simpl in (KindIndexKind Attr) in
            let AttrIndex := eval simpl in (KindIndexIndex Attr) in
                let is_equality := eval compute in (string_dec AttrKind "EqualityIndex") in
                match is_equality with
                  | left _ =>
                    let AttrType := eval compute in (Domain heading AttrIndex) in
                        match AttrType with
                          | BinNums.N =>
                            BuildQSIndexedBag
                              heading
                              AttrList'
                              ltac:(fun subtree =>
                                      k (@NTreeBag.IndexedBagAsCorrectBag
                                           _ _ _ _ _ _ _ subtree
                                           (fun x => GetAttribute (heading := heading) x AttrIndex)))
                          | BinNums.Z =>
                            BuildQSIndexedBag
                              heading
                              AttrList'
                              (fun x => GetAttribute x AttrIndex)
                              ltac:(fun subtree =>
                                      k (@ZTreeBag.IndexedBagAsCorrectBag
                                           _ _ _ _ _ _ _ subtree
                                           (fun x => GetAttribute (heading := heading) x AttrIndex)))
                          | nat =>
                            BuildQSIndexedBag
                              heading
                              AttrList'
                              ltac:(fun subtree =>
                                      k (@NatTreeBag.IndexedBagAsCorrectBag
                                           _ _ _ _ _ _ _ subtree
                                           (fun x => GetAttribute (heading := heading) x AttrIndex)))
                          | string =>
                            BuildQSIndexedBag
                              heading
                              AttrList'
                              ltac:(fun subtree =>
                                      k (@StringTreeBag.IndexedBagAsCorrectBag
                                           _ _ _ _ _ _ _ subtree
                                           (fun x => GetAttribute (heading := heading) x AttrIndex)))
                        end
                end
    end.

  Lemma ValidUpdateCorrect
  : forall (A : Prop), false = true -> A.
    intros; discriminate.
  Qed.

  Ltac BuildQSIndexedBags SearchTerms k :=
    match SearchTerms with
      | @icons _ _ ?sch ?schemas'
               {| BagSearchTermType := BuildIndexSearchTerm ?AttrList;
                  BagMatchSearchTerm := _;
                  BagUpdateTermType := _;
                  BagApplyUpdateTerm := _ |}
               ?SeachTerms'
        =>
        BuildQSIndexedBags
          SeachTerms'
          ltac:(fun Bags =>
                     BuildQSIndexedBag (schemaHeading (relSchema sch))
                                       AttrList
                                       ltac:(fun Bag => k (i2cons

                                                             SearchTerms
                                                             (@SharpenedBagImpl _ _ _ _ _ _ (fun _ => false) _ Bag (fun a b => ValidUpdateCorrect _ b)) Bags)))
      | inil _ => k (i2nil
                       (fun ns (SearchTerm : SearchUpdateTerms (schemaHeading (relSchema ns))) =>
                          FullySharpened
                            (@BagSpec (@Tuple (schemaHeading (relSchema ns)))
                                      (BagSearchTermType SearchTerm)
                                      (BagUpdateTermType SearchTerm)
                                      (BagMatchSearchTerm SearchTerm)
                                      (BagApplyUpdateTerm SearchTerm)))
                       SearchTerms)
    end.

  Ltac BuildQSIndexedBags' :=
    match goal with
        |- context [Build_IndexedQueryStructure_Impl_Sigs ?SearchTerms _] =>
        BuildQSIndexedBags
          SearchTerms
          ltac:(fun Bags =>
                  eapply (LookupQSDelegateImpls' Bags))
    end.

Arguments LookupQSDelegateReps _ _ _ / .
Arguments LookupQSDelegateImpls _ _ _ _ _ / .
Arguments LookupQSDelegateImpls' _ _ _ _ / .
Arguments Build_IndexedQueryStructure_Impl_cRep _ _ _ / .
