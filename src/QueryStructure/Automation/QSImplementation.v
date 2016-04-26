(* Tactics for extracting Query Structure Implementations. *)
Require Import Coq.Strings.String
Fiat.ADTRefinement.GeneralBuildADTTactics
Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsOfTuples
Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
Fiat.QueryStructure.Automation.AutoDB.
Require Export Fiat.Common.ilist3_pair
        Fiat.Common.ilist3
        Fiat.Common.i3list2.

Ltac list_of_evar B As k :=
  lazymatch As with
  | nil => k (@nil B)
  | cons ?a ?As' =>
    makeEvar B ltac:(fun b =>
                       list_of_evar
                         B As' ltac:(fun Bs => k (cons b Bs)))
  end.

Lemma ValidUpdateCorrect
  : forall (A : Prop), false = true -> A.
Proof.
  intros; discriminate.
Qed.

Definition LookupQSDelegateReps {n}
           (Reps : Vector.t Type n)
           (idx : Fin.t n)
  : Type := Vector.nth Reps idx.

Definition LookupQSDelegateImpls {n}
           {schemas : Vector.t RawSchema n}
           (SearchTerms : ilist3 (B := fun sch => SearchUpdateTerms (rawSchemaHeading sch)) schemas)
           (Reps : Vector.t Type n)
           (DelegateImpls : ilist3_pair
                              (B := fun sch => SearchUpdateTerms (rawSchemaHeading sch))
                              (C := fun sch Rep SearchTerm =>
                                      ComputationalADT.pcADT
                                        (BagSig (@RawTuple (rawSchemaHeading sch))
                                                (BagSearchTermType SearchTerm)
                                                (BagUpdateTermType SearchTerm))
                                        Rep) SearchTerms Reps)
  : forall (idx : Fin.t n),
    ComputationalADT.pcADT
      (Build_IndexedQueryStructure_Impl_Sigs SearchTerms idx)
      (LookupQSDelegateReps Reps idx) := ith3_pair DelegateImpls.

Definition LookupQSDelegateImpls' {n}
           {schemas : Vector.t RawSchema n}
           (SearchTerms : ilist3 (B := fun sch => SearchUpdateTerms (rawSchemaHeading sch)) schemas)
           (DelegateImpls :
              i3list2
                (fun sch (SearchTerm : SearchUpdateTerms (rawSchemaHeading sch)) =>
                   FullySharpened
                     (@BagSpec (@RawTuple (rawSchemaHeading sch))
                               (BagSearchTermType SearchTerm)
                               (BagUpdateTermType SearchTerm)
                               (BagMatchSearchTerm SearchTerm)
                               (BagApplyUpdateTerm SearchTerm)))
                SearchTerms)
  : forall (idx : Fin.t n),
    refineADT
      (Build_IndexedQueryStructure_Impl_Specs SearchTerms idx)
      (ComputationalADT.LiftcADT (projT1 (i3th2 DelegateImpls idx))).
Proof.
  intro.
  unfold Build_IndexedQueryStructure_Impl_Specs.
  revert schemas SearchTerms DelegateImpls.
  induction idx.
  - intro; pattern n, schemas; eapply Vector.caseS; simpl.
    intros; eapply (projT2 (prim_fst DelegateImpls)).
  - intro schemas; revert idx IHidx;
    pattern n, schemas; eapply Vector.caseS.
    intros; eapply IHidx.
Qed.

Definition LookupQSDelegateImpls'' {n}
           {schemas : Vector.t RawSchema n}
           (SearchTerms : ilist3 (B := fun sch => SearchUpdateTerms (rawSchemaHeading sch)) schemas)
           (DelegateImpls :
              i3list2
                (fun sch (SearchTerm : SearchUpdateTerms (rawSchemaHeading sch)) =>
                   FullySharpened
                     (@BagSpec (@RawTuple (rawSchemaHeading sch))
                               (BagSearchTermType SearchTerm)
                               (BagUpdateTermType SearchTerm)
                               (BagMatchSearchTerm SearchTerm)
                               (BagApplyUpdateTerm SearchTerm)))
                SearchTerms)
  : forall (idx : Fin.t n),
    refineADT
      (Build_IndexedQueryStructure_Impl_Specs SearchTerms idx)
      (ComputationalADT.LiftcADT (i3th2 (i3map2 (fun sch SearchTerm c => projT1 c) DelegateImpls) idx)).
Proof.
  intro.
  rewrite <- i3th2_i3map2.
  eapply LookupQSDelegateImpls'.
Qed.

Ltac BuildQSDelegateSigs QSImpl :=
  let p := eval unfold QSImpl in QSImpl in
      let p := eval simpl in (Sharpened_DelegateSigs p) in
          lazymatch p with
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
          lazymatch p with
            Build_IndexedQueryStructure_Impl_Sigs ?SearchTerms =>
            pose SearchTerms
          end;
        repeat match goal with
               | H : ilist _ (?sch :: ?schemas')
                 |- ilist _ (?sch :: ?schemas') =>
                 let SearchTerm := fresh "SearchTerm" in
                 econstructor 1;
                   [let SearchTerm := eval simpl in (BagSearchTermType (ilist_hd H)) in
                        lazymatch SearchTerm
                        with
                        | BuildIndexSearchTerm ?AttrList =>
                          pose AttrList;
                            clear H;
                            list_of_evar (@ProperAttribute (schemaHeading (relSchema sch))) AttrList
                                         ltac:(fun PAttrList =>
                                                 assert (map BagsOfTuples.Attribute PAttrList = AttrList)
                                                 by (simpl; repeat f_equal;
                                                     lazymatch goal with
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

(*Ltac BuildQSDelegateImpls QSImpl :=
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
      end. *)

Ltac BuildQSIndexedBag heading AttrList BuildEarlyBag BuildLastBag k :=
  lazymatch AttrList with
  | ?Attr :: [ ] =>
    let AttrKind := eval simpl in (KindIndexKind Attr) in
        let AttrIndex := eval simpl in (KindIndexIndex Attr) in
            let is_equality := eval compute in (string_dec AttrKind "EqualityIndex") in

                lazymatch is_equality with
                | left _ =>
                  let AttrType := eval compute in (Domain heading AttrIndex) in
                      lazymatch AttrType with
                      | BinNums.N =>
                        k (@NTreeBag.IndexedBagAsCorrectBag
                             _ _ _ _ _ _ _
                             (@CountingListAsCorrectBag
                                (@RawTuple heading)
                                (IndexedTreeUpdateTermType heading)
                                (IndexedTreebupdate_transform heading))
                             (fun x => GetAttributeRaw (heading := heading) x AttrIndex)
                          )
                      | BinNums.Z =>
                        k (@ZTreeBag.IndexedBagAsCorrectBag
                             _ _ _ _ _ _ _
                             (@CountingListAsCorrectBag
                                (@RawTuple heading)
                                (IndexedTreeUpdateTermType heading)
                                (IndexedTreebupdate_transform heading))
                             (fun x => GetAttributeRaw (heading := heading) x AttrIndex)
                          )
                      | nat =>
                        k (@NatTreeBag.IndexedBagAsCorrectBag
                             _ _ _ _ _ _ _
                             (@CountingListAsCorrectBag
                                (@RawTuple heading)
                                (IndexedTreeUpdateTermType heading)
                                (IndexedTreebupdate_transform heading))
                             (fun x => GetAttributeRaw (heading := heading) x AttrIndex)
                          )
                      | string =>
                        k (@StringTreeBag.IndexedBagAsCorrectBag
                             _ _ _ _ _ _ _
                             (@CountingListAsCorrectBag
                                (@RawTuple heading)
                                (IndexedTreeUpdateTermType heading)
                                (IndexedTreebupdate_transform heading))
                             (fun x => GetAttributeRaw (heading := heading) x AttrIndex)
                          )
                      end
                | right _ =>
                  BuildLastBag heading AttrList AttrKind AttrIndex k
                end
  | ?Attr :: ?AttrList' =>
    let AttrKind := eval simpl in (KindIndexKind Attr) in
        let AttrIndex := eval simpl in (KindIndexIndex Attr) in
            let is_equality := eval compute in (string_dec AttrKind "EqualityIndex") in
                lazymatch is_equality with
                | left _ =>
                  let AttrType := eval compute in (Domain heading AttrIndex) in
                      lazymatch AttrType with
                      | BinNums.N =>
                        BuildQSIndexedBag
                          heading AttrList'
                          BuildEarlyBag BuildLastBag
                          ltac:(fun subtree =>
                                  k (@NTreeBag.IndexedBagAsCorrectBag
                                       _ _ _ _ _ _ _ subtree
                                       (fun x => GetAttributeRaw (heading := heading) x AttrIndex)))
                      | BinNums.Z =>
                        BuildQSIndexedBag
                          heading AttrList'
                          BuildEarlyBag BuildLastBag
                          (fun x => GetAttributeRaw x AttrIndex)
                          ltac:(fun subtree =>
                                  k (@ZTreeBag.IndexedBagAsCorrectBag
                                       _ _ _ _ _ _ _ subtree
                                       (fun x => GetAttributeRaw (heading := heading) x AttrIndex)))
                      | nat =>
                        BuildQSIndexedBag
                          heading AttrList'
                          BuildEarlyBag BuildLastBag
                          ltac:(fun subtree =>
                                  k (@NatTreeBag.IndexedBagAsCorrectBag
                                       _ _ _ _ _ _ _ subtree
                                       (fun x => GetAttributeRaw (heading := heading) x AttrIndex)))
                      | string =>
                        BuildQSIndexedBag
                          heading AttrList'
                          BuildEarlyBag BuildLastBag
                          ltac:(fun subtree =>
                                  k (@StringTreeBag.IndexedBagAsCorrectBag
                                       _ _ _ _ _ _ _ subtree
                                       (fun x => GetAttributeRaw (heading := heading) x AttrIndex)))
                      end
                | right _ =>
                  BuildQSIndexedBag
                    heading AttrList'
                    BuildEarlyBag BuildLastBag
                    ltac:(fun subtree =>
                            BuildEarlyBag
                                 heading AttrList AttrKind AttrIndex subtree k)
                end
  | [ ] =>
    k (@CountingListAsCorrectBag
         (@RawTuple heading)
         (IndexedTreeUpdateTermType heading)
         (IndexedTreebupdate_transform heading))
  end.

  Ltac BuildQSIndexedBags SearchTerms BuildEarlyBags BuildLastBags k :=
    lazymatch SearchTerms with
    | @icons3 _ _ ?heading _ ?headings' ?SearchTerm
              ?SeachTerms'
      =>
      let BagSearchTermType' := eval simpl in (BagSearchTermType SearchTerm) in
          let AttrList' := lazymatch BagSearchTermType' with
                           | BuildIndexSearchTerm ?AttrList => AttrList
                           end in
          BuildQSIndexedBags
            SeachTerms' BuildEarlyBags BuildLastBags
            ltac:(fun Bags =>
                    BuildQSIndexedBag
                      heading AttrList'
                      BuildEarlyBags BuildLastBags
                      ltac:(fun BagCorrect =>
                              abstractADTImpl
                                (@SharpenedBagImpl _ _ _ _ _ _
                                                   (fun _ => false) _
                                                   BagCorrect (fun a b => ValidUpdateCorrect _ b))
                                ltac:(fun BagADT' =>
                                        k (i3cons2
                                             (C := (fun sch (SearchTerm' : SearchUpdateTerms sch) =>
                                                      FullySharpened
                                                        (@BagSpec (@RawTuple sch)
                                                                  (BagSearchTermType SearchTerm')
                                                                  (BagUpdateTermType SearchTerm')
                                                                  (BagMatchSearchTerm SearchTerm')
                                                                  (BagApplyUpdateTerm SearchTerm'))))
                                             (b := SearchTerm)
                                             (existT _ BagADT'
                                                     (@SharpenedBagImpl_subproof
                                                        _ _ _ _ _ _
                                                        (fun _ => false) _
                                                        BagCorrect (fun a b => ValidUpdateCorrect _ b))) Bags))))
    | inil3 => k (i3nil2
                    (C := fun heading' (SearchTerm' : SearchUpdateTerms heading') =>
                            FullySharpened
                              (@BagSpec (@RawTuple heading')
                                        (BagSearchTermType SearchTerm')
                                        (BagUpdateTermType SearchTerm')
                                        (BagMatchSearchTerm SearchTerm')
                                        (BagApplyUpdateTerm SearchTerm'))))
    end.

Ltac BuildQSIndexedBags' BuildEarlyBags BuildLastBags :=
  repeat match goal with
           H := BuildIndexSearchTerm _ |- _ => subst H
         end;
  lazymatch goal with
    |- context [@Build_IndexedQueryStructure_Impl_Sigs _ ?indices ?SearchTerms _] =>
    BuildQSIndexedBags
      SearchTerms BuildEarlyBags BuildLastBags
      ltac:(fun Bags =>
              let Impls := fresh in
              pose proof (@LookupQSDelegateImpls'' _ indices SearchTerms Bags) as Impls; unfold  Update_Build_IndexedQueryStructure_Impl_cRep,
                                                                                        Update_Iterate_Dep_Type in Impls; simpl in Impls;
            apply Impls
           )
  end.

Ltac BuildLastEqualityBag heading AttrList AttrKind AttrIndex k := fail.
Ltac BuildEarlyEqualityBag heading AttrList AttrKind AttrIndex subtree k := fail.

Arguments LookupQSDelegateReps _ _ _ / .
Arguments LookupQSDelegateImpls _ _ _ _ _ _ / .
Arguments LookupQSDelegateImpls' _ _ _ _ _ / .
Arguments Build_IndexedQueryStructure_Impl_cRep _ _ _ _ / .
