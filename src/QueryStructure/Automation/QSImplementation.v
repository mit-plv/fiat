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

Arguments LookupQSDelegateReps _ _ _ / .
Arguments LookupQSDelegateImpls _ _ _ _ _ / .
Arguments Build_IndexedQueryStructure_Impl_cRep _ _ _ / .
