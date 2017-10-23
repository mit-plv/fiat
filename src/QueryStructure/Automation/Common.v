Require Import
        Coq.Strings.String
        Fiat.Common
        Fiat.Common.StringBound
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Common.Tactics.HintDbExtra
        Fiat.Common.Tactics.TransparentAbstract
        Fiat.Computation.Refinements.General
        Fiat.Computation.SetoidMorphisms
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Schema
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.

Ltac psearch_combine x y k := solve [x; k ()] || y k.

Ltac psearch_eapply_combine x y k := solve [eapply x; k ()] || y k.

Ltac psearch_lazy_combine x y k := solve [x (); k ()] || y k.

Ltac psearch n z :=
  fun _ =>
    match n with
    | 0 => fail
    | S ?n' => z ltac:(psearch n' z)
    end.

Create HintDb headingCache.

Ltac fold_heading_hyps :=
  (repeat foreach [ headingCache ] run (fun id => progress fold id)).

Ltac fold_heading_hyps_in H :=
  repeat foreach [ headingCache ] run (fun id => progress fold id in H).

Ltac pose_heading_hyps :=
  fold_heading_hyps;
  repeat
    match goal with
    | |- context[@Build_RawHeading ?n ?attrlist] =>
      let heading := fresh "heading" in
      let H' := fresh in
      assert True as H' by
            (clear;
             (cache_term (@Build_RawHeading n attrlist) as heading
                 run (fun id => fold id in *;
                                add id to headingCache));
      exact I); clear H'
    | |- context[ @BuildHeading ?n ?attrlist ] =>
      let heading := fresh "heading" in
      let H' := fresh in
      assert True as H' by
            (clear;
             (cache_term (@BuildHeading n attrlist) as heading
                 run (fun id => fold id in *;
                                add id to headingCache));
      exact I); clear H'
    | |- context [@Build_RawSchema ?heading ?TupleConstr ?RelConstr] =>
      let str := fresh "schema" in
      let H' := fresh in
      assert True as H' by
            (clear;
             (cache_term (@Build_RawSchema heading TupleConstr RelConstr) as str
                 run (fun id => fold id in *;
                                add id to headingCache));
      exact I); clear H'
    | |- context [@Build_RawQueryStructureSchema ?n ?qs_schema ?CrossConstr] =>
      let str := fresh "qs_schema" in
      let H' := fresh in
      assert True as H' by
            (clear;
             (cache_term (@Build_RawQueryStructureSchema n qs_schema CrossConstr) as str run (fun id => fold id in *);
                                                                                                add id to headingCache);
      exact I); clear H'
    end.

Ltac pose_heading_hyps_in H :=
  fold_heading_hyps_in H;
  repeat
    (let H' := eval unfold H in H in
         match H' with
         | context[@Build_RawHeading ?n ?attrlist] =>
           let heading := fresh "heading" in
           let H'' := fresh in
           assert True as H'' by
                 (clear;
           (cache_term (@Build_RawHeading n attrlist) as heading
                      run (fun id => fold id in *;
                                     add id to headingCache));
           exact I); clear H''
         | context [@Build_RawSchema ?heading ?TupleConstr ?RelConstr] =>
           let str := fresh "schema" in
           let H'' := fresh in
           assert True as H'' by
                 (clear;
           (cache_term (@Build_RawSchema heading TupleConstr RelConstr) as str
                      run (fun id => fold id in *;
                                     add id to headingCache));
           exact I); clear H''
         | context [@Build_RawQueryStructureSchema ?n ?qs_schema ?CrossConstr] =>
           let str := fresh "qs_schema" in
           let H'' := fresh in
           assert True as H'' by
                 (clear;
           (cache_term (@Build_RawQueryStructureSchema n qs_schema CrossConstr) as str
                      run (fun id => fold id in *;
                                     add id to headingCache));
           exact I);  clear H''
         end).

Ltac pose_headings_all := pose_heading_hyps.

Create HintDb search_term_Cache.

Ltac pose_search_term_in H :=
  repeat
    (let H' := eval unfold H in H in
         match H' with
         | context[BuildIndexSearchTerm ?Indexes] =>
           let search_term := fresh "SearchTerm" in
           let H'' := fresh in
           assert True as H'' by
                 (clear;
           (cache_term (BuildIndexSearchTerm Indexes) as search_term
                      run (fun id => fold id in *;
                                     add id to search_term_Cache));
           exact I); clear H''
         end).

Ltac pose_search_term :=
  repeat
    ( match goal with
        |- context[BuildIndexSearchTerm ?Indexes] =>
        let search_term := fresh "SearchTerm" in
        let H'' := fresh in
           assert True as H'' by
                 (clear;
        (cache_term (BuildIndexSearchTerm Indexes) as search_term
                      run (fun id => fold id in *;
                                     add id to search_term_Cache));
        exact I);
        clear H''
      end).

Create HintDb SearchUpdateTermCache.

Ltac pose_SearchUpdateTerms_in H :=
  repeat
    (let H' := eval unfold H in H in
         match H' with
         | context [@Build_SearchUpdateTerms
                      ?heading
                      ?search_term ?matcher
                      ?update_term ?applier] =>
           let search_update_term := fresh "SearchUpdateTerm" in
           let H'' := fresh in
           assert True as H'' by
                 (clear;
           (cache_term (@Build_SearchUpdateTerms
                         heading search_term
                         matcher update_term applier)
                      as search_update_term
                      run (fun id => fold id in *;
                                     add id to SearchUpdateTermCache));
           exact I); clear H''
         end).

Ltac pose_SearchUpdateTerms :=
  repeat
    (match goal with
       |- context [@Build_SearchUpdateTerms
                     ?heading
                     ?search_term ?matcher
                     ?update_term ?applier] =>
       let search_update_term := fresh "SearchUpdateTerm" in
       let H'' := fresh in
       assert True as H'' by
             (clear;
       (cache_term (@Build_SearchUpdateTerms
                     heading search_term
                     matcher update_term applier)
                  as search_update_term
                  run (fun id => fold id in *;
                                 add id to SearchUpdateTermCache));
       exact I); clear H''
     end).

Ltac subst_all := idtac.
(*repeat match goal with H : _ |- _ => subst H end.*)

Ltac zeta_expand id H :=
  revert id H;
  match goal with
    |- let id := ?Z in
       let H := ?bod in
       _ =>
    let H' := fresh in
    pose (let id := Z in bod) as H;
      intros id H'; change H' with H in *;
      clear H'; revert id
  end.

Ltac zeta_expand_all impl :=
  repeat match goal with
           H := _ : _, impl := _ : _ |- _ =>
           zeta_expand H impl
         end.

Ltac CombineCase1 x y :=
  fun a => x a y.

Ltac CombineCase2 x y :=
  fun a b => x a b y.

Ltac CombineCase3 x y :=
  fun a b c => x a b c y.

Ltac CombineCase4 x y :=
  fun a b c d => x a b c d y.

Ltac CombineCase5 x y :=
  fun a b c d e => x a b c d e y.

Ltac CombineCase6 x y :=
  fun a b c d e f => x a b c d e f y.

Ltac CombineCase7 x y :=
  fun a b c d e f g => x  a b c d e f g y.

Ltac CombineCase8 x y :=
  fun a b c d e f g h => x a b c d e f g h y.

Ltac CombineCase9 x y :=
  fun a b c d e f g h i => x a b c d e f g h i y.

Ltac CombineCase10 x y :=
  fun a b c d e f g h i j => x a b c d e f g h i j y.

Ltac CombineCase11 x y :=
  fun a b c d e f g h i j k => x a b c d e f g h i j k y.

Ltac LastCombineCase1 x :=
  fun a => x a ltac:(fun _ => fail).

Ltac LastCombineCase2 x :=
  fun a b => x a b ltac:(fun _ _ => fail).

Ltac LastCombineCase3 x :=
  fun a b c => x a b ltac:(fun _ _ _ => fail).

Ltac LastCombineCase4 x :=
  fun a b c d => x a b c d ltac:(fun _ _ _ _ => fail).

Ltac LastCombineCase5 x :=
  fun a b c d e => x a b c d e ltac:(fun _ _ _ _ _ => fail).

Ltac LastCombineCase6 x :=
  fun a b c d e f => x a b c d e f ltac:(fun _ _ _ _ _ _ => fail).

Ltac LastCombineCase7 x :=
  fun a b c d e f g => x  a b c d e f g ltac:(fun _ _ _ _ _ _ _ => fail).

Ltac LastCombineCase8 x :=
  fun a b c d e f g h => x a b c d e f g h ltac:(fun _ _ _ _ _ _ _ _ => fail).

Ltac LastCombineCase9 x :=
  fun a b c d e f g h i => x a b c d e f g h i ltac:(fun _ _ _ _ _ _ _ _ _ => fail).

Ltac LastCombineCase10 x :=
  fun a b c d e f g h i j => x a b c d e f g h i j ltac:(fun _ _ _ _ _ _ _ _ _ _ => fail).

Ltac LastCombineCase11 x :=
  fun a b c d e f g h i j k => x a b c d e f g h i j k ltac:(fun _ _ _ _ _ _ _ _ _ _ _ => fail).

Ltac PackageIndexTactics
     FindAttributeUses
     BuildEarlyIndex BuildLastIndex
     IndexUse createEarlyTerm createLastTerm
     IndexUse_dep createEarlyTerm_dep createLastTerm_dep
     BuildEarlyBag BuildLastBag
     f :=
  f FindAttributeUses
    BuildEarlyIndex BuildLastIndex
    IndexUse createEarlyTerm createLastTerm
    IndexUse_dep createEarlyTerm_dep createLastTerm_dep
    BuildEarlyBag BuildLastBag.

Ltac CombineIndexTactics IndexPackage1 IndexPackage2 f :=
  IndexPackage2
    ltac:(fun FindAttributeUses2 BuildEarlyIndex2 BuildLastIndex2
              IndexUse2 createEarlyTerm2 createLastTerm2
              IndexUse_dep2 createEarlyTerm_dep2 createLastTerm_dep2
              BuildEarlyBag2 BuildLastBag2 =>
            IndexPackage1
              ltac:(fun FindAttributeUses1 BuildEarlyIndex1 BuildLastIndex1
                        IndexUse1 createEarlyTerm1 createLastTerm1
                        IndexUse_dep1 createEarlyTerm_dep1 createLastTerm_dep1
                    BuildEarlyBag1 BuildLastBag1 =>
                      f
                        ltac:(FindAttributeUses1 FindAttributeUses2)
                        ltac:(CombineCase6 BuildEarlyIndex1 BuildEarlyIndex2)
                        ltac:(CombineCase5 BuildLastIndex1 BuildLastIndex2)
                        ltac:(CombineCase5 IndexUse1 IndexUse2)
                        ltac:(CombineCase10 createEarlyTerm1 createEarlyTerm2)
                        ltac:(CombineCase7 createLastTerm1 createLastTerm2)
                        ltac:(CombineCase7 IndexUse_dep1 IndexUse_dep2)
                        ltac:(CombineCase11 createEarlyTerm_dep1 createEarlyTerm_dep2)
                        ltac:(CombineCase8 createLastTerm_dep1 createLastTerm_dep2)
                         ltac:(CombineCase6 BuildEarlyBag1 BuildEarlyBag2)
                         ltac:(CombineCase5 BuildLastBag1 BuildLastBag2))).

Ltac rewrite_drill :=
  subst_refine_evar;
  first
    [ eapply refine_under_bind_both;
      [set_refine_evar | intros; set_refine_evar ]
    | eapply refine_If_Then_Else;
      [set_refine_evar | set_refine_evar ]
    | eapply refine_If_Opt_Then_Else_trans;
      [set_refine_evar | set_refine_evar ] ].
