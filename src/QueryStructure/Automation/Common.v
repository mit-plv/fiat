Require Import
        Coq.Strings.String
        Fiat.Common.StringBound
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Schema
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.

Ltac fold_string_hyps :=
  repeat
    match goal with
    | H' := String ?R ?R' : _ |- _ => progress (fold H')
    (* | H' := @BoundedIndex ?A ?Bound : _ |- _ => progress (fold H')
    | H' := @Build_BoundedIndex ?A ?Bound ?idx ?bnd : _ |- _ => progress (fold H')
    | H' := ``(?R) : _ |- _ => progress(fold H') *)
    end.

Ltac fold_string_hyps_in H :=
  repeat
    match goal with
    | H' := String ?R ?R' : _ |- _ =>
      match type of H with
      | context [String R R'] => fold H' in H
      end

    (*| H' := @BoundedIndex ?A ?Bound : _ |- _ =>
              match type of H with
                | context [@BoundedIndex A Bound ] => fold H' in H
              end

      | H' := @Build_BoundedIndex ?A ?Bound ?idx ?bnd : _ |- _ =>
              match type of H with
                | context [@Build_BoundedIndex A Bound idx bnd ] => fold H' in H
              end
      | H' := ``(?R) : _ |- _ =>
              match type of H with
                | context [``(R)] => fold H' in H
              end *)
    end.

Ltac pose_string_hyps :=
  fold_string_hyps;
  repeat
    match goal with
    | |- context [String ?R ?R'] =>
      let str := fresh "StringId" in
      set (String R R') as str in *
    (*| |- context [@BoundedIndex ?A ?Bound] =>
        let idx := fresh "BStringId" in
        set (@BoundedIndex A Bound) as idx in *
      | |- context [ ``(?R) ] =>
        let idx := fresh "BStringId" in
        set ``(R) as idx in *
      | |- context [@Build_BoundedIndex ?A ?Bound ?idx ?bnd] =>
        let idx := fresh "BStringId" in
        set (@Build_BoundedIndex A Bound idx bnd) as idx in *  *)
    end.

Ltac fold_heading_hyps :=
  repeat
    match goal with
    | [H' := @Build_RawHeading _ _ :  _ |- _ ] => progress (fold H')
    | [H' := @Build_RawSchema ?heading ?TupleConstr ?RelConstr |- _ ]=> progress (fold H')
    | [H' := @Build_RawQueryStructureSchema _ ?qs_schema ?CrossConstr |- _ ] => progress (fold H')
    end.

Ltac fold_heading_hyps_in H :=
  repeat match goal with
         | [H' := @Build_RawHeading ?n ?heading :  _ |- _] =>
           match type of H with
           | context [@Build_RawHeading n heading] => fold H' in H
           end
         | [H' := @Build_RawSchema ?heading ?TupleConstr ?RelConstr |- _ ] =>
           match type of H with
           | context [@Build_RawSchema heading TupleConstr RelConstr] =>
             fold H' in H
           end
         | [H' := @Build_RawQueryStructureSchema ?n ?qs_schema ?CrossConstr |- _ ] =>
           match type of H with
           | context [@Build_QueryStructureSchema ?n ?qs_schema ?CrossConstr] =>
             fold H' in H
           end
         end.

Ltac pose_heading_hyps :=
  fold_heading_hyps;
  repeat match goal with
         (*| |- context[@Build_RawHeading ?n ?attrlist] =>
             let heading := fresh "heading" in
             set (@Build_RawHeading n attrlist) as heading in * *)

         | |- context [@Build_RawSchema ?heading ?TupleConstr ?RelConstr] =>
           let sch := fresh "schma" in
           set (@Build_RawSchema heading TupleConstr RelConstr) as sch in *

         | |- context [@Build_RawQueryStructureSchema ?n ?qs_schema ?CrossConstr] =>
           let qs_sch := fresh "qs_schma" in
           set (@Build_RawQueryStructureSchema n qs_schema CrossConstr) as qs_schema in *

         end.


Ltac subst_all :=
  repeat match goal with H : _ |- _ => subst H end.

Ltac pose_string_hyps_in H :=
  fold_string_hyps_in H;
  repeat
    (let H' := eval unfold H in H in
         match H' with
         | context [String ?R ?R'] =>
           let str := fresh "StringId" in
           set (String R R') as str in *
         (*| context [@BoundedIndex ?A ?Bound] =>
             let idx := fresh "BStringId" in
             set (@BoundedIndex A Bound) as idx in *
           | context [ ``(?R) ] =>
             let idx := fresh "BStringId" in
             set ``(R) as idx in *
           | context [@Build_BoundedIndex ?A ?Bound ?idx ?bnd] =>
             let idx := fresh "BStringId" in
             set (@Build_BoundedIndex A Bound idx bnd) as idx in * *)
         end).

Ltac pose_heading_hyps_in H :=
  fold_heading_hyps_in H;
  repeat
    (let H' := eval unfold H in H in
         match H' with
         (* | context[Build_RawHeading ?n ?attrlist] =>
             let heading := fresh "heading" in
             set (@Build_RawHeading n attrlist) as heading in * *)

         | context [@Build_RawSchema ?heading ?TupleConstr ?RelConstr] =>
           let sch := fresh "schma" in
           set (@Build_RawSchema heading TupleConstr RelConstr) as sch in *

         | context [@Build_RawQueryStructureSchema ?n ?qs_schema ?CrossConstr] =>
           let qs_sch := fresh "qs_schma" in
           set (@Build_QueryStructureSchema n qs_schema CrossConstr) as qs_schema in *
         end).

Ltac pose_search_term_in H :=
  repeat
    (let H' := eval unfold H in H in
         match H' with
         | context[BuildIndexSearchTerm ?Indexes] =>
           let search_term := fresh "SearchTerm" in
           set (BuildIndexSearchTerm Indexes) as search_term in *
         end).

Ltac pose_SearchUpdateTerms_in H :=
  repeat
    (let H' := eval unfold H in H in
         match H' with
         | context [@Build_SearchUpdateTerms
                      ?heading
                      ?search_term ?matcher
                      ?update_term ?applier] =>
           let search_update_term := fresh "SearchUpdateTerm" in
           set (@Build_SearchUpdateTerms heading search_term
                                         matcher update_term applier)
             as search_update_term in *
         end).

Ltac pose_search_term :=
  repeat
    ( match goal with
        |- context[BuildIndexSearchTerm ?Indexes] =>
        let search_term := fresh "SearchTerm" in
        set (BuildIndexSearchTerm Indexes) as search_term in *
      end).

Ltac pose_SearchUpdateTerms :=
  repeat
    (match goal with
       |- context [@Build_SearchUpdateTerms
                     ?heading
                     ?search_term ?matcher
                     ?update_term ?applier] =>
       let search_update_term := fresh "SearchUpdateTerm" in
       set (@Build_SearchUpdateTerms heading search_term
                                     matcher update_term applier)
         as search_update_term in *
     end).

Ltac pose_headings_all :=
  fold_heading_hyps;
  repeat match goal with
         | |- context[@Build_RawHeading ?n ?attrlist] =>
           let heading := fresh "heading" in
           set (@Build_RawHeading n attrlist) as heading in *

         | |- context [@Build_RawSchema ?heading ?TupleConstr ?RelConstr] =>
           let sch := fresh "schma" in
           set (@Build_RawSchema heading TupleConstr RelConstr) as sch in *

         | |- context [@Build_RawQueryStructureSchema ?n ?qs_schema ?CrossConstr] =>
           let qs_sch := fresh "qs_schma" in
           set (@Build_RawQueryStructureSchema n qs_schema CrossConstr) as qs_schema in *
         end.



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

Ltac PackageIndexTactics
     matchIndex IndexUse createEarlyTerm createLastTerm
     IndexUse_dep createEarlyTerm_dep createLastTerm_dep f :=
  f matchIndex IndexUse createEarlyTerm createLastTerm
    IndexUse_dep createEarlyTerm_dep createLastTerm_dep.

Ltac CombineIndexTactics IndexPackage1 IndexPackage2 f :=
  IndexPackage2
    ltac:(fun matchIndex2 IndexUse2 createEarlyTerm2 createLastTerm2
              IndexUse_dep2 createEarlyTerm_dep2 createLastTerm_dep2 =>
            IndexPackage1
              ltac:(fun matchIndex1 IndexUse1 createEarlyTerm1 createLastTerm1
                        IndexUse_dep1 createEarlyTerm_dep1 createLastTerm_dep1 =>
                      f ltac:(CombineCase2 matchIndex1 matchIndex2)
                               ltac:(CombineCase5 IndexUse1 IndexUse2)
                                      ltac:(CombineCase10 createEarlyTerm1 createEarlyTerm2)
                                             ltac:(CombineCase7 createLastTerm1 createLastTerm2)
                                                    ltac:(CombineCase7 IndexUse_dep1 IndexUse_dep2)
                                                           ltac:(CombineCase11 createEarlyTerm_dep1 createEarlyTerm_dep2)
                                                                  ltac:(CombineCase8 createLastTerm_dep1 createLastTerm_dep2))).
