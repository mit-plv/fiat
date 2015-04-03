Require Import
        Coq.Strings.String
        ADTSynthesis.Common.StringBound
        ADTSynthesis.QueryStructure.Specification.Representation.Heading
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.

Ltac fold_string_hyps :=
  repeat
    match goal with
      | H' := String ?R ?R' : _ |- _ => progress (fold H')
      | H' := @BoundedIndex ?A ?Bound : _ |- _ => progress (fold H')
      | H' := @Build_BoundedIndex ?A ?Bound ?idx ?bnd : _ |- _ => progress (fold H')
      | H' := ``(?R) : _ |- _ => progress(fold H')
    end.

Ltac fold_string_hyps_in H :=
  repeat
    match goal with
      | H' := String ?R ?R' : _ |- _ =>
              match type of H with
                | context [String R R'] => fold H' in H
              end

      | H' := @BoundedIndex ?A ?Bound : _ |- _ =>
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
              end
    end.

Ltac pose_string_hyps :=
  fold_string_hyps;
  repeat
    match goal with
      | |- context [String ?R ?R'] =>
        let str := fresh "StringId" in
        set (String R R') as str in *
      | |- context [@BoundedIndex ?A ?Bound] =>
        let idx := fresh "BStringId" in
        set (@BoundedIndex A Bound) as idx in *
      | |- context [ ``(?R) ] =>
        let idx := fresh "BStringId" in
        set ``(R) as idx in *
      | |- context [@Build_BoundedIndex ?A ?Bound ?idx ?bnd] =>
        let idx := fresh "BStringId" in
        set (@Build_BoundedIndex A Bound idx bnd) as idx in *
    end.

Ltac fold_heading_hyps :=
  repeat
    match goal with
      | H' := @BuildHeading _ :  _ |- _ => progress (fold H')
    end.

Ltac fold_heading_hyps_in H :=
  repeat match goal with
           | H' := @BuildHeading ?heading :  _ |- _ =>
                   (match type of H with
                      | context [@BuildHeading heading] => fold H' in H
                    end)
         end.

Ltac pose_heading_hyps :=
  fold_heading_hyps;
  repeat match goal with
           | |- context[BuildHeading ?attrlist] =>
             let heading := fresh "heading" in
             set (BuildHeading attrlist) as heading in *
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
           | context [@BoundedIndex ?A ?Bound] =>
             let idx := fresh "BStringId" in
             set (@BoundedIndex A Bound) as idx in *
           | context [ ``(?R) ] =>
             let idx := fresh "BStringId" in
             set ``(R) as idx in *
           | context [@Build_BoundedIndex ?A ?Bound ?idx ?bnd] =>
             let idx := fresh "BStringId" in
             set (@Build_BoundedIndex A Bound idx bnd) as idx in *
         end).

Ltac pose_heading_hyps_in H :=
  fold_heading_hyps_in H;
  repeat
    (let H' := eval unfold H in H in
         match H' with
           | context[BuildHeading ?attrlist] =>
             let heading := fresh "heading" in
             set (BuildHeading attrlist) as heading in *
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


Ltac CombineCase1 x y :=
  fun a =>
    match goal with
      | _ => x a
      | _ => y a
    end.
Ltac CombineCase2 x y :=
  fun a b =>
    match goal with
      | _ => x a b
      | _ => y a b
    end.
Ltac CombineCase3 x y :=
  fun a b c =>
    match goal with
      | _ => x a b c
      | _ => y a b c
    end.
Ltac CombineCase4 x y :=
  fun a b c d =>
    match goal with
      | _ => x a b c d
      | _ => y a b c d
    end.

Ltac CombineCase5 x y :=
  fun a b c d e =>
    match goal with
      | _ => x a b c d e
      | _ => y a b c d e
    end.

Ltac CombineCase6 x y :=
  fun a b c d e f =>
    match goal with
      | _ => x a b c d e f
      | _ => y a b c d e f
    end.

Ltac CombineCase7 x y :=
  fun a b c d e f g =>
    match goal with
      | _ => x a b c d e f g
      | _ => y a b c d e f g
    end.

Ltac CombineCase8 x y :=
  fun a b c d e f g h =>
    match goal with
      | _ => x a b c d e f g h
      | _ => y a b c d e f g h
    end.
