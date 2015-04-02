Require Import
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureNotations
        ADTSynthesis.QueryStructure.Specification.SearchTerms.InRange
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        ADTSynthesis.QueryStructure.Automation.IndexSelection.

(* Instances for building indexes with make simple indexes. *)
(* Every Kind of index is keyed on an inductive type with a single constructor*)
Definition RangeIndex : string := "RangeIndex".

(* This is our search term type. *)
Record RangeSearchTerm
       (heading : Heading)
  :=
    { RangeIndexSearchTerm : option (nat * nat);
      RangeItemSearchTerm : @Tuple heading -> bool }.

(* This builds the type of searchterms and the matching function on them *)
Global Instance RangeIndexDenotation
       (heading : Heading)
       (index : @Attributes heading)
       (projection : @Tuple heading -> nat)
: @IndexDenotation "RangeIndex" heading index :=
  {| DenoteIndex := RangeSearchTerm heading; (* Pick search term type *)
     MatchIndex search_term item := (* matching function : DenoteIndex -> Tuple heading -> bool *)
       match RangeIndexSearchTerm search_term with
         | Some indexSearchTerm =>
           if InRange_dec (projection item) indexSearchTerm then
             RangeItemSearchTerm search_term item
           else false
         | None =>
           RangeItemSearchTerm search_term item
       end |}.

(* Extra type class magic for range indices. *)
Hint Extern 10 (@IndexDenotation "RangeIndex" ?heading ?index) =>
let index_domain := eval hnf in (@Domain heading index) in
match index_domain with
  | nat =>
    apply (@RangeIndexDenotation
             heading index
             (fun tup => GetAttribute tup index ))
end
: typeclass_instances.

Ltac matchRangeIndex WhereClause k :=
  match WhereClause with
    | fun tups => InRange (@?C1 tups) _ =>
      let attrs1 := TermAttributes C1 in
      k (map (fun a12 => (RangeIndex, (fst a12, snd a12)))
             (attrs1))
  end.

Ltac RangeIndexUse SC F indexed_attrs f k :=
match type of f with
        (* Range Search Terms *)
        | forall a, {InRange (_!?fd) ?X} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "RangeIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
            k ({| KindNameKind := "RangeIndex";
                  KindNameName := fd|}, X) (fun _ : @Tuple SC => true)
        | forall a, {InRange (_!``?fd) ?X} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "RangeIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
            k ({| KindNameKind := "RangeIndex";
                  KindNameName := fd|}, X) (fun _ : @Tuple SC => true)
end.

Ltac RangeIndexUse_dep SC F indexed_attrs visited_attrs f T k :=
    match type of f with
        (* Range Search Terms *)
        | forall a b, {InRange (_!?fd) (@?X a)} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "RangeIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
          match eval simpl in
                (in_dec string_dec fd visited_attrs) with
            | right _ => k (fd :: visited_attrs)
                           ({| KindNameKind := "RangeIndex";
                               KindNameName := fd |}, X)
                           (fun (a : T) (_ : @Tuple SC) => true)
            | left _ => k visited_attrs tt F
          end
        | forall a b, {InRange (_``?fd) (@?X a)} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "RangeIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto);
            match eval simpl in
                  (in_dec string_dec fd visited_attrs) with
              | right _ => k (fd :: visited_attrs)
                             ({| KindNameKind := "RangeIndex";
                                 KindNameName := fd |}, X)
                             (fun (a : T) (_ : @Tuple SC) => true)
              | left _ => k visited_attrs tt F
            end
    end.

Ltac createLastRangeTerm f fds tail fs kind s k :=
  match kind with
    | "RangeIndex" =>
      (findMatchingTerm
         fds kind s
         ltac:(fun X => k {| RangeIndexSearchTerm := Some X;
                             RangeItemSearchTerm := tail |}))
        || k {| RangeIndexSearchTerm := None;
                RangeItemSearchTerm := tail |}
end.

Ltac createLastRangeTerm_dep dom f fds tail fs kind rest s k :=
  match kind with
    | "RangeIndex" =>
      (findMatchingTerm
         fds kind s
         ltac:(fun X => k (fun x : dom => {| RangeIndexSearchTerm := Some (X x);
                                             RangeItemSearchTerm := tail x |}))
                || k (fun x : dom => {| RangeIndexSearchTerm := None;
                                        RangeItemSearchTerm := tail x |}))
  end.

Ltac createEarlyRangeTerm f fds tail fs kind EarlyIndex LastIndex rest s k :=
  match kind with
    | "RangeIndex" =>
      (findMatchingTerm
         fds kind s
         ltac:(fun X => k (Some X, rest)))
        || k (@None (nat * nat), rest)
  end.
