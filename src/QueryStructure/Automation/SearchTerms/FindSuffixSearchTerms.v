Require Import
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Automation.Common
        Coq.Strings.Ascii.

(* Instances for building indexes with make simple indexes. *)
(* Every Kind of index is keyed on an inductive type with a single constructor*)
Definition FindSuffixIndex : string := "FindSuffixIndex".

(* This is our search term type. *)
Record FindSuffixSearchTerm
       (heading : Heading)
  :=
    { FindSuffixIndexSearchTerm : option (list string);
      FindSuffixItemSearchTerm : @Tuple heading -> bool }.

Global Instance Astring_eq : Query_eq string := {| A_eq_dec := string_dec |}.

(* This builds the type of searchterms and the matching function on them *)
Global Instance FindSuffixIndexDenotation
       (heading : Heading)
       (index : @Attributes heading)
       (projection : @Tuple heading -> list string)
: @IndexDenotation "FindSuffixIndex" heading index :=
  {| DenoteIndex := FindSuffixSearchTerm heading; (* Pick search term type *)
     MatchIndex search_term item := (* matching function : DenoteIndex -> Tuple heading -> bool *)
       match FindSuffixIndexSearchTerm search_term with
         | Some indexSearchTerm =>
           if IsSuffix_dec (projection item) indexSearchTerm then
             FindSuffixItemSearchTerm search_term item
           else false
         | None =>
           FindSuffixItemSearchTerm search_term item
       end |}.

(* Extra type class magic for prefix indices. *)
Hint Extern 10 (@IndexDenotation "FindSuffixIndex" ?heading ?index) =>
let index_domain := eval hnf in (@Domain heading index) in
match index_domain with
  | list _ =>
    apply (@FindSuffixIndexDenotation
             heading index
             (fun tup => GetAttribute tup index ))
end
: typeclass_instances.

Ltac matchFindSuffixIndex WhereClause k k_fail :=
  match WhereClause with
    | fun tups => IsSuffix (@?C1 tups) _ =>
      let attrs1 := TermAttributes C1 in
      k (map (fun a12 => ("FindSuffixIndex", (fst a12, snd a12)))
             (attrs1))
    | fun tups => IsPrefix _ (@?C1 tups) =>
      let attrs1 := TermAttributes C1 in
      k (map (fun a12 => ("FindSuffixIndex", (fst a12, snd a12)))
             (attrs1))
    | _ => k_fail WhereClause k
  end.

Ltac SuffixIndexUse SC F indexed_attrs f k k_fail :=
     match type of f with
(* FindSuffix Search Terms *)
       | forall a, {IsSuffix (GetAttribute _ ?fd') ?X} + {_} =>
         let fd := eval simpl in (bindex fd') in
             let H := fresh in
             assert (List.In {| KindNameKind := "FindSuffixIndex";
                                KindNameName := fd|} indexed_attrs) as H
                 by (clear; simpl; intuition eauto); clear H;
             k ({| KindNameKind := "FindSuffixIndex";
                   KindNameName := fd|}, X) (fun _ : @Tuple SC => true)
       | forall a, {IsPrefix ?X (GetAttribute _ ?fd')} + {_} =>
         let fd := eval simpl in (bindex fd') in
             let H := fresh in
             assert (List.In {| KindNameKind := "FindSuffixIndex";
                                KindNameName := fd|} indexed_attrs) as H
                 by (clear; simpl; intuition eauto); clear H;
             k ({| KindNameKind := "FindSuffixIndex";
                   KindNameName := fd|}, X) (fun _ : @Tuple SC => true)

       | _ => k_fail SC F indexed_attrs f k
     end.

      (* FindSuffix Search Terms *)
Ltac SuffixIndexUse_dep SC F indexed_attrs visited_attrs f T k k_fail :=
    match type of f with
      | forall a b, {IsSuffix (GetAttribute _ ?fd') (@?X a)} + {_} =>
        let fd := eval simpl in (bindex fd') in
            let H := fresh in
            assert (List.In {| KindNameKind := "FindSuffixIndex";
                               KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
          match eval simpl in
                (in_dec string_dec fd visited_attrs) with
            | right _ => k (fd :: visited_attrs)
                           ({| KindNameKind := "FindSuffixIndex";
                               KindNameName := fd |}, X)
                           (fun (a : T) (_ : @Tuple SC) => true)
            | left _ => k visited_attrs tt F
          end
      | forall a b, {IsPrefix (@?X a) (GetAttribute _ ?fd')} + {_} =>
        let fd := eval simpl in (bindex fd') in
            let H := fresh in
            assert (List.In {| KindNameKind := "FindSuffixIndex";
                               KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
          match eval simpl in
                (in_dec string_dec fd visited_attrs) with
            | right _ => k (fd :: visited_attrs)
                           ({| KindNameKind := "FindSuffixIndex";
                               KindNameName := fd |}, X)
                           (fun (a : T) (_ : @Tuple SC) => true)
            | left _ => k visited_attrs tt F
          end

      | _ => k_fail SC F indexed_attrs visited_attrs f T k
end.

Ltac createLastSuffixTerm f fds tail fs kind s k k_fail :=
  let is_equality := eval compute in (string_dec kind "FindSuffixIndex") in
      match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k {| FindSuffixIndexSearchTerm := Some X;
                                 FindSuffixItemSearchTerm := tail |}))
            || k {| FindSuffixIndexSearchTerm := None;
                    FindSuffixItemSearchTerm := tail |}
        | _ => k_fail f fds tail fs kind s k
      end.

Ltac createLastSuffixTerm_dep dom f fds tail fs kind s k k_fail :=
  let is_equality := eval compute in (string_dec kind "FindSuffixIndex") in
      match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k (fun x : dom => {| FindSuffixIndexSearchTerm := Some (X x);
                                                 FindSuffixItemSearchTerm := tail x |}))
                    || k (fun x : dom => {| FindSuffixIndexSearchTerm := None;
                                            FindSuffixItemSearchTerm := tail x |}))
        | _ => k_fail dom f fds tail fs kind s k
      end.

Ltac createEarlySuffixTerm f fds tail fs kind EarlyIndex LastIndex rest s k k_fail :=
  let is_equality := eval compute in (string_dec kind "FindSuffixIndex") in
      match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k (Some X, rest)))
            || k (@None (list string), rest)
        | _ => k_fail f fds tail fs kind EarlyIndex LastIndex rest s k
      end.

Ltac createEarlySuffixTerm_dep dom f fds tail fs kind EarlyIndex LastIndex rest s k k_fail :=
  let is_equality := eval compute in (string_dec kind "FindSuffixIndex") in
      match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k (fun x : dom => (Some (X x), rest x))))
            || k (fun x : dom => (@None (list string), rest x))
        | _ => k_fail f fds tail fs kind EarlyIndex LastIndex rest s k
      end.

Ltac SuffixIndexTactics f :=
  PackageIndexTactics
    matchFindSuffixIndex
    SuffixIndexUse createEarlySuffixTerm createLastSuffixTerm
    SuffixIndexUse_dep createEarlySuffixTerm_dep createLastSuffixTerm_dep f.
