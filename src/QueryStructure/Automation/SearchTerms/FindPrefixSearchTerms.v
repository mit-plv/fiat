Require Import
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Automation.Common
        Coq.Strings.Ascii.

(* Instances for building indexes with make simple indexes. *)
(* Every Kind of index is keyed on an inductive type with a single constructor*)
Definition FindPrefixIndex : string := "FindPrefixIndex".

(* This is our search term type. *)
Record FindPrefixSearchTerm
       (heading : RawHeading)
  :=
    { FindPrefixIndexSearchTerm : option (list ascii);
      FindPrefixItemSearchTerm : @RawTuple heading -> bool }.

Global Instance Aascii_eq : Query_eq ascii := {| A_eq_dec := ascii_dec |}.

(* This builds the type of searchterms and the matching function on them *)
Global Instance FindPrefixIndexDenotation
       (heading : RawHeading)
       (index : @Attributes heading)
       (projection : @RawTuple heading -> list ascii)
: @IndexDenotation "FindPrefixIndex" heading index :=
  {| DenoteIndex := FindPrefixSearchTerm heading; (* Pick search term type *)
     MatchIndex search_term item := (* matching function : DenoteIndex -> Tuple heading -> bool *)
       match FindPrefixIndexSearchTerm search_term with
         | Some indexSearchTerm =>
           if IsPrefix_dec (projection item) indexSearchTerm then
             FindPrefixItemSearchTerm search_term item
           else false
         | None =>
           FindPrefixItemSearchTerm search_term item
       end |}.

(* Extra type class magic for prefix indices. *)
Hint Extern 10 (@IndexDenotation "FindPrefixIndex" ?heading ?index) =>
let index_domain := eval hnf in (@Domain heading index) in
match index_domain with
  | list ascii =>
    apply (@FindPrefixIndexDenotation
             heading index
             (fun tup => GetAttributeRaw tup index ))
end
: typeclass_instances.

Ltac matchFindPrefixIndex qsSchema WhereClause k k_fail :=
  match WhereClause with
  | fun tups => IsPrefix (@?C1 tups) _ =>
    TermAttributes C1 ltac:(fun Ridx attr =>
                              k (@InsertOccurence _ qsSchema Ridx ("FindPrefixIndex", attr) (InitOccurence _)))
    | _ => k_fail qsSchema WhereClause k
  end.

Ltac PrefixIndexUse SC F indexed_attrs f k k_fail :=
     match type of f with
(* FindPrefix Search Terms *)
       | forall a, {IsPrefix (GetAttributeRaw _ ?fd) ?X} + {_} =>
             let H := fresh in
             assert (List.In (@Build_KindIndex SC FindPrefixIndex fd) indexed_attrs) as H
                 by (clear; simpl; intuition eauto); clear H;
             k ((@Build_KindIndex SC FindPrefixIndex fd), X) (fun _ : @RawTuple SC => true)
       | _ => k_fail SC F indexed_attrs f k
     end.

      (* FindPrefix Search Terms *)
Ltac PrefixIndexUse_dep SC F indexed_attrs visited_attrs f T k k_fail :=
    match type of f with
      | forall a b, {IsPrefix (GetAttributeRaw _ ?fd) (@?X a)} + {_} =>
            let H := fresh in
            assert (List.In (@Build_KindIndex SC FindPrefixIndex fd) indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
          match eval simpl in
                (in_dec fin_eq_dec fd visited_attrs) with
            | right _ => k (fd :: visited_attrs)
                           ((@Build_KindIndex SC FindPrefixIndex fd), X)
                           (fun (a : T) (_ : @RawTuple SC) => true)
            | left _ => k visited_attrs tt F
          end
      | _ => k_fail SC F indexed_attrs visited_attrs f T k
end.

Ltac createLastPrefixTerm f fds tail fs kind s k k_fail :=
  let is_equality := eval compute in (string_dec kind "FindPrefixIndex") in
      match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k {| FindPrefixIndexSearchTerm := Some X;
                                 FindPrefixItemSearchTerm := tail |}))
            || k {| FindPrefixIndexSearchTerm := None;
                    FindPrefixItemSearchTerm := tail |}
        | _ => k_fail f fds tail fs kind s k
      end.

Ltac createLastPrefixTerm_dep dom f fds tail fs kind s k k_fail :=
  let is_equality := eval compute in (string_dec kind "FindPrefixIndex") in
      match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k (fun x : dom => {| FindPrefixIndexSearchTerm := Some (X x);
                                                 FindPrefixItemSearchTerm := tail x |}))
                    || k (fun x : dom => {| FindPrefixIndexSearchTerm := None;
                                            FindPrefixItemSearchTerm := tail x |}))
        | _ => k_fail dom f fds tail fs kind s k
      end.

Ltac createEarlyPrefixTerm f fds tail fs kind EarlyIndex LastIndex rest s k k_fail :=
  let is_equality := eval compute in (string_dec kind "FindPrefixIndex") in
      match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k (Some X, rest)))
            || k (@None (list ascii), rest)
        | _ => k_fail f fds tail fs kind EarlyIndex LastIndex rest s k
      end.

Ltac createEarlyPrefixTerm_dep dom f fds tail fs kind EarlyIndex LastIndex rest s k k_fail :=
  let is_equality := eval compute in (string_dec kind "FindPrefixIndex") in
      match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k (fun x : dom => (Some (X x), rest x))))
            || k (fun x : dom => (@None (list ascii), rest x))
        | _ => k_fail dom f fds tail fs kind EarlyIndex LastIndex rest s k
      end.

Ltac PrefixIndexTactics f :=
  PackageIndexTactics
    matchFindPrefixIndex
    PrefixIndexUse createEarlyPrefixTerm createLastPrefixTerm
    PrefixIndexUse_dep createEarlyPrefixTerm_dep createLastPrefixTerm_dep f.
