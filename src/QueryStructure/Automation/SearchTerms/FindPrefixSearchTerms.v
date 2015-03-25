Require Import
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureNotations
        ADTSynthesis.QueryStructure.Specification.SearchTerms.ListPrefix
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        ADTSynthesis.QueryStructure.Automation.IndexSelection
        Coq.Strings.Ascii.

(* Instances for building indexes with make simple indexes. *)
(* Every Kind of index is keyed on an inductive type with a single constructor*)
Definition FindPrefixIndex : string := "FindPrefixIndex".

(* This is our search term type. *)
Record FindPrefixSearchTerm
       (heading : Heading)
  :=
    { FindPrefixIndexSearchTerm : option (list ascii);
      FindPrefixItemSearchTerm : @Tuple heading -> bool }.

Global Instance Aascii_eq : Query_eq ascii := {| A_eq_dec := ascii_dec |}.

(* This builds the type of searchterms and the matching function on them *)
Global Instance FindPrefixIndexDenotation
       (heading : Heading)
       (index : @Attributes heading)
       (projection : @Tuple heading -> list ascii)
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
             (fun tup => GetAttribute tup index ))
end
: typeclass_instances.

Ltac matchFindPrefixIndex WhereClause k :=
  match WhereClause with
    | fun tups => IsPrefix (@?C1 tups) _ =>
      let attrs1 := TermAttributes C1 in
      k (map (fun a12 => (FindPrefixIndex, (fst a12, snd a12)))
             (attrs1))
  end.
