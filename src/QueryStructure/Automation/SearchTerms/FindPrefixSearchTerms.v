Require Import
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureNotations
        ADTSynthesis.QueryStructure.Specification.SearchTerms.ListPrefix
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        Coq.Strings.Ascii.

(* Instances for building indexes with make simple indexes. *)
(* Every Kind of index is keyed on an inductive type with a single constructor*)
Inductive FindPrefixIndex : Set := findPrefixIndex.

(* This is our search term type. *)
Record FindPrefixSearchTerm
       (heading : Heading)
  :=
    { IndexSearchTerm : option (list ascii);
      ItemSearchTerm : @Tuple heading -> bool }.

Global Instance Aascii_eq : Query_eq ascii := {| A_eq_dec := ascii_dec |}.

(* This builds the type of searchterms and the matching function on them *)
Global Instance IndexedIndexDenotation
       (heading : Heading)
       (index : @Attributes heading)
       (projection : @Tuple heading -> list ascii)
: @IndexDenotation FindPrefixIndex heading index :=
  {| DenoteIndex := FindPrefixSearchTerm heading; (* Pick search term type *)
     MatchIndex search_term item := (* matching function : DenoteIndex -> Tuple heading -> bool *)
       match IndexSearchTerm search_term with
         | Some indexSearchTerm =>
           if IsPrefix_dec (projection item) indexSearchTerm then
             ItemSearchTerm search_term item
           else false
         | None =>
           ItemSearchTerm search_term item
       end |}.

(* Extra type class magic for inverted indices. *)
Hint Extern 10 (@IndexDenotation FindPrefixIndex ?heading ?index) =>
let index_domain := eval hnf in (@Domain heading index) in
match index_domain with
  | list ascii =>
    apply (@IndexedIndexDenotation
             heading index
             (fun tup => GetAttribute tup index ))
end
: typeclass_instances.
