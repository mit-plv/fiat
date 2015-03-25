Require Import
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureNotations
        ADTSynthesis.QueryStructure.Specification.SearchTerms.InRange
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms.

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
Hint Extern 10 (@IndexDenotation RangeIndex ?heading ?index) =>
let index_domain := eval hnf in (@Domain heading index) in
match index_domain with
  | nat =>
    apply (@RangeIndexDenotation
             heading index
             (fun tup => GetAttribute tup index ))
end
: typeclass_instances.
