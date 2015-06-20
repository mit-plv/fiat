Require Export Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Automation.QSImplementation.

Ltac master_plan' matchIndex
     BuildEarlyIndex BuildLastIndex
     IndexUse createEarlyTerm createLastTerm
     IndexUse_dep createEarlyTerm_dep createLastTerm_dep
     BuildEarlyBag BuildLastBag :=
  (* Implement constraints as queries. *)
  start honing QueryStructure;
  (* Automatically select indexes + data structure. *)
  [GenerateIndexesForAll
     matchIndex
     ltac:(fun attrlist => make_simple_indexes attrlist BuildEarlyIndex BuildLastIndex;
           match goal with
           | |- Sharpened _ => idtac (* Do nothing to the next Sharpened ADT goal. *)
           | |- _ => (* Otherwise implement each method using the indexed data structure *)
             plan IndexUse createEarlyTerm createLastTerm
                  IndexUse_dep createEarlyTerm_dep createLastTerm_dep
           end;
           pose_headings_all;
           match goal with
           | |- appcontext[@BuildADT (IndexedQueryStructure ?Schema ?Indexes)] =>
             FullySharpenQueryStructure Schema Indexes
           end
          )
  | simpl; pose_string_ids; pose_headings_all;
    pose_search_term;  pose_SearchUpdateTerms;

    BuildQSIndexedBags' BuildEarlyBag BuildLastBag
  | higher_order_reflexivityT ].

(* This planner variant stops after planning queries for Bags, in
   case we want to inspect the results. *)
Ltac partial_master_plan' matchIndex
     BuildEarlyIndex BuildLastIndex
     IndexUse createEarlyTerm createLastTerm
     IndexUse_dep createEarlyTerm_dep createLastTerm_dep
     BuildEarlyBag BuildLastBag :=
  (* Implement constraints as queries. *)
  start honing QueryStructure;
  (* Automatically select indexes + data structure. *)
  [GenerateIndexesForAll
     matchIndex
     ltac:(fun attrlist => make_simple_indexes attrlist BuildEarlyIndex BuildLastIndex;
           match goal with
           | |- Sharpened _ => idtac (* Do nothing to the next Sharpened ADT goal. *)
           | |- _ => (* Otherwise implement each method using the indexed data structure *)
             plan IndexUse createEarlyTerm createLastTerm
                  IndexUse_dep createEarlyTerm_dep createLastTerm_dep
           end;
           pose_headings_all)
  |
  |  ].

   Ltac matchEqIndex qsSchema WhereClause k := fail.
   Ltac EqIndexUse SC F indexed_attrs f k := fail.
   Ltac createEarlyEqualityTerm f fds tail fs kind EarlyIndex LastIndex rest s k := fail.
   Ltac createLastEqualityTerm f fds tail fs kind s k := fail.
   Ltac EqIndexUse_dep SC F indexed_attrs visited_attrs f T k := fail.
   Ltac createEarlyEqualityTerm_dep dom f fds tail fs kind EarlyIndex LastIndex rest s k := fail.
   Ltac createLastEqualityTerm_dep dom f fds tail fs kind s k := fail.

Ltac EqIndexTactics f :=
  PackageIndexTactics matchEqIndex
    ltac:(LastCombineCase6 BuildEarlyEqualityIndex)
    ltac:(LastCombineCase5 BuildLastEqualityIndex)
    EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
    EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep
    BuildEarlyEqualityBag BuildLastEqualityBag
    f.

Ltac master_plan IndexTactics := IndexTactics master_plan'.
Ltac partial_master_plan IndexTactics := IndexTactics partial_master_plan'.

Ltac simple_master_plan := master_plan EqIndexTactics.
Ltac simple_partial_master_plan := partial_master_plan EqIndexTactics.
