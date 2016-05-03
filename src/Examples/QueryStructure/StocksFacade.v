Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import Bedrock.Memory.

Instance : Query_eq (Word.word n) :=
  { A_eq_dec := @Word.weq n }.
Opaque Word.weq.
Opaque Word.natToWord.
Opaque Word.wlt_dec.
Definition WordMax (w w' : W) :=
  if Word.wlt_dec w w' then w' else w.
Definition MaxW (rows : Comp (list W)) : Comp (option W) :=
  FoldAggregateOption WordMax rows.
Definition SumW rows := FoldAggregate (@Word.wplus 32) (Word.natToWord 32 0) rows.

Definition Market := W.
Definition StockType := W.
Definition StockCode := W.
Definition Date      := W.
Definition Timestamp := W.

Definition TYPE := "TYPE".
Definition MARKET := "MARKET".
Definition STOCK_CODE := "STOCK_CODE".
Definition FULL_NAME := "FULL_NAME".

Definition DATE := "DATE".
Definition TIME := "TIME".
Definition PRICE := "PRICE".
Definition VOLUME := "VOLUME".

Definition STOCKS := "STOCKS".
Definition TRANSACTIONS := "TRANSACTIONS".

Definition StocksSchema :=
  Query Structure Schema
    [ relation STOCKS has
              schema <STOCK_CODE :: W,
                      FULL_NAME :: W,
                      MARKET :: W,
                      TYPE :: W>
              where (UniqueAttribute ``STOCK_CODE); (* uniqueness, really *)
      relation TRANSACTIONS has
              schema <STOCK_CODE :: W,
                      DATE :: W,
                      TIME :: W,
                      PRICE :: W,
                      VOLUME :: W> ]
    enforcing [attribute STOCK_CODE for TRANSACTIONS references STOCKS].

Definition StocksSpec : ADT _ :=
  Def ADT {
    rep := QueryStructure StocksSchema,
    Def Constructor0 "Init" : rep := empty,,

    Def Method1 "AddStock" (r : rep) (stock: StocksSchema#STOCKS) : rep * bool :=
        Insert stock into r!STOCKS,

    Def Method1 "AddTransaction" (r : rep) (transaction : StocksSchema#TRANSACTIONS) : rep * bool :=
        Insert transaction into r!TRANSACTIONS,

    Def Method2 "TotalVolume" (r : rep) (code : StockCode) (date : Date) : rep * W :=
          sum <- SumW (For (transaction in r!TRANSACTIONS)
                           Where (transaction!STOCK_CODE = code)
                           Where (transaction!DATE = date)
                           Return transaction!VOLUME);
    ret (r, sum),

    Def Method2 "MaxPrice" (r : rep) (code : StockCode) (date : Date) : rep * option W :=
      max <- MaxW (For (transaction in r!TRANSACTIONS)
                       Where (transaction!STOCK_CODE = code)
                       Where (transaction!DATE = date)
                       Return transaction!PRICE);
     ret (r, max),

    Def Method2 "TotalActivity" (r : rep) (code : StockCode) (date : Date) : rep * W :=
       count <- Count (For (transaction in r!TRANSACTIONS)
                           Where (transaction!STOCK_CODE = code)
                           Where (transaction!DATE = date)
                           Return ());
     ret (r, Word.natToWord 32 count),

    Def Method2 "LargestTransaction" (r : rep) (type : StockType) (date : Date) : rep * option W :=
        max <- MaxW (For (stock in r!STOCKS) (transaction in r!TRANSACTIONS)
                         Where (stock!TYPE = type)
                         Where (transaction!DATE = date)
                         Where (stock!STOCK_CODE = transaction!STOCK_CODE)
                         Return (Word.wmult transaction!PRICE transaction!VOLUME));
     ret (r, max)
}%methDefParsing.

Definition SharpenedStocks :
  MostlySharpened StocksSpec.
Proof.
  start sharpening ADT.
  simpl; pose_string_hyps; pose_heading_hyps.
  start_honing_QueryStructure'.
  hone method "AddStock".
  { setoid_rewrite UniqueAttribute_symmetry.
    setoid_rewrite (@refine_uniqueness_check_into_query' StocksSchema Fin.F1 _ _ _ _).
    setoid_rewrite refine_Count.
    simplify with monad laws; simpl in *; subst.
    setoid_rewrite refine_pick_eq'.
    setoid_rewrite refine_bind_unit.
    setoid_rewrite refine_If_Then_Else_Duplicate.
    finish honing. }
  GenerateIndexesForAll EqExpressionAttributeCounter
  ltac:(fun attrlist =>
          let attrlist' := eval compute in (PickIndexes _ (CountAttributes' attrlist)) in
              make_simple_indexes attrlist'
                                  ltac:(LastCombineCase6 BuildEarlyEqualityIndex)
                                         ltac:(LastCombineCase5 BuildLastEqualityIndex)).
  + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + setoid_rewrite refine_For_rev; simplify with monad laws.
    plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + setoid_rewrite refine_For_rev; simplify with monad laws.
    plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + setoid_rewrite refine_For_rev; simplify with monad laws.
    plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + setoid_rewrite refine_For_rev; simplify with monad laws.
    plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + setoid_rewrite refine_For_rev; simplify with monad laws.
    plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + setoid_rewrite refine_For_rev; simplify with monad laws.
    plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + hone method "AddStock".
    { simpl in *; subst.
      simplify with monad laws.
      unfold ilist2_hd at 1; simpl.
      repeat setoid_rewrite rev_length.
      repeat setoid_rewrite map_length.
      setoid_rewrite refine_pick_eq'; simplify with monad laws.
      repeat setoid_rewrite refine_If_Then_Else_Bind.
      repeat setoid_rewrite refineEquiv_bind_bind.
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
      unfold H1; eapply refine_under_bind; intros; set_evars.
      rewrite (CallBagFind_fst H0); simpl.
      finish honing.
    }
    hone method "AddTransaction".
    { simpl in *; subst.
      setoid_rewrite refine_Count; simplify with monad laws.
      setoid_rewrite app_nil_r;
        setoid_rewrite map_map; simpl.
      unfold ilist2_hd at 1; simpl.
      setoid_rewrite rev_length.
      setoid_rewrite map_length.
      setoid_rewrite refine_pick_eq'; simplify with monad laws.
      repeat setoid_rewrite refine_If_Then_Else_Bind.
      repeat setoid_rewrite refineEquiv_bind_bind.
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
      unfold H1.
      eapply refine_under_bind; intros; set_evars.
      rewrite (CallBagFind_fst H0); simpl.
      finish honing.
    }
    hone method "TotalVolume".
    { simpl in *; subst; simplify with monad laws.
      unfold H1; eapply refine_under_bind; intros; set_evars.
      rewrite (CallBagFind_fst H0); simpl.
      setoid_rewrite refine_pick_eq'; simplify with monad laws.
      rewrite app_nil_r, map_map; unfold ilist2_hd; simpl.
      finish honing.
    }
    hone method "MaxPrice".
    { simpl in *; subst; simplify with monad laws.
      unfold H1; eapply refine_under_bind; intros; set_evars.
      rewrite (CallBagFind_fst H0); simpl.
      setoid_rewrite refine_pick_eq'; simplify with monad laws.
      rewrite app_nil_r, map_map; unfold ilist2_hd; simpl.
      finish honing.
    }
    hone method "TotalActivity".
    { simpl in *; subst.
      setoid_rewrite refine_Count; simplify with monad laws.
      unfold H1; eapply refine_under_bind; intros; set_evars.
      rewrite (CallBagFind_fst H0); simpl.
      setoid_rewrite refine_pick_eq'; simplify with monad laws.
      rewrite app_nil_r, map_map; unfold ilist2_hd; simpl.
      rewrite rev_length, map_length.
      finish honing.
    }
    hone method "LargestTransaction".
    { simpl in *; subst; simplify with monad laws.
      unfold H1; eapply refine_under_bind; intros; set_evars.
      rewrite (CallBagFind_fst H0); simpl.
      etransitivity.
      eapply refine_under_bind_both.
      eapply (@Join_Comp_Lists_eq StocksSchema Index (Fin.FS Fin.F1)).
      intros; finish honing.
      simplify with monad laws.
      unfold H2; apply refine_under_bind; set_evars.
      intros.
      apply Join_Comp_Lists_eq' in H4; rewrite H4.
      setoid_rewrite refine_pick_eq'; simplify with monad laws.
      simpl.
      finish honing.
    }
    simpl; eapply reflexivityT.
  + unfold CallBagFind, CallBagInsert.
    pose_headings_all.
    match goal with
    | |- appcontext[ @BuildADT (IndexedQueryStructure ?Schema ?Indexes) ] =>
      FullySharpenQueryStructure Schema Indexes
    end.

Time Defined.
(* 2590MB  *)

Time Definition StocksImpl :=
  Eval simpl in (fst (projT1 SharpenedStocks)).
Print StocksImpl.
