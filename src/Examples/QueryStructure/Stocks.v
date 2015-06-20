Require Import Fiat.QueryStructure.Automation.MasterPlan.

Definition Market := string.
Definition StockType := nat.
Definition StockCode := nat.
Definition Date      := nat.
Definition Timestamp := nat.

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
              schema <STOCK_CODE :: StockCode,
                      FULL_NAME :: string,
                      MARKET :: Market,
                      TYPE :: StockType>
              where attributes [FULL_NAME; MARKET; TYPE] depend on [STOCK_CODE]; (* uniqueness, really *)
      relation TRANSACTIONS has
              schema <STOCK_CODE :: nat,
                      DATE :: Date,
                      TIME :: Timestamp,
                      PRICE :: N,
                      VOLUME :: N>
              where attributes [PRICE] depend on [STOCK_CODE; TIME] ]
    enforcing [attribute STOCK_CODE for TRANSACTIONS references STOCKS].

Definition StocksSig : ADTSig :=
  ADTsignature {
      Constructor "Init"               : unit                              -> rep,
      Method "AddStock"           : rep x (StocksSchema#STOCKS)       -> rep x bool,
      Method "AddTransaction"     : rep x (StocksSchema#TRANSACTIONS) -> rep x bool,
      Method "TotalVolume"        : rep x (StockCode * Date)          -> rep x N,
      Method "MaxPrice"           : rep x (StockCode * Date)          -> rep x option N,
      Method "TotalActivity"      : rep x (StockCode * Date)          -> rep x nat,
      Method "LargestTransaction" : rep x (StockType * Date)          -> rep x option N
    }.

Definition StocksSpec : ADT StocksSig :=
  QueryADTRep StocksSchema {
    Def Constructor "Init" (_: unit) : rep := empty,

    update "AddStock" (r : rep, stock: StocksSchema#STOCKS) : bool :=
        Insert stock into r!STOCKS,

    update "AddTransaction" (r : rep, transaction : StocksSchema#TRANSACTIONS) : bool :=
        Insert transaction into r!TRANSACTIONS,

    query "TotalVolume" (r : rep, params: StockCode * Date) : N :=
      SumN (For (transaction in r!TRANSACTIONS)
            Where (transaction!STOCK_CODE = fst params)
            Where (transaction!DATE = snd params)
            Return transaction!VOLUME),

    query "MaxPrice" (r : rep, params: StockCode * Date) : option N :=
      MaxN (For (transaction in r!TRANSACTIONS)
            Where (transaction!STOCK_CODE = fst params)
            Where (transaction!DATE = snd params)
            Return transaction!PRICE),

    query "TotalActivity" (r : rep, params: StockCode * Date) : nat :=
      Count (For (transaction in r!TRANSACTIONS)
            Where (transaction!STOCK_CODE = fst params)
            Where (transaction!DATE = snd params)
            Return ()),

    query "LargestTransaction" (r : rep, params: StockType * Date) : option N :=
      MaxN (For (stock in r!STOCKS) (transaction in r!TRANSACTIONS)
            Where (stock!TYPE = fst params)
            Where (transaction!DATE = snd params)
            Where (stock!STOCK_CODE = transaction!STOCK_CODE)
            Return (N.mul transaction!PRICE transaction!VOLUME))
}.

Definition SharpenedStocks :
  FullySharpened StocksSpec.
Proof.

  start honing QueryStructure.
  (* Automatically select indexes + data structure. *)
  {GenerateIndexesForAll
     matchEqIndex
     ltac:(fun attrlist => make_simple_indexes attrlist
                                               ltac:(LastCombineCase6 BuildEarlyEqualityIndex)
                                                      ltac:(LastCombineCase5 BuildLastEqualityIndex));
   match goal with
           | |- Sharpened _ => idtac (* Do nothing to the next Sharpened ADT goal. *)
           | |- _ => (* Otherwise implement each method using the indexed data structure *)
             plan
               EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
               EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep
   end.
   pose_headings_all.
     match goal with
     | |- appcontext[@BuildADT (IndexedQueryStructure ?Schema ?Indexes)] =>
       FullySharpenQueryStructure Schema Indexes
     end.
  (* 1231 Before. *)
     (* 1600 After.*)
  } 
  simpl; pose_string_ids; pose_headings_all;
  pose_search_term;  pose_SearchUpdateTerms.

  BuildQSIndexedBags' BuildEarlyEqualityBag BuildLastEqualityBag.
  (* 1700MB *)
  higher_order_reflexivityT.

  (* Uncomment this to see the mostly sharpened implementation *)
  (* partial_master_plan EqIndexTactics. *)
  (*master_plan EqIndexTactics. *)

Time Defined.
(* 2590MB  *)

Time Definition StocksImpl : ComputationalADT.cADT StocksSig :=
  Eval simpl in projT1 SharpenedStocks.
(* 3728MB *)
Print StocksImpl.
