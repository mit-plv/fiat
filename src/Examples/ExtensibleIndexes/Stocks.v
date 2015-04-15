Require Import Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Automation.AutoDB.

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

    update "AddStock" (stock: StocksSchema#STOCKS) : bool :=
        Insert stock into STOCKS,

    update "AddTransaction" (transaction : StocksSchema#TRANSACTIONS) : bool :=
        Insert transaction into TRANSACTIONS,

    query "TotalVolume" (params: StockCode * Date) : N :=
      SumN (For (transaction in TRANSACTIONS)
            Where (transaction!STOCK_CODE = fst params)
            Where (transaction!DATE = snd params)
            Return transaction!VOLUME),

    query "MaxPrice" (params: StockCode * Date) : option N :=
      MaxN (For (transaction in TRANSACTIONS)
            Where (transaction!STOCK_CODE = fst params)
            Where (transaction!DATE = snd params)
            Return transaction!PRICE),

    query "TotalActivity" (params: StockCode * Date) : nat :=
      Count (For (transaction in TRANSACTIONS)
            Where (transaction!STOCK_CODE = fst params)
            Where (transaction!DATE = snd params)
            Return ()),

    query "LargestTransaction" (params: StockType * Date) : option N :=
      MaxN (For (stock in STOCKS) (transaction in TRANSACTIONS)
            Where (stock!TYPE = fst params)
            Where (transaction!DATE = snd params)
            Where (stock!STOCK_CODE = transaction!STOCK_CODE)
            Return (N.mul transaction!PRICE transaction!VOLUME))
}.

Definition StocksDB :
  Sharpened StocksSpec.
Proof.

  start honing QueryStructure.
  (* Old, explicit index selection*)
  (* make simple indexes using [[AREA_CODE]; [MEASUREMENT_TYPE; CELL_ID]]. *)
  make indexes using matchFindPrefixIndex.
  - initializer.
  - insertion
    ltac:(fun SC F indexed_attrs f k =>
            match goal with
              | _ => InclusionIndexUse SC F indexed_attrs f k
              | _ => RangeIndexUse SC F indexed_attrs f k
            end)
           ltac:(fun f fds tail fs kind EarlyIndex LastIndex rest s k =>
                   match goal with
                     | _ => createEarlyInclusionTerm f fds tail fs kind EarlyIndex LastIndex rest s k
                     | _ => createEarlyRangeTerm f fds tail fs kind EarlyIndex LastIndex rest s k
                   end)
                  ltac:(fun f fds tail fs kind s k =>
                          match goal with
                            | _ => createLastInclusionTerm f fds tail fs kind s k
                            | _ => createLastRangeTerm f fds tail fs kind s k
                          end)
                         ltac:(fun SC F indexed_attrs visited_attrs f T k =>
                                 match goal with
                                   | _ => InclusionIndexUse_dep SC F indexed_attrs visited_attrs f T k
                                   | _ => RangeIndexUse_dep SC F indexed_attrs visited_attrs f T k
                                 end)
                                randomCrab
                                ltac:(fun dom f fds tail fs kind rest s k =>
                                        match goal with
                                          | _ => createLastInclusionTerm_dep dom f fds tail fs kind rest s k
                                          | _ => createLastRangeTerm_dep dom f fds tail fs kind rest s k
                                        end).
  - insertion
    ltac:(fun SC F indexed_attrs f k =>
            match goal with
              | _ => InclusionIndexUse SC F indexed_attrs f k
              | _ => RangeIndexUse SC F indexed_attrs f k
            end)
           ltac:(fun f fds tail fs kind EarlyIndex LastIndex rest s k =>
                   match goal with
                     | _ => createEarlyInclusionTerm f fds tail fs kind EarlyIndex LastIndex rest s k
                     | _ => createEarlyRangeTerm f fds tail fs kind EarlyIndex LastIndex rest s k
                   end)
                  ltac:(fun f fds tail fs kind s k =>
                          match goal with
                            | _ => createLastInclusionTerm f fds tail fs kind s k
                            | _ => createLastRangeTerm f fds tail fs kind s k
                          end)
                         ltac:(fun SC F indexed_attrs visited_attrs f T k =>
                                 match goal with
                                   | _ => InclusionIndexUse_dep SC F indexed_attrs visited_attrs f T k
                                   | _ => RangeIndexUse_dep SC F indexed_attrs visited_attrs f T k
                                 end)
                                randomCrab
                                ltac:(fun dom f fds tail fs kind rest s k =>
                                        match goal with
                                          | _ => createLastInclusionTerm_dep dom f fds tail fs kind rest s k
                                          | _ => createLastRangeTerm_dep dom f fds tail fs kind rest s k
                                        end).
  - observer
    ltac:(fun SC F indexed_attrs f k =>
            match goal with
              | _ => InclusionIndexUse SC F indexed_attrs f k
              | _ => RangeIndexUse SC F indexed_attrs f k
            end)
           ltac:(fun f fds tail fs kind EarlyIndex LastIndex rest s k =>
                   match goal with
                     | _ => createEarlyInclusionTerm f fds tail fs kind EarlyIndex LastIndex rest s k
                     | _ => createEarlyRangeTerm f fds tail fs kind EarlyIndex LastIndex rest s k
                   end)
                  ltac:(fun f fds tail fs kind s k =>
                          match goal with
                            | _ => createLastInclusionTerm f fds tail fs kind s k
                            | _ => createLastRangeTerm f fds tail fs kind s k
                          end)
                         ltac:(fun SC F indexed_attrs visited_attrs f T k =>
                                 match goal with
                                   | _ => InclusionIndexUse_dep SC F indexed_attrs visited_attrs f T k
                                   | _ => RangeIndexUse_dep SC F indexed_attrs visited_attrs f T k
                                 end)
                                randomCrab
                                ltac:(fun dom f fds tail fs kind rest s k =>
                                        match goal with
                                          | _ => createLastInclusionTerm_dep dom f fds tail fs kind rest s k
                                          | _ => createLastRangeTerm_dep dom f fds tail fs kind rest s k
                                        end).
      - observer
    ltac:(fun SC F indexed_attrs f k =>
            match goal with
              | _ => InclusionIndexUse SC F indexed_attrs f k
              | _ => RangeIndexUse SC F indexed_attrs f k
            end)
           ltac:(fun f fds tail fs kind EarlyIndex LastIndex rest s k =>
                   match goal with
                     | _ => createEarlyInclusionTerm f fds tail fs kind EarlyIndex LastIndex rest s k
                     | _ => createEarlyRangeTerm f fds tail fs kind EarlyIndex LastIndex rest s k
                   end)
                  ltac:(fun f fds tail fs kind s k =>
                          match goal with
                            | _ => createLastInclusionTerm f fds tail fs kind s k
                            | _ => createLastRangeTerm f fds tail fs kind s k
                          end)
                         ltac:(fun SC F indexed_attrs visited_attrs f T k =>
                                 match goal with
                                   | _ => InclusionIndexUse_dep SC F indexed_attrs visited_attrs f T k
                                   | _ => RangeIndexUse_dep SC F indexed_attrs visited_attrs f T k
                                 end)
                                randomCrab
                                ltac:(fun dom f fds tail fs kind rest s k =>
                                        match goal with
                                          | _ => createLastInclusionTerm_dep dom f fds tail fs kind rest s k
                                          | _ => createLastRangeTerm_dep dom f fds tail fs kind rest s k
                                        end).
          - observer
    ltac:(fun SC F indexed_attrs f k =>
            match goal with
              | _ => InclusionIndexUse SC F indexed_attrs f k
              | _ => RangeIndexUse SC F indexed_attrs f k
            end)
           ltac:(fun f fds tail fs kind EarlyIndex LastIndex rest s k =>
                   match goal with
                     | _ => createEarlyInclusionTerm f fds tail fs kind EarlyIndex LastIndex rest s k
                     | _ => createEarlyRangeTerm f fds tail fs kind EarlyIndex LastIndex rest s k
                   end)
                  ltac:(fun f fds tail fs kind s k =>
                          match goal with
                            | _ => createLastInclusionTerm f fds tail fs kind s k
                            | _ => createLastRangeTerm f fds tail fs kind s k
                          end)
                         ltac:(fun SC F indexed_attrs visited_attrs f T k =>
                                 match goal with
                                   | _ => InclusionIndexUse_dep SC F indexed_attrs visited_attrs f T k
                                   | _ => RangeIndexUse_dep SC F indexed_attrs visited_attrs f T k
                                 end)
                                randomCrab
                                ltac:(fun dom f fds tail fs kind rest s k =>
                                        match goal with
                                          | _ => createLastInclusionTerm_dep dom f fds tail fs kind rest s k
                                          | _ => createLastRangeTerm_dep dom f fds tail fs kind rest s k
                                        end).
              - observer
    ltac:(fun SC F indexed_attrs f k =>
            match goal with
              | _ => InclusionIndexUse SC F indexed_attrs f k
              | _ => RangeIndexUse SC F indexed_attrs f k
            end)
           ltac:(fun f fds tail fs kind EarlyIndex LastIndex rest s k =>
                   match goal with
                     | _ => createEarlyInclusionTerm f fds tail fs kind EarlyIndex LastIndex rest s k
                     | _ => createEarlyRangeTerm f fds tail fs kind EarlyIndex LastIndex rest s k
                   end)
                  ltac:(fun f fds tail fs kind s k =>
                          match goal with
                            | _ => createLastInclusionTerm f fds tail fs kind s k
                            | _ => createLastRangeTerm f fds tail fs kind s k
                          end)
                         ltac:(fun SC F indexed_attrs visited_attrs f T k =>
                                 match goal with
                                   | _ => InclusionIndexUse_dep SC F indexed_attrs visited_attrs f T k
                                   | _ => RangeIndexUse_dep SC F indexed_attrs visited_attrs f T k
                                 end)
                                randomCrab
                                ltac:(fun dom f fds tail fs kind rest s k =>
                                        match goal with
                                          | _ => createLastInclusionTerm_dep dom f fds tail fs kind rest s k
                                          | _ => createLastRangeTerm_dep dom f fds tail fs kind rest s k
                                        end).
              - FullySharpenQueryStructure StocksSchema Index;
                implement_bag_methods.
                Time Defined.
(* *Only* 204 seconds for Defined! *)
