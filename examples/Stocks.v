Require Import AutoDB.

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
                      PRICE :: nat,
                      VOLUME :: nat>
              where attributes [PRICE] depend on [STOCK_CODE; TIME] ]
    enforcing [attribute STOCK_CODE for TRANSACTIONS references STOCKS].

Definition StocksSig : ADTSig :=
  ADTsignature {
      "Init"               : unit                              → rep,
      "AddStock"           : rep × (StocksSchema#STOCKS)       → rep × bool,
      "AddTransaction"     : rep × (StocksSchema#TRANSACTIONS) → rep × bool,
      "TotalVolume"        : rep × (StockCode * Date)          → rep × nat,
      "MaxPrice"           : rep × (StockCode * Date)          → rep × nat,
      "TotalActivity"      : rep × (StockCode * Date)          → rep × nat,
      "LargestTransaction" : rep × Date                        → rep × nat
    }.

Definition StocksSpec : ADT StocksSig :=
  QueryADTRep StocksSchema {
    const "Init" (_: unit) : rep := empty,

    update "AddStock" (stock: StocksSchema#STOCKS) : bool :=
        Insert stock into STOCKS,

    update "AddTransaction" (transaction : StocksSchema#TRANSACTIONS) : bool :=
        Insert transaction into TRANSACTIONS,

    query "TotalVolume" (params: StockCode * Date) : nat :=
      SumN (For (transaction in TRANSACTIONS)
            Where (transaction!STOCK_CODE = fst params)
            Where (transaction!DATE = sdn params)
            Return transaction!VOLUME),

    query "MaxPrice" (params: StockCode * Date) : nat :=
      MaxN (For (transaction in TRANSACTIONS)
            Where (transaction!STOCK_CODE = fst params)
            Where (transaction!DATE = sdn params)
            Return transaction!PRICE),

    query "TotalActivity" (params: StockCode * Date) : nat :=
      Count (For (transaction in TRANSACTIONS)
            Where (transaction!STOCK_CODE = fst params)
            Where (transaction!DATE = sdn params)
            Return 1),

    query "LargestTransaction" (params: StockType * Date) : nat :=
      MaxN (For (stock in STOKES)
            For (transaction in TRANSACTIONS)
            Where (stock!TYPE = fst params)
            Where (transaction!DATE = snd params)
            Where (stock!STOCK_CODE = transaction!STOCK_CODE)
            Return (transaction!PRICE * transaction!VOLUME))
}.

Definition StocksStorage : @BagPlusBagProof (StocksSchema#STOCKS).
  makeIndex StocksSchema STOCKS [ TYPE; STOCK_CODE ].
Defined.

Definition TransactionsStorage : @BagPlusBagProof (StocksSchema#TRANSACTIONS).
  makeIndex StocksSchema TRANSACTIONS [ DATE; STOCK_CODE ].
Defined.

Definition TStocksBag := BagType StocksStorage.
Definition TTransactionsBag := BagType TransactionsStorage.

Definition Stocks_AbsR
           (or : UnConstrQueryStructure StocksSchema)
           (nr : (TStocksBag) * (TTransactionsBag)) : Prop :=
  or!STOCKS ≃ benumerate (fst nr) /\ or!TRANSACTIONS ≃ benumerate (snd nr).

Definition StocksDB :
  Sharpened StocksSpec.
Proof.
  plan Stocks_AbsR.
  Print Ltac plan.

  (*unfold cast, eq_rect_r, eq_rect, eq_sym.*)
  Notation "a ! b" := (a ``(b)).
  Notation "a == b" := (if string_dec a b then true else false).
  Notation "a != b" := (negb (beq_nat b a)) (at level 20, no associativity).
  Notation "a == b" := (beq_nat b a).
  repeat match goal with
           | [ H := _ |- _ ] => unfold H; clear H
         end.
  finish sharpening.
Defined.
