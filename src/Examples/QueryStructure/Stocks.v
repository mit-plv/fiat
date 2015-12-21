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
      Constructor "Init"               : rep,
      Method "AddStock"           : rep * (StocksSchema#STOCKS)       -> rep * bool,
      Method "AddTransaction"     : rep * (StocksSchema#TRANSACTIONS) -> rep * bool,
      Method "TotalVolume"        : rep * StockCode * Date          -> rep * N,
      Method "MaxPrice"           : rep * StockCode * Date          -> rep * (option N),
      Method "TotalActivity"      : rep * StockCode * Date          -> rep * nat,
      Method "LargestTransaction" : rep * StockType * Date          -> rep * (option N)
    }.

Definition StocksSpec : ADT StocksSig :=
  QueryADTRep StocksSchema {
    Def Constructor0 "Init" : rep := empty,

    Def Method1 "AddStock" (r : rep) (stock: StocksSchema#STOCKS) : rep * bool :=
        Insert stock into r!STOCKS,

    Def Method1 "AddTransaction" (r : rep) (transaction : StocksSchema#TRANSACTIONS) : rep * bool :=
        Insert transaction into r!TRANSACTIONS,

    Def Method2 "TotalVolume" (r : rep) (code : StockCode) (date : Date) : rep * N :=
          sum <- SumN (For (transaction in r!TRANSACTIONS)
                           Where (transaction!STOCK_CODE = code)
                           Where (transaction!DATE = date)
                           Return transaction!VOLUME);
    ret (r, sum),

    Def Method2 "MaxPrice" (r : rep) (code : StockCode) (date : Date) : rep * option N :=
      max <- MaxN (For (transaction in r!TRANSACTIONS)
                       Where (transaction!STOCK_CODE = code)
                       Where (transaction!DATE = date)
                       Return transaction!PRICE);
     ret (r, max),

    Def Method2 "TotalActivity" (r : rep) (code : StockCode) (date : Date) : rep * nat :=
       count <- Count (For (transaction in r!TRANSACTIONS)
                           Where (transaction!STOCK_CODE = code)
                           Where (transaction!DATE = date)
                           Return ());
     ret (r, count),

    Def Method2 "LargestTransaction" (r : rep) (type : StockType) (date : Date) : rep * option N :=
        max <- MaxN (For (stock in r!STOCKS) (transaction in r!TRANSACTIONS)
                         Where (stock!TYPE = type)
                         Where (transaction!DATE = date)
                         Where (stock!STOCK_CODE = transaction!STOCK_CODE)
                         Return (N.mul transaction!PRICE transaction!VOLUME));
     ret (r, max)
}%methDefParsing.


Definition SharpenedStocks :
  FullySharpened StocksSpec.
Proof.
  start sharpening ADT.
  pose_string_hyps.
  eapply SharpenStep;
  [ match goal with
        |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _ _ _] =>
        eapply refineADT_BuildADT_Rep_refine_All with (AbsR := @DropQSConstraints_AbsR Rep);
          [ repeat (first [eapply refine_Constructors_nil
                          | eapply refine_Constructors_cons;
                            [ simpl; intros;
                              match goal with
                              | |- refine _ (?E _ _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _) => let H := fresh in set (H := E)
                              | |- refine _ (?E) => let H := fresh in set (H := E)
                              | _ => idtac
                              end;
                              (* Drop constraints from empty *)
                              try apply Constructor_DropQSConstraints;
                              cbv delta [GetAttribute] beta; simpl
                            | ] ])
          | repeat (first [eapply refine_Methods_nil
                          | eapply refine_Methods_cons;
                            [ simpl; intros;
                              match goal with
                              | |- refine _ (?E _ _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _) => let H := fresh in set (H := E)
                              | |- refine _ (?E) => let H := fresh in set (H := E)
                              | _ => idtac
                              end;
                              cbv delta [GetAttribute] beta; simpl | ]
                          ])]
    end | ].
  - doAny drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - hone representation using (@FiniteTables_AbsR StocksSchema).
    + simplify with monad laws.
      refine pick val _; simpl; intuition.
      eauto using FiniteTables_AbsR_QSEmptySpec.
    + doAny simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny simplify_queries
            Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny simplify_queries
            Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny simplify_queries
            Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + simpl.

      master_plan EqIndexTactics.

  (* Uncomment this to see the mostly sharpened implementation *)
  (* partial_master_plan EqIndexTactics. *)
  (*master_plan EqIndexTactics. *)

Time Defined.
(* 2590MB  *)

Time Definition StocksImpl : ComputationalADT.cADT StocksSig :=
  Eval simpl in projT1 SharpenedStocks.
(* 3728MB *)
Print StocksImpl.
