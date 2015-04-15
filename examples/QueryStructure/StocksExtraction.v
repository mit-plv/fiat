Require Import Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Automation.QSImplementation
        StockswDelegation.

    Definition StocksDelegateReps
  : ilist (fun ns => Type) (qschemaSchemas StocksSchema).
      simpl.
      BuildQSDelegateReps StocksImpl.
    Defined.

    Definition StocksDelegateSearchUpdateTerms
    : ilist (fun ns => SearchUpdateTerms (schemaHeading (relSchema ns)))
             (qschemaSchemas StocksSchema).
      simpl; BuildQSDelegateSigs StocksImpl.
    Defined.

    Definition StocksDelegateImpls
    : i2list2 (fun ns (SearchTerm : SearchUpdateTerms (schemaHeading (relSchema ns)))
                   (Rep : Type) =>
                 ComputationalADT.pcADT
                   (BagSig (@Tuple (schemaHeading (relSchema ns)))
                           (BagSearchTermType SearchTerm)
                           (BagUpdateTermType SearchTerm))
                   Rep)
              StocksDelegateSearchUpdateTerms
              StocksDelegateReps.

      unfold StocksDelegateReps,
      StocksDelegateSearchUpdateTerms; simpl.
      BuildQSDelegateImpls StocksImpl.
    Defined.

    Definition ExtractWorthyStocksImpl : ComputationalADT.cADT StocksSig.
      let s := eval unfold StocksImpl in StocksImpl in
          let Impl := eval simpl in
          (Sharpened_Implementation s
                                    (LookupQSDelegateReps StocksDelegateReps)
                                    (LookupQSDelegateImpls StocksDelegateImpls)) in
              exact Impl.
    Defined.

    (* And we get a result worthy of extraction! *)
    Print ExtractWorthyStocksImpl.
