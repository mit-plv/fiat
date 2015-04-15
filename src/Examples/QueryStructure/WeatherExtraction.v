Require Import Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Automation.QSImplementation
        WeatherwDelegation.

    Definition WeatherStationDelegateReps
  : ilist (fun ns => Type) (qschemaSchemas WeatherSchema).
      simpl.
      BuildQSDelegateReps WeatherStationImpl.
    Defined.

    Definition WeatherStationDelegateSearchUpdateTerms
    : ilist (fun ns => SearchUpdateTerms (schemaHeading (relSchema ns)))
             (qschemaSchemas WeatherSchema).
      simpl; BuildQSDelegateSigs WeatherStationImpl.
    Defined.

    Definition WeatherStationDelegateImpls
    : i2list2 (fun ns (SearchTerm : SearchUpdateTerms (schemaHeading (relSchema ns)))
                   (Rep : Type) =>
                 ComputationalADT.pcADT
                   (BagSig (@Tuple (schemaHeading (relSchema ns)))
                           (BagSearchTermType SearchTerm)
                           (BagUpdateTermType SearchTerm))
                   Rep)
              WeatherStationDelegateSearchUpdateTerms
              WeatherStationDelegateReps.

      unfold WeatherStationDelegateReps,
      WeatherStationDelegateSearchUpdateTerms; simpl.
      BuildQSDelegateImpls WeatherStationImpl.
    Defined.

    Definition ExtractWorthyWeatherStationImpl : ComputationalADT.cADT WeatherSig.
      let s := eval unfold WeatherStationImpl in WeatherStationImpl in
          let Impl := eval simpl in
          (Sharpened_Implementation s
                                    (LookupQSDelegateReps WeatherStationDelegateReps)
                                    (LookupQSDelegateImpls WeatherStationDelegateImpls)) in
              exact Impl.
    Defined.

    (* And we get a result worthy of extraction! *)
    Print ExtractWorthyWeatherStationImpl.
