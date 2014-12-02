Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        ADTSynthesis.Common.Ensembles.IndexedEnsembles ADTSynthesis.Computation ADTSynthesis.ADT ADTSynthesis.ADTRefinement ADTSynthesis.ADTNotation
        ADTSynthesis.ADTRefinement.BuildADTRefinements.

Open Scope string.

Section BagADT.

  Variable ElementType : Type.
  Variable SearchTermType : Type.
  Variable UpdateTermType : Type.
  Variable SearchTermMatcher : SearchTermType -> ElementType -> bool.
  Variable ApplyUpdateTerm : UpdateTermType -> ElementType -> ElementType.

  Definition BagSig : ADTSig :=
    ADTsignature {
        Constructor "EmptyBag" : unit             -> rep,
        Method "Find"      : rep x SearchTermType -> rep x list ElementType,
        Method "Enumerate" : rep x unit -> rep x list ElementType,
        Method "Insert"    : rep x ElementType -> rep x unit,
        Method "Count"     : rep x SearchTermType  -> rep x nat,
        Method "Delete"    : rep x SearchTermType  -> rep x (list ElementType),
        Method "Update"    : rep x (SearchTermType * UpdateTermType) -> rep x unit
  }.

  Definition BagSpec : ADT BagSig :=
    ADTRep (IndexedEnsemble) {
        Def Constructor "EmptyBag" (_ : unit) : rep :=
          ret (Empty_set _),

        Def Method "Find" (r : rep, f : SearchTermType)
          : list ElementType :=
            results <- {l | EnsembleIndexedListEquivalence r l};
        ret (r, filter (SearchTermMatcher f) results),

        Def Method "Enumerate" (r : rep, f : unit)
          : list ElementType :=
            results <- {l | EnsembleIndexedListEquivalence r l};
        ret (r, results),

        Def Method "Insert" (r : rep, element : ElementType) : unit :=
          freshIdx <- {freshIdx | UnConstrFreshIdx r freshIdx};
        ret (Add _ r {| elementIndex := freshIdx;
                        indexedElement := element |}, ()),

        Def Method "Count" (r : rep, f : SearchTermType) : nat :=
          results <- {l | EnsembleIndexedListEquivalence r l};
        ret (r, length (filter (SearchTermMatcher f) results)),

        Def Method "Delete" (r : rep, f : SearchTermType)
        : list ElementType :=
          deleted <- {l | EnsembleIndexedListEquivalence r l};
          ret (EnsembleDelete
                 r
                 (fun tup => SearchTermMatcher f tup = true),
               filter (SearchTermMatcher f) deleted),

        Def Method "Update" (r : rep, f : SearchTermType * UpdateTermType) : unit :=
            ret (IndexedEnsembleUpdate r (fun tup => SearchTermMatcher (fst f) tup = true) (ApplyUpdateTerm (snd f)), tt)
        }.

End BagADT.
