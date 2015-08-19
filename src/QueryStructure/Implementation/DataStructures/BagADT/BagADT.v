Require Import Coq.Strings.String
        Coq.omega.Omega
        Coq.Lists.List
        Coq.Logic.FunctionalExtensionality
        Coq.Sets.Ensembles
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Computation
        Fiat.ADT
        Fiat.ADTRefinement
        Fiat.ADTNotation
        Fiat.ADTRefinement.BuildADTRefinements.

Section BagADT.

  Local Open Scope string_scope.

  Variable ElementType : Type.
  Variable SearchTermType : Type.
  Variable UpdateTermType : Type.
  Variable MatchSearchTerm : SearchTermType -> ElementType -> bool.
  Variable ApplyUpdateTerm : UpdateTermType -> ElementType -> ElementType.

  Definition sEmpty := "Empty".
  Definition sFind := "Find".
  Definition sEnumerate := "Enumerate".
  Definition sInsert := "Insert".
  Definition sCount := "Count".
  Definition sDelete := "Delete".
  Definition sUpdate := "Update".

  (* Get rid of Bag. *)
  Definition BagSig :=
    ADTsignature {
        Constructor sEmpty : unit             -> rep,
        Method sFind      : rep x SearchTermType -> rep x list ElementType,
        Method sEnumerate : rep x unit -> rep x list ElementType,
        Method sInsert    : rep x ElementType -> rep x unit,
        Method sCount     : rep x SearchTermType  -> rep x nat,
        Method sDelete    : rep x SearchTermType  -> rep x (list ElementType),
        Method sUpdate    : rep x (SearchTermType * UpdateTermType) -> rep x (list ElementType)
  }.

  Definition BagSpec : ADT BagSig :=
    ADTRep (IndexedEnsemble) {
        Def Constructor sEmpty (_ : unit) : rep :=
          ret (Empty_set _),

        Def Method sFind (r : rep, f : SearchTermType)
          : list ElementType :=
            results <- {l | EnsembleIndexedListEquivalence r l};
            ret (r, filter (MatchSearchTerm f) results),

        Def Method sEnumerate (r : rep, f : unit)
          : list ElementType :=
            results <- {l | EnsembleIndexedListEquivalence r l};
            ret (r, results),

        Def Method sInsert (r : rep, element : ElementType) : unit :=
          freshIdx <- {freshIdx | UnConstrFreshIdx r freshIdx};
          ret (Add _ r {| elementIndex := freshIdx;
                          indexedElement := element |}, ()),

        Def Method sCount (r : rep, f : SearchTermType) : nat :=
          results <- {l | EnsembleIndexedListEquivalence r l};
        ret (r, length (filter (MatchSearchTerm f) results)),

        Def Method sDelete (r : rep, f : SearchTermType)
        : list ElementType :=
          deleted <- {l | EnsembleIndexedListEquivalence r l};
          ret (EnsembleDelete
                 r
                 (fun tup => MatchSearchTerm f tup = true),
               filter (MatchSearchTerm f) deleted),

        Def Method sUpdate (r : rep, f : SearchTermType * UpdateTermType) : list ElementType :=
            updated <- {l | EnsembleIndexedListEquivalence r l};
          ret (IndexedEnsembleUpdate r (fun tup => MatchSearchTerm (fst f) tup = true)
                                     (fun old new => new = (ApplyUpdateTerm (snd f) old)),
                 filter (MatchSearchTerm (fst f)) updated)
        }.

End BagADT.
