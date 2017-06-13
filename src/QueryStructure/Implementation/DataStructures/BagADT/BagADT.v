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
        Constructor sEmpty : rep,
        Method sFind      : rep * SearchTermType -> rep * (list ElementType),
        Method sEnumerate : rep -> rep * (list ElementType),
        Method sInsert    : rep * ElementType -> rep,
        Method sCount     : rep * SearchTermType  -> rep * nat,
        Method sDelete    : rep * SearchTermType  -> rep * (list ElementType),
        Method sUpdate    : rep * SearchTermType * UpdateTermType -> rep * (list ElementType)
  }.

  Definition BagSpec : ADT BagSig :=
    Def ADT {
        rep := @IndexedEnsemble ElementType,
        Def Constructor0 sEmpty : rep :=
          ret (Empty_set _),,

        Def Method1 sFind (r : rep) (f : SearchTermType)
          : rep * (list ElementType) :=
            results <- {l | EnsembleIndexedListEquivalence
                              (IndexedEnsemble_Intersection r (fun x => MatchSearchTerm f x = true)) l};
            ret (r, results),

        Def Method0 sEnumerate (r : rep)
          : rep * (list ElementType) :=
            results <- {l | EnsembleIndexedListEquivalence r l};
            ret (r, results),

        Def Method1 sInsert (r : rep) (element : ElementType) : rep :=
          freshIdx <- {freshIdx | UnConstrFreshIdx r freshIdx};
          ret (Add _ r {| elementIndex := freshIdx;
                          indexedElement := element |}),

        Def Method1 sCount (r : rep) (f : SearchTermType) : rep * (nat : Type) :=
          results <- {l | EnsembleIndexedListEquivalence
                            (IndexedEnsemble_Intersection r (fun x => MatchSearchTerm f x = true)) l};
          ret (r, length results),

        Def Method1 sDelete (r : rep) (f : SearchTermType)
        : rep * (list ElementType) :=
          deleted <- {l | EnsembleIndexedListEquivalence r l};
          ret (EnsembleDelete
                 r
                 (fun tup => MatchSearchTerm f tup = true),
               filter (MatchSearchTerm f) deleted),

        Def Method2 sUpdate (r : rep) (st : SearchTermType) (ut : UpdateTermType)
          : rep * (list ElementType) :=
            updated <- {l | EnsembleIndexedListEquivalence r l};
          ret (IndexedEnsembleUpdate r (fun tup => MatchSearchTerm st tup = true)
                                     (fun old new => new = (ApplyUpdateTerm ut old)),
                 filter (MatchSearchTerm st) updated)
        }.

End BagADT.
