Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        ADTSynthesis.Computation ADTSynthesis.ADT ADTSynthesis.ADTRefinement ADTSynthesis.ADTNotation ADTSynthesis.ADTRefinement.BuildADTRefinements
        ADTExamples.CacheADT.KVEnsembles.

Open Scope string.

Section CacheSpec.

  Variable Key : Type.
  Variable Value : Type.

  Definition CacheSig : ADTSig :=
    ADTsignature {
        "EmptyCache"  : unit → rep,
        "AddKey" : rep × (Key * Value) → rep × bool,
        "UpdateKey" : rep × (Key * (Value -> Value)) → rep × bool,
        "LookupKey"   : rep × Key → rep × (option Value)
  }.

  Definition CacheSpec : ADT CacheSig :=
    ADTRep (Ensemble (Key * Value)) {
        const "EmptyCache" (_ : unit) : rep :=
          ret (fun _ => False),
        meth "AddKey" (r : rep, kv : Key * Value) : bool :=
            { r' | (SubEnsembleInsert kv r (fst r')) /\
                   ((usedKey r (fst kv) /\ snd r' = false) \/
                    (~ usedKey r (fst kv) /\ snd r' = true))},
        meth "UpdateKey" (r : rep, kv : Key * (Value -> Value)) : bool :=
              { r' |
                (Same_set _ (fst r') (EnsembleUpdateKey (fst kv) r (snd kv)))
                 /\ ((usedKey r (fst kv) /\ snd r' = true) \/
                     (~ usedKey r (fst kv) -> snd r' = false))},
        meth "LookupKey" (r : rep, k : Key) : option Value :=
                v <- {v | ValidLookup r k v};
        ret (r, v)
      }.

End CacheSpec.
