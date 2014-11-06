Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation BuildADTRefinements
        KVEnsembles.

Open Scope string.

Section CacheSpec.

  Variable Key : Type.
  Variable Value : Type.

  Definition CacheSig : ADTSig :=
    ADTsignature {
        "EmptyCache"  : unit -> rep,
        "AddKey" : rep x (Key * Value) -> rep x bool,
        "UpdateKey" : rep x (Key * (Value -> Value)) -> rep x bool,
        "LookupKey"   : rep x Key -> rep x (option Value)
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
