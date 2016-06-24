Require Import
        Fiat.Common
        Fiat.Computation.Notations
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.WordFacts.

Unset Implicit Arguments.
Section Option.

  Context {sz : nat}.
  Context {A : Type}.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.

  Variable encode_A : A -> CacheEncode -> Comp (B * CacheEncode).
  
  Definition encode_option_Spec
             (encode_None : CacheEncode -> Comp (B * CacheEncode))
             (a_opt : option A)
    := match a_opt with
       | Some a => encode_A a
       | None => encode_None
       end.

End Option.
