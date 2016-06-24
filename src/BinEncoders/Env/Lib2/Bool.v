Require Import
        Fiat.Common
        Fiat.Computation.Notations
        Fiat.BinEncoders.Env.Common.Specs.

Unset Implicit Arguments.

Section Bool.

  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : TransformerUnitOpt transformer bool}.

  Definition encode_bool_Spec (b : bool) (ctx : CacheEncode) :=
    ret (transform_push_opt b transform_id, ctx).

End Bool.
