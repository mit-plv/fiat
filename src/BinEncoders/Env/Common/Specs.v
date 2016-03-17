Require Export
        Coq.Lists.List
        Fiat.BinEncoders.Env.Common.Transformer
        Fiat.BinEncoders.Env.Common.Cache.

Set Implicit Arguments.

Section Specifications.
  Variable A : Type.

  Definition encode_decode_correct
             (cache : Cache)
             (transformer : Transformer)
             (predicate : A -> Prop)
             (encode : A -> CacheEncode -> bin * CacheEncode)
             (decode :  bin -> CacheDecode -> A * bin * CacheDecode) :=
    forall env env' xenv xenv' data data' bin ext ext',
      Equiv env env' ->
      predicate data ->
      encode data env = (bin, xenv) ->
      decode (transform bin ext) env' = (data', ext', xenv') ->
      Equiv xenv xenv' /\ data = data' /\ ext = ext'.

  Class decoder
        (cache : Cache)
        (transformer : Transformer)
        (predicate : A -> Prop)
        (encode : A -> CacheEncode -> bin * CacheEncode) :=
    { decode : bin -> CacheDecode -> A * bin * CacheDecode;
      decode_correct : encode_decode_correct cache transformer predicate encode decode }.
End Specifications.
