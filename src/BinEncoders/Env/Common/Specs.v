Require Export
        Coq.Lists.List
        Fiat.BinEncoders.Env.Common.Transformer
        Fiat.BinEncoders.Env.Common.Cache.

Set Implicit Arguments.

Section Specifications.
  Variable A : Type.
  Variable B : Type.

  Definition encode_decode_correct
             (cache : Cache)
             (transformer : Transformer B)
             (predicate : A -> Prop)
             (encode : A -> CacheEncode -> B * CacheEncode)
             (decode : B -> CacheDecode -> A * B * CacheDecode) :=
    forall env env' xenv xenv' data data' bin ext ext',
      Equiv env env' ->
      predicate data ->
      encode data env = (bin, xenv) ->
      decode (transform bin ext) env' = (data', ext', xenv') ->
      Equiv xenv xenv' /\ data = data' /\ ext = ext'.

  (* Definition encode_decode_correct_deep
             (cache : Cache)
             (transformer : Transformer)
             (predicate : A -> Prop)
             (encode : A -> CacheEncode -> bin * CacheEncode)
             (decode :  bin -> CacheDecode -> option (A * bin * CacheDecode)) :=
    forall env env' xenv xenv' data data' bin ext ext',
      Equiv env env' ->
      predicate data ->
      encode data env = (bin, xenv) ->
      (decode (transform bin ext) env' = Some (data', ext', xenv') <-> Equiv xenv xenv' /\ data = data' /\ ext = ext'). *)
End Specifications.
