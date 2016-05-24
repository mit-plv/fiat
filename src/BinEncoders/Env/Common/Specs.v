Require Export
        Coq.Lists.List
        Fiat.Common
        Fiat.Computation.Notations
        Fiat.BinEncoders.Env.Common.Transformer
        Fiat.BinEncoders.Env.Common.Cache.

Delimit Scope binencoders_scope with binencoders.

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

  Definition encode_decode_correct_f
             (cache : Cache)
             (transformer : Transformer B)
             (predicate : A -> Prop)
             (encode : A -> CacheEncode -> B * CacheEncode)
             (decode : B -> CacheDecode -> option (A * B * CacheDecode)) :=
    forall env env' xenv data bin ext,
      Equiv env env' ->
      predicate data ->
      encode data env = (bin, xenv) ->
      exists xenv',
        decode (transform bin ext) env' = Some (data, ext, xenv')
        /\ Equiv xenv xenv'.

  Definition DecodeBindOpt2
             {C D}
             (a : option (A * B * D))
             (k : A -> B -> D -> option (C * B * D))
    : option (C * B * D) :=
    Ifopt a as a_opt Then
      match a_opt with (a, bin', env') => k a bin' env' end
      Else None.

  Definition DecodeBindOpt
             {C}
             (a : option (A * B))
             (k : A -> B -> option (C * B))
    : option (C * B) :=
    Ifopt a as a_opt Then
      match a_opt with (a, bin') => k a bin' end
    Else None.

End Specifications.

Notation "`( a , b , env ) <- c ; k" :=
  (DecodeBindOpt2 c%binencoders (fun a b env => k%binencoders)) : binencoders_scope.

Notation "`( a , b ) <- c ; k" :=
  (DecodeBindOpt c%binencoders (fun a b => k%binencoders)) : binencoders_scope.

Open Scope binencoders_scope.
Global Unset Implicit Arguments.
