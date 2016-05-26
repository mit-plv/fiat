Require Export
        Coq.Lists.List
        Fiat.Common
        Fiat.Computation.Core
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
             (encode : A -> CacheEncode -> Comp (B * CacheEncode))
             (decode : B -> CacheDecode -> option (A * B * CacheDecode)) :=
    (forall env env' xenv data bin ext,
      Equiv env env' ->
      predicate data ->
      encode data env ↝ (bin, xenv) ->
      exists xenv',
        decode (transform bin ext) env' = Some (data, ext, xenv')
        /\ Equiv xenv xenv') /\
    (forall env env' xenv' data bin ext,
        Equiv env env'
        -> decode bin env' = Some (data, ext, xenv')
        -> exists bin' xenv,
            encode data env ↝ (bin', xenv)
            /\ bin = transform bin' ext
            /\ predicate data
            /\ Equiv xenv xenv').

  Definition DecodeBindOpt2
             {C D E}
             (a : option (A * B * D))
             (k : A -> B -> D -> option (C * E * D))
    : option (C * E * D) :=
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

Section DecodeWMeasure.
  Context {A : Type}. (* data type *)
  Context {B : Type}. (* bin type *)
  Context {cache : Cache}.
  Context {transformer : Transformer B}.

  Variable A_encode_Spec : A -> CacheEncode -> Comp (B * CacheEncode).
  Variable A_decode : B -> CacheDecode -> option (A * B * CacheDecode).
  Variable A_decode_pf : encode_decode_correct_f cache transformer (fun _ => True) A_encode_Spec A_decode.

  Definition Decode_w_Measure_lt
        (b : B)
        (cd : CacheDecode)
        (A_decode_lt
         : forall  (b : B)
                   (cd : CacheDecode)
                   (a : A)
                   (b' : B)
                   (cd' : CacheDecode),
            A_decode b cd = Some (a, b', cd')
      -> lt_B b' b)
    : option (A * {b' : B | lt_B b' b} * CacheDecode).
    destruct (A_decode b cd) as [ [ [ a b' ] cd' ] | ] eqn: Heqo ;
      [ refine (Some (a, exist _ b' (A_decode_lt _ _ _ _ _ Heqo), cd'))
        | exact None ].
  Defined.

  Definition Decode_w_Measure_le
             (b : B)
             (cd : CacheDecode)
             (A_decode_le
              : forall  (b : B)
                        (cd : CacheDecode)
                        (a : A)
                        (b' : B)
                        (cd' : CacheDecode),
                 A_decode b cd = Some (a, b', cd')
                 -> le_B b' b)
    : option (A * {b' : B | le_B b' b} * CacheDecode).
    destruct (A_decode b cd) as [ [ [ a b' ] cd' ] | ] eqn: Heqo ;
      [ refine (Some (a, exist _ b' (A_decode_le _ _ _ _ _ Heqo), cd'))
      | exact None ].
  Defined.

End DecodeWMeasure.

Notation "`( a , b , env ) <- c ; k" :=
  (DecodeBindOpt2 c%binencoders (fun a b env => k%binencoders)) : binencoders_scope.

Notation "`( a , b ) <- c ; k" :=
  (DecodeBindOpt c%binencoders (fun a b => k%binencoders)) : binencoders_scope.

Open Scope binencoders_scope.
Global Unset Implicit Arguments.
