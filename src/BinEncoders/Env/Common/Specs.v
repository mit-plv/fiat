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
             (decode : B -> CacheDecode -> option (A * B * CacheDecode))
             (decode_inv : CacheDecode -> Prop) :=
    (forall env env' xenv data bin ext,
      Equiv env env' ->
      predicate data ->
      encode data env ↝ (bin, xenv) ->
      exists xenv',
        decode (transform bin ext) env' = Some (data, ext, xenv')
        /\ Equiv xenv xenv') /\
    (forall env env' xenv' data bin ext,
        Equiv env env'
        -> decode_inv env'
        -> decode bin env' = Some (data, ext, xenv')
        -> decode_inv xenv'
           /\ exists bin' xenv,
            encode data env ↝ (bin', xenv)
            /\ bin = transform bin' ext
            /\ predicate data
            /\ Equiv xenv xenv').

  (* Definition that identifies properties of cache invariants for automation. *)
  Definition cache_inv_Property
             {cache : Cache}
             (P : CacheDecode -> Prop)
             (P_inv : (CacheDecode -> Prop) -> Prop) :=
    P_inv P.

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

Add Parametric Morphism
    A B
    (cache : Cache)
    (transformer : Transformer B)
    (predicate : A -> Prop)
    (decode : B -> CacheDecode -> option (A * B * CacheDecode))
    (decode_inv : CacheDecode -> Prop)
  : (fun encoder =>
       @encode_decode_correct_f A B cache transformer predicate
                               encoder decode decode_inv)
    with signature (pointwise_relation _ (pointwise_relation _ refineEquiv) ==> impl)
      as encode_decode_correct_refineEquiv.
Proof.
  unfold impl, pointwise_relation, encode_decode_correct_f;
    intuition eauto; intros.
  - eapply H1; eauto; apply H; eauto.
  - eapply H2; eauto.
  - destruct (H2 _ _ _ _ _ _ H0 H3 H4) as [ ? [? [? ?] ] ];
      intuition.
    repeat eexists; eauto; apply H; eauto.
Qed.

Section DecodeWMeasure.
  Context {A : Type}. (* data type *)
  Context {B : Type}. (* bin type *)
  Context {cache : Cache}.
  Context {transformer : Transformer B}.

  Variable A_encode_Spec : A -> CacheEncode -> Comp (B * CacheEncode).
  Variable A_decode : B -> CacheDecode -> option (A * B * CacheDecode).

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
    generalize (A_decode_lt b cd); clear.
    destruct (A_decode b cd) as [ [ [ a b' ] cd' ] | ]; intros;
      [ refine (Some (a, exist _ b' (H _ _ _ eq_refl), cd'))
        | exact None ].
  Defined.

  Lemma Decode_w_Measure_lt_eq
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
    : forall a' b' cd',
      A_decode b cd = Some (a', b', cd')
      -> exists pf,
        Decode_w_Measure_lt b cd A_decode_lt =
        Some (a', exist _ b' pf , cd').
  Proof.
    clear; intros; unfold Decode_w_Measure_lt.
    remember (A_decode_lt b cd); clear Heql.
    destruct (A_decode b cd) as [ [ [? ?] ? ] | ].
    injections; eauto.
    discriminate.
  Qed.

  Lemma Decode_w_Measure_lt_eq'
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
    : A_decode b cd = None
      -> Decode_w_Measure_lt b cd A_decode_lt = None.
  Proof.
    clear; intros; unfold Decode_w_Measure_lt.
    remember (A_decode_lt b cd); clear Heql.
    destruct (A_decode b cd) as [ [ [? ?] ? ] | ]; eauto.
    discriminate.
  Qed.

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
    generalize (A_decode_le b cd); clear.
    destruct (A_decode b cd) as [ [ [ a b' ] cd' ] | ]; intros;
      [ refine (Some (a, exist _ b' (H _ _ _ eq_refl), cd'))
        | exact None ].
  Defined.

  Lemma Decode_w_Measure_le_eq
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
    : forall a' b' cd',
      A_decode b cd = Some (a', b', cd')
      -> exists pf,
        Decode_w_Measure_le b cd A_decode_le =
        Some (a', exist _ b' pf , cd').
  Proof.
    clear; intros; unfold Decode_w_Measure_le.
    remember (A_decode_le b cd); clear Heql.
    destruct (A_decode b cd) as [ [ [? ?] ? ] | ].
    injections; eauto.
    discriminate.
  Qed.

  Lemma Decode_w_Measure_le_eq'
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
    : A_decode b cd = None
      -> Decode_w_Measure_le b cd A_decode_le = None.
  Proof.
    clear; intros; unfold Decode_w_Measure_le.
    remember (A_decode_le b cd); clear Heql.
    destruct (A_decode b cd) as [ [ [? ?] ? ] | ]; eauto.
    discriminate.
  Qed.

End DecodeWMeasure.

Notation "`( a , b , env ) <- c ; k" :=
  (DecodeBindOpt2 c%binencoders (fun a b env => k%binencoders)) : binencoders_scope.

Notation "`( a , b ) <- c ; k" :=
  (DecodeBindOpt c%binencoders (fun a b => k%binencoders)) : binencoders_scope.

Open Scope binencoders_scope.
Global Unset Implicit Arguments.
