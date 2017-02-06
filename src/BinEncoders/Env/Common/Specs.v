Require Export
        Coq.Lists.List
        Fiat.Common
        Fiat.Computation.Core
        Fiat.Computation.Notations
        Fiat.BinEncoders.Env.Common.Notations
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

  Definition encode_decode_correct_f
             (cache : Cache)
             (transformer : Transformer B)
             (predicate : A -> Prop)
             (rest_predicate : A -> B -> Prop)
             (encode : A -> CacheEncode -> Comp (B * CacheEncode))
             (decode : B -> CacheDecode -> option (A * B * CacheDecode))
             (decode_inv : CacheDecode -> Prop) :=
    (forall env env' xenv data bin ext,
      Equiv env env' ->
      predicate data ->
      rest_predicate data ext ->
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

  Lemma DecodeBindOpt2_inv
        {C D E}
        (a_opt : option (A * B * D))
        (a : C * E * D)
        (k : A -> B -> D -> option (C * E * D))
    : DecodeBindOpt2 a_opt k = Some a ->
      exists a' b' d',
        a_opt = Some (a', b', d')
        /\ Some a = k a' b' d'.
  Proof.
    unfold DecodeBindOpt2; destruct a_opt as [ [ [a' b'] d'] | ];
      simpl; intros; first [discriminate | injections ].
    eexists _, _, _; intuition eauto.
  Qed.

  Lemma DecodeBindOpt_inv
        {C}
        (a_opt : option (A * B))
        (a : C * B)
        (k : A -> B -> option (C * B))
    : DecodeBindOpt a_opt k = Some a ->
      exists a' b',
        a_opt = Some (a', b')
        /\ Some a = k a' b'.
  Proof.
    unfold DecodeBindOpt; destruct a_opt as [ [a' b'] | ];
      simpl; intros; first [discriminate | injections ].
    eexists _, _; intuition eauto.
  Qed.

End Specifications.

Lemma DecodeBindOpt2_assoc {A B C D E F G} :
  forall (a_opt : option (A * B * D))
         (f : A -> B -> D -> option (C * E * D))
         (g : C -> E -> D -> option (F * G * D)),
    DecodeBindOpt2 (DecodeBindOpt2 a_opt f) g =
    DecodeBindOpt2 a_opt (fun a b c => DecodeBindOpt2 (f a b c) g).
Proof.
  destruct a_opt as [ [ [? ?] ?] | ]; simpl; intros; eauto.
Qed.

Lemma DecodeBindOpt2_under_bind {A B C D E} :
  forall (a_opt : option (A * B * D))
         (f f' : A -> B -> D -> option (C * E * D)),
         (forall a b d, f a b d = f' a b d)
         -> DecodeBindOpt2 a_opt f = DecodeBindOpt2 a_opt f'.
Proof.
  destruct a_opt as [ [ [? ?] ?] | ]; simpl; intros; eauto.
Qed.

Add Parametric Morphism
    A B
    (cache : Cache)
    (transformer : Transformer B)
    (predicate : A -> Prop)
    rest_predicate
    (decode : B -> CacheDecode -> option (A * B * CacheDecode))
    (decode_inv : CacheDecode -> Prop)
  : (fun encoder =>
       @encode_decode_correct_f A B cache transformer predicate
                               rest_predicate encoder decode decode_inv)
    with signature (pointwise_relation _ (pointwise_relation _ refineEquiv) ==> impl)
      as encode_decode_correct_refineEquiv.
Proof.
  unfold impl, pointwise_relation, encode_decode_correct_f;
    intuition eauto; intros.
  - eapply H1; eauto; apply H; eauto.
  - eapply H2; eauto.
  - destruct (H2 _ _ _ _ _ _ H0 H3 H4) as [ ? [? [? ?] ] ];
      intuition.
    repeat eexists; intuition eauto; apply H; eauto.
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
  (DecodeBindOpt2 c%bencode (fun a b env => k%bencode)) : binencoders_scope.

Notation "`( a , b ) <- c ; k" :=
  (DecodeBindOpt c%bencode (fun a b => k%bencode)) : binencoders_scope.

Open Scope binencoders_scope.
Global Unset Implicit Arguments.

Definition CorrectDecoderFor {A B} {cache : Cache}
           {transformer : Transformer B} Invariant FormatSpec :=
{ decodePlusCacheInv |
      exists P_inv,
        (cache_inv_Property (snd decodePlusCacheInv) P_inv
         -> encode_decode_correct_f (A := A) cache transformer Invariant (fun _ _ => True)
                                    FormatSpec
                                    (fst decodePlusCacheInv)
                                    (snd decodePlusCacheInv))
        /\ cache_inv_Property (snd decodePlusCacheInv) P_inv}.

Lemma Start_CorrectDecoderFor
      {A B} {cache : Cache}
      {transformer : Transformer B}
      Invariant
      FormatSpec
      (decoder decoder_opt : B -> CacheDecode -> option (A * B * CacheDecode))
      (cache_inv : CacheDecode -> Prop)
      (P_inv : (CacheDecode -> Prop) -> Prop)
      (decoder_OK :
         cache_inv_Property cache_inv P_inv
         -> encode_decode_correct_f (A := A) cache transformer Invariant (fun _ _ => True)
                                    FormatSpec decoder cache_inv)
      (cache_inv_OK : cache_inv_Property cache_inv P_inv)
      (decoder_opt_OK : forall b cd, decoder b cd = decoder_opt b cd)
  : @CorrectDecoderFor A B cache transformer Invariant FormatSpec.
Proof.
  exists (decoder_opt, cache_inv); exists P_inv; split; simpl; eauto.
  unfold encode_decode_correct_f in *; intuition; intros.
  - destruct (H1 _ _ _ _ _ ext H0 H3 H4 H5).
    rewrite decoder_opt_OK in H6; eauto.
  - rewrite <- decoder_opt_OK in H4; destruct (H2 _ _ _ _ _ _ H0 H3 H4); eauto.
  - rewrite <- decoder_opt_OK in H4; destruct (H2 _ _ _ _ _ _ H0 H3 H4); eauto.
Defined.

(* Shorthand for nondeterministically decoding a value. *)
Definition Pick_Decoder_For
      {A B} {cache : Cache}
      {transformer : Transformer B}
      Invariant
      FormatSpec
      (b : B)
      (ce : CacheEncode)
  := {a : option A |
            forall a' : A,
              a = Some a' <->
              (exists b1 b2 (ce' : CacheEncode),
                  computes_to (FormatSpec a' ce) (b1, ce')
                  /\ b = transform b1 b2
                  /\ Invariant a')}%comp.

Lemma refine_Pick_Decoder_For
      {A B} {cache : Cache}
      {transformer : Transformer B} {Invariant}
      {FormatSpec}
      (decoderImpl : @CorrectDecoderFor A B cache transformer Invariant FormatSpec)
  : forall b ce cd,
    Equiv ce cd
    -> snd (projT1 decoderImpl) cd
    -> refine (Pick_Decoder_For Invariant FormatSpec b ce)
           (ret match fst (projT1 decoderImpl) b cd
                           with
                           | Some (a, _, _) => Some a
                           | None => None
                           end).
Proof.
  intros.
  pose proof (projT2 (decoderImpl)).
  cbv beta in H1.
  destruct_ex; intuition.
  destruct H1.
  intros v Comp_v; computes_to_inv; subst;
    apply PickComputes; intros.
  split; intros.
  - destruct (fst (projT1 decoderImpl) b cd) as [ [ [? ?] ?] | ] eqn: ?; try discriminate.
    injections.
    eapply H2 in Heqo; eauto.
    destruct Heqo as [? [? [? [? ?] ] ] ].
    intuition.
    subst.
    eexists _, _, _ ; split; eauto.
  - destruct_ex; intuition; subst.
    eapply H1 in H5; eauto.
    destruct_ex; intuition.
    rewrite H5; reflexivity.
Qed.
