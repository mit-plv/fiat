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
    (forall env env' xenv data bin ext
            (env_OK : decode_inv env'),
        Equiv env env' ->
        predicate data ->
        rest_predicate data ext ->
        encode data env ↝ (bin, xenv) ->
        exists xenv',
          decode (transform bin ext) env' = Some (data, ext, xenv')
          /\ Equiv xenv xenv' /\ decode_inv xenv') /\
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

  Definition BindOpt {A' A''}
             (a_opt : option A')
             (k : A' -> option A'') :=
    Ifopt a_opt as a Then k a Else None.

  Definition DecodeBindOpt2
             {C D E}
             (a : option (A * B * D))
             (k : A -> B -> D -> option (C * E * D))
    : option (C * E * D) :=
    BindOpt a (fun a => match a with (a, b, d) => k a b d end).

  Definition DecodeBindOpt
             {C}
             (a : option (A * B))
             (k : A -> B -> option (C * B))
    : option (C * B) :=
    BindOpt a (fun a => let (a, b) := a in k a b).

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

Definition DecodeOpt2_fmap
           {A A'}
           (f : A -> A')
           (a_opt : option A)
  : option A' := Ifopt a_opt as a Then Some (f a) Else None.

Definition DecodeOpt2_fmap_id {A}
  : forall (a_opt : option A),
    DecodeOpt2_fmap id a_opt = a_opt.
Proof.
  destruct a_opt as [ a' | ]; reflexivity.
Qed.

Definition DecodeOpt2_fmap_compose
           {A A' A''}
  : forall
    (f : A -> A')
    (f' : A' -> A'')
    (a_opt : option A),
    DecodeOpt2_fmap f' (DecodeOpt2_fmap f a_opt) =
    DecodeOpt2_fmap (compose f' f) a_opt.
Proof.
  destruct a_opt as [ a' | ]; reflexivity.
Qed.

Definition DecodeBindOpt2_fmap
           {A B B'} :
  forall (f : B -> B')
         (a_opt : option A)
         (k : A -> option B),
    DecodeOpt2_fmap f (BindOpt a_opt k) =
    BindOpt a_opt (fun a => DecodeOpt2_fmap f (k a)).
Proof.
  destruct a_opt as [ a' | ]; reflexivity.
Qed.

Definition BindOpt_map
           {A B B'} :
  forall (f : option B -> B')
         (a_opt : option A)
         (k : A -> option B),
    f (BindOpt a_opt k) =
    Ifopt a_opt as a Then f (k a) Else f None.
Proof.
  destruct a_opt as [ a' | ]; reflexivity.
Qed.

Lemma DecodeOpt2_fmap_if_bool
      {A A' }
  : forall
    (f : A -> A')
    (b : bool)
    (a_opt a_opt' : option A),
    DecodeOpt2_fmap f (if b then a_opt else a_opt') =
    if b then (DecodeOpt2_fmap f a_opt)
    else (DecodeOpt2_fmap f a_opt').
Proof.
  intros; find_if_inside; reflexivity.
Qed.

Lemma BindOpt_map_if_bool
      {A A' }
  : forall
    (f : option A -> A')
    (b : bool)
    (a_opt a_opt' : option A),
    f (if b then a_opt else a_opt') =
    if b then (f a_opt)
    else (f a_opt').
Proof.
  intros; find_if_inside; reflexivity.
Qed.

Lemma DecodeOpt2_fmap_if
      {A A' P P'}
  : forall
    (f : A -> A')
    (b : {P} + {P'})
    (a_opt a_opt' : option A),
    DecodeOpt2_fmap f (if b then a_opt else a_opt') =
    if b then (DecodeOpt2_fmap f a_opt)
    else (DecodeOpt2_fmap f a_opt').
Proof.
  intros; find_if_inside; reflexivity.
Qed.

Lemma BindOpt_map_if
      {A A' P P'}
  : forall
    (f : option A -> A')
    (b : {P} + {P'})
    (a_opt a_opt' : option A),
    f (if b then a_opt else a_opt') =
    if b then (f a_opt)
    else (f a_opt').
Proof.
  intros; find_if_inside; reflexivity.
Qed.

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

Notation "`( a , b , env ) <- c ; k" :=
  (DecodeBindOpt2 c%bencode (fun a b env => k%bencode)) : binencoders_scope.

Notation "`( a , b ) <- c ; k" :=
  (DecodeBindOpt c%bencode (fun a b => k%bencode)) : binencoders_scope.

Open Scope binencoders_scope.

Lemma optimize_If_bind2_bool {A A' B B' C}
  : forall (c : bool)
           (t e : option (A * B * C))
           (k : A -> B -> C -> option (A' * B' * C)),
    (`(a, b, env) <- (If c Then t Else e); k a b env) =
    If c Then `(a, b, env) <- t; k a b env Else (`(a, b, env) <- e; k a b env).
Proof.
  destruct c; simpl; intros; reflexivity.
Qed.

Lemma If_sumbool_Then_Else_DecodeBindOpt {A B B' ResultT ResultT'} {c : Cache} {P}
  : forall (a_eq_dec : forall a a' : A, {P a a'} + {~ P a a'})
           a a'
           (k : _ -> _ -> _ -> option (ResultT' * B' * CacheDecode))
           (t : P a a' ->  option (ResultT * B * CacheDecode))
           (e : ~ P a a' -> option (ResultT * B * CacheDecode)),
    (`(w, b', cd') <- match a_eq_dec a a' with
                      | left e => t e
                      | right n => e n
                      end;
       k w b' cd') =
    match a_eq_dec a a' with
    | left e => `(w, b', cd') <- t e; k w b' cd'
    | right n => `(w, b', cd') <- e n; k w b' cd'
    end.
Proof.
  intros; destruct (a_eq_dec a a'); simpl; intros; reflexivity.
Qed.

Lemma optimize_under_DecodeBindOpt2_both {A B C D E} {B' }
  : forall (a_opt : option (A * B * C))
           (a_opt' : option (A * B' * C))
           (g : B' -> B)
           (a_opt_eq_Some : forall a' b' c,
               a_opt' = Some (a', b', c) ->
               a_opt = Some (a', g b', c))
           (a_opt_eq_None : a_opt' = None -> a_opt = None)
           (k : _ -> _ -> _ -> option (D * E * C))
           (k' : _ -> _ -> _ -> _)
           (k_eq_Some :
              forall a' b' c,
                a_opt' = Some (a', b', c) ->
                k a' (g b') c = k' a' b' c),
    DecodeBindOpt2 a_opt k = DecodeBindOpt2 a_opt' k'.
Proof.
  destruct a_opt' as [ [ [? ?] ?] | ]; simpl; intros.
  erewrite a_opt_eq_Some; simpl; eauto.
  erewrite a_opt_eq_None; simpl; eauto.
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

  Lemma Decode_w_Measure_le_eq'':
    forall (b : B) (cd : CacheDecode)
           (A_decode_le : forall (b0 : B) (cd0 : CacheDecode) (a : A) (b' : B) (cd' : CacheDecode),
               A_decode b0 cd0 = Some (a, b', cd') -> le_B b' b0),
      Decode_w_Measure_le b cd A_decode_le = None ->
      A_decode b cd = None.
  Proof.
    clear; intros ? ? ?; unfold Decode_w_Measure_le in *.
    remember (A_decode_le b cd); clear Heql.
    destruct (A_decode b cd) as [ [ [? ?] ? ] | ]; eauto.
    intros; discriminate.
  Qed.

  Lemma Decode_w_Measure_lt_eq'':
    forall (b : B) (cd : CacheDecode)
           (A_decode_lt : forall (b0 : B) (cd0 : CacheDecode) (a : A) (b' : B) (cd' : CacheDecode),
               A_decode b0 cd0 = Some (a, b', cd') -> lt_B b' b0),
      Decode_w_Measure_lt b cd A_decode_lt = None ->
      A_decode b cd = None.
  Proof.
    clear; intros ? ? ?; unfold Decode_w_Measure_lt in *.
    remember (A_decode_lt b cd); clear Heql.
    destruct (A_decode b cd) as [ [ [? ?] ? ] | ]; eauto.
    discriminate.
  Qed.



End DecodeWMeasure.


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
  - destruct (H1 _ _ _ _ _ ext env_OK H0 H3 H4 H5).
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
