Require Export
        Coq.Lists.List
        Fiat.Common
        Fiat.Computation.Core
        Fiat.Computation.Notations
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.Monoid
        Fiat.Narcissus.Stores.Cache.

Set Implicit Arguments.

Section Specifications.

  Variable S : Type. (* Source Type. (in-memory data) *)
  Variable T : Type. (* Target Type. (usually ByteStrings) *)
  Context {store : Cache}. (* Store Type. *)

  (* Formats are a quaternary relation on an source value, initial store,
     target value, and final store. *)
  Definition FormatM : Type :=
    S -> CacheFormat -> Comp (T * CacheFormat).

  (* Decoders consume a target value and store and produce either
     - a source value, remaining target value, and updated store
     - or an error value, i.e. None. *)

  Definition DecodeM : Type :=
    T -> CacheDecode -> option (S * CacheDecode).

  (* Encoders take a source value and store and produce either a
     - target value and updated store
     - or an error value, i.e. None. *)

  Definition EncodeM : Type :=
    S -> CacheFormat -> option (T * CacheFormat).

  Local Notation "a ∋ b" := (@computes_to _ a b) (at level 90).
  Local Notation "a ∌ b" := (~ @computes_to _ a b) (at level 90).

  Definition CorrectDecoder {V}
             (monoid : Monoid T)
             (Source_Predicate : S -> Prop)
             (View_Predicate : V -> Prop)
             (view : S -> V -> Prop)
             (format : FormatM)
             (decode : T -> CacheDecode -> option (V * T * CacheDecode))
             (decode_inv : CacheDecode -> Prop)
             (view_format : V -> CacheFormat -> Comp (T * CacheFormat)) :=
    (forall env env' xenv s t ext
            (env_OK : decode_inv env'),
        Equiv env env' ->
        Source_Predicate s ->
        format s env ∋ (t, xenv) ->
        exists v xenv',
          decode (mappend t ext) env' = Some (v, ext, xenv')
          /\ view s v
          /\ (view_format v env ∋ (t, xenv))
          /\ Equiv xenv xenv' /\ decode_inv xenv') /\
    (forall (env : CacheFormat) (env' xenv' : CacheDecode) (v : V) (t t' : T),
        Equiv env env' ->
        decode_inv env' ->
        decode t env' = Some (v, t', xenv') ->
        decode_inv xenv' /\
        exists (t'' : T) (xenv : CacheFormat),
          (view_format v env ∋ (t'', xenv))
          /\ t = mappend t'' t'
          /\ View_Predicate v
          /\ Equiv xenv xenv').

  Definition CorrectEncoder
             (format : FormatM)
             (encode : EncodeM)
    :=
      (forall (a : S) (env : CacheFormat) (b : T) (xenv : CacheFormat),
          encode a env = Some (b, xenv)
          -> format a env ∋ (b, xenv))
      /\ (forall (a : S) (env : CacheFormat),
             encode a env = None
             -> forall b xenv, ~ (format a env ∋ (b, xenv))).

    (* Definition that identifies properties of cache invariants for automation. *)
  Definition cache_inv_Property
             (P : CacheDecode -> Prop)
             (P_inv : (CacheDecode -> Prop) -> Prop) :=
    P_inv P.

  Lemma CorrectDecoderNone
        (monoid : Monoid T)
        {V}
    : forall (Source_Predicate : S -> Prop)
             (View_Predicate : V -> Prop)
             (format : FormatM)
             (decode : _)
             (view : S -> V -> Prop)
             (decode_inv : CacheDecode -> Prop)
             (view_format : V -> CacheFormat -> Comp (T * CacheFormat)),
      CorrectDecoder _ Source_Predicate View_Predicate view format decode decode_inv view_format
      -> forall b b' s_d,
        decode_inv s_d
        -> decode (mappend b b') s_d = None
        -> forall a s_e s_e',
            Equiv s_e s_d
            -> Source_Predicate a
            -> format a s_e ∌ (b, s_e').
  Proof.
    unfold not, CorrectDecoder; intros.
    split_and.
    eapply H5 in H4; eauto.
    destruct_ex; split_and.
    rewrite H6 in H1; discriminate.
  Qed.

  Definition CorrectDecoder_id
             (monoid : Monoid T)
             (Source_Predicate : S -> Prop)
             (format : FormatM)
             (decode : T -> CacheDecode -> option (S * T * CacheDecode))
             (decode_inv : CacheDecode -> Prop) :=
    (forall env env' xenv s t ext
            (env_OK : decode_inv env'),
        Equiv env env' ->
        Source_Predicate s ->
        format s env ∋ (t, xenv) ->
        exists xenv',
          decode (mappend t ext) env' = Some (s, ext, xenv')
          /\ Equiv xenv xenv' /\ decode_inv xenv') /\
    (forall env env' xenv' s t ext,
        Equiv env env'
        -> decode_inv env'
        -> decode t env' = Some (s, ext, xenv')
        -> decode_inv xenv'
           /\ exists t' xenv,
            (format s env ∋ (t', xenv))
            /\ t = mappend t' ext
            /\ Source_Predicate s
            /\ Equiv xenv xenv').

  (* The current definition of decoder correctness is equivalent to an
   e arlier one, when the projection is the identity function. *)
  Lemma CorrectDecoder_equiv_CorrectDecoder_id
    : forall (monoid : Monoid T)
             (Source_Predicate : S -> Prop)
             (format : FormatM)
             encode
             (correctEncode : CorrectEncoder format encode)
             (decode : T -> CacheDecode -> option (S * T * CacheDecode))
             (decode_inv : CacheDecode -> Prop),
      (CorrectDecoder_id monoid Source_Predicate format decode decode_inv <->
       CorrectDecoder monoid Source_Predicate Source_Predicate eq format decode decode_inv format).
  Proof.
    unfold CorrectDecoder_id, CorrectDecoder; intuition eauto.
    - generalize H3; intro;
        eapply H0 in H3; destruct_ex; split_and; eauto.
      rewrite H5; eexists _, _; intuition eauto.
    - eapply H0 in H3; destruct_ex; split_and; eauto.
      rewrite H3; eexists _; subst; intuition eauto.
  Qed.

  Corollary CorrectDecoderNone_dec_Source_Predicates
            (monoid : Monoid T)
            {V}
    : forall (Source_Predicate : S -> Prop)
             (View_Predicate : V -> Prop)
             (view : S -> V -> Prop)
             (Source_Predicate_dec : forall a, Source_Predicate a \/ ~ Source_Predicate a)
             (format : FormatM)
             (decode : _)
             (decode_inv : CacheDecode -> Prop)
             view_format,
      CorrectDecoder _ Source_Predicate View_Predicate view format decode decode_inv view_format
      -> forall b b' s_d,
        decode_inv s_d
        -> decode (mappend b b') s_d = None
        -> forall a ,
            (~ Source_Predicate a)
            \/ forall s_e s_e',
                Equiv s_e s_d
                -> format a s_e ∌ (b, s_e').
  Proof.
    intros.
    destruct (Source_Predicate_dec a); intuition.
    right; intros; eapply CorrectDecoderNone; eauto.
  Qed.

  Lemma decode_None :
    forall (monoid : Monoid T)
           (Source_Predicate : S -> Prop)
           (format : S -> CacheFormat -> Comp (T * CacheFormat))
           (decode : T -> CacheDecode -> option (S * T * CacheDecode))
           (decode_inv : CacheDecode -> Prop)
           (Source_Predicate_dec : forall a, {Source_Predicate a} + {~ Source_Predicate a}),
      CorrectDecoder monoid Source_Predicate Source_Predicate eq format decode decode_inv format
      -> forall b env' env,
        Equiv env env'
        -> decode b env' = None
        -> decode_inv env'
        -> forall s,
          ~ Source_Predicate s
          \/ ~ exists xenv, format s env ∋ (b, xenv).
  Proof.
    intros.
    destruct (Source_Predicate_dec s); try (solve [intuition]).
    right.
    intros [? ?].
    destruct ((proj1 H) env env' _ s _ mempty H2 H0 s0 H3); intuition;
      destruct_ex; intuition.
    rewrite mempty_right in H5; congruence.
  Qed.

  Local Transparent computes_to.

  (* We can always strengthen a format to disallow invalid s. *)
  Lemma CorrectDecoderStrengthenFormat :
    forall (monoid : Monoid T)
           {V}
           (Source_Predicate : S -> Prop)
           (View_Predicate : V -> Prop)
           (view : S -> V -> Prop)
           (format : S -> CacheFormat -> Comp (T * CacheFormat))
           (decode : T -> CacheDecode -> option (V * T * CacheDecode))
           (decode_inv : CacheDecode -> Prop)
           (Source_Predicate_dec : forall a, {Source_Predicate a} + {~ Source_Predicate a})
           view_format
    ,
      CorrectDecoder monoid Source_Predicate View_Predicate view format decode decode_inv view_format
      ->
      CorrectDecoder monoid Source_Predicate View_Predicate view  (fun a s b => (format a s ∋ b) /\ Source_Predicate a) decode decode_inv view_format.
  Proof.
    intros; destruct H as [? ? ]; unfold CorrectDecoder; split; intros.
    - eapply H; eauto.
      apply (proj1 H3).
    - eapply H0 in H3; intuition eauto.
  Qed.

  Local Opaque computes_to.

  Definition BindOpt {S' S''}
             (a_opt : option S')
             (k : S' -> option S'') :=
    Ifopt a_opt as a Then k a Else None.

  Lemma BindOpt_assoc {S''' S' S''} :
    forall (a_opt : option S''')
           (f : S''' -> option S')
           (g : S' -> option S''),
      BindOpt (BindOpt a_opt f) g =
      BindOpt a_opt (fun a => BindOpt (f a) g).
  Proof.
    destruct a_opt as [ ? | ]; simpl; intros; eauto.
  Qed.

  Definition DecodeBindOpt2
             {V D E}
             (a : option (S * T * D))
             (k : S -> T -> D -> option (V * E * D))
    : option (V * E * D) :=
    BindOpt a (fun a => match a with (a, b, d) => k a b d end).

  Definition DecodeBindOpt
             {V}
             (a : option (S * T))
             (k : S -> T -> option (V * T))
    : option (V * T) :=
    BindOpt a (fun a => let (a, b) := a in k a b).

  Lemma DecodeBindOpt2_inv
        {V D E}
        (a_opt : option (S * T * D))
        (a : V * E * D)
        (k : S -> T -> D -> option (V * E * D))
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
        {V}
        (a_opt : option (S * T))
        (a : V * T)
        (k : S -> T -> option (V * T))
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

Definition Cache_plus_inv (cache : Cache)
           (decode_inv : @CacheDecode cache -> Prop): Cache :=
  {| CacheFormat := @CacheFormat cache;
     CacheDecode := @CacheDecode cache;
     Equiv ce cd := Equiv ce cd /\ decode_inv cd|}.

Definition decode_strict
           {S T}
           {cache : Cache}
           {monoid : Monoid T}
           (decode : DecodeM S T)
  : DecodeM (S * T) T :=
  fun cd bs => Ifopt decode cd bs
    as abscd'
         Then Some (fst abscd', mempty, snd abscd')
         Else None.

Definition RestrictFormat
           {S T}
           {cache : Cache}
           (format : FormatM S T)
           (Source_Predicate : S -> Prop)
  : FormatM S T :=
  fun s env txenv => format s env txenv /\ Source_Predicate s.

(* DoneLax 'appends' a supplied bytestring onto the end of a format *)
Definition DoneLax {S T}
           {cache : Cache}
           {monoid : Monoid T}
           (format : FormatM S T)
  : FormatM (S * T) T :=
  fun s_rest env txenv =>
    exists t', fst txenv = mappend t' (snd s_rest) /\
                 format (fst s_rest) env (t', snd txenv).

Definition decode_obliviously
           {S T}
           {cache : Cache}
           {monoid : Monoid T}
           (decode : DecodeM (S * T) T)
  : T -> CacheDecode -> option (S * CacheDecode) :=
  fun bs cd => option_map (fun abc => (fst (fst abc), snd abc)) (decode bs cd).

(*Lemma CorrectDecoder_simpl_lax_equiv
      {S T}
      (cache : Cache)
      (monoid : Monoid T)
      (Source_Predicate : S -> Prop)
  : forall (decode_inv : CacheDecode -> Prop)
           (format : FormatM S T)
           (decode : DecodeM (S * T) T),
    CorrectDecoder (store := cache) monoid Source_Predicate (fun _ _ => True)  format
                   decode
                   decode_inv
    <-> CorrectDecoder_simpl
         (store := Cache_plus_inv cache decode_inv)
         (DoneLax (RestrictFormat format Source_Predicate))
         decode.
Proof.
  unfold CorrectDecoder, CorrectDecoder_simpl, DoneLax, RestrictFormat, decode_obliviously; split.
  - intuition.
    + rewrite unfold_computes in H2; simpl in *; destruct_ex; intuition.
      destruct (H0 env env' xenv a x b); simpl; intuition eauto.
      rewrite H, H7; simpl; eauto.
    + destruct (decode t env') as [ [ [? ?] ?] | ] eqn: ?; destruct_ex;
        simpl in *; try discriminate; intuition; injections; eauto.
      eapply H1 in Heqo; intuition eauto; destruct_ex; intuition.
      rewrite H2; eexists; rewrite unfold_computes; intuition eauto.
      rewrite unfold_computes in H5; simpl; eauto.
  - intros; split_and; split; intros.
    + destruct (H0 env env' xenv (s, ext) (mappend t ext)).
      simpl; intuition.
      apply unfold_computes; simpl.
      eexists; intuition eauto.
      split_and; eauto.
    + destruct (H1 env env' xenv' (s, ext) t); eauto.
      split_and. rewrite unfold_computes in H5; destruct_ex; split_and.
      subst; split; eauto.
      eexists _, _; intuition eauto.
      eauto using unfold_computes.
Qed. *)

Definition DecodeOpt2_fmap
           {S S'}
           (f : S -> S')
           (a_opt : option S)
  : option S' := Ifopt a_opt as a Then Some (f a) Else None.

Definition DecodeOpt2_fmap_id {S}
  : forall (a_opt : option S),
    DecodeOpt2_fmap id a_opt = a_opt.
Proof.
  destruct a_opt as [ a' | ]; reflexivity.
Qed.

Definition DecodeOpt2_fmap_compose
           {S S' S''}
  : forall
    (f : S -> S')
    (f' : S' -> S'')
    (a_opt : option S),
    DecodeOpt2_fmap f' (DecodeOpt2_fmap f a_opt) =
    DecodeOpt2_fmap (compose f' f) a_opt.
Proof.
  destruct a_opt as [ a' | ]; reflexivity.
Qed.

Definition DecodeBindOpt2_fmap
           {S T T'} :
  forall (f : T -> T')
         (a_opt : option S)
         (k : S -> option T),
    DecodeOpt2_fmap f (BindOpt a_opt k) =
    BindOpt a_opt (fun a => DecodeOpt2_fmap f (k a)).
Proof.
  destruct a_opt as [ a' | ]; reflexivity.
Qed.

Definition BindOpt_map
           {S T T'} :
  forall (f : option T -> T')
         (a_opt : option S)
         (k : S -> option T),
    f (BindOpt a_opt k) =
    Ifopt a_opt as a Then f (k a) Else f None.
Proof.
  destruct a_opt as [ a' | ]; reflexivity.
Qed.

Lemma If_Opt_Then_Else_BindOpt {S T V}
  : forall (a_opt : option S)
           (t : S -> option T)
           (e : option T)
           (k : _ -> option V),
    BindOpt (Ifopt a_opt as a Then t a Else e) k
    = Ifopt a_opt as a Then (BindOpt (t a) k) Else (BindOpt e k).
Proof.
  destruct a_opt; simpl; intros; reflexivity.
Qed.

Lemma DecodeOpt2_fmap_if_bool
      {S S' }
  : forall
    (f : S -> S')
    (b : bool)
    (a_opt a_opt' : option S),
    DecodeOpt2_fmap f (if b then a_opt else a_opt') =
    if b then (DecodeOpt2_fmap f a_opt)
    else (DecodeOpt2_fmap f a_opt').
Proof.
  intros; find_if_inside; reflexivity.
Qed.

Lemma BindOpt_map_if_bool
      {S S' }
  : forall
    (f : option S -> S')
    (b : bool)
    (a_opt a_opt' : option S),
    f (if b then a_opt else a_opt') =
    if b then (f a_opt)
    else (f a_opt').
Proof.
  intros; find_if_inside; reflexivity.
Qed.

Lemma DecodeOpt2_fmap_if
      {S S' P P'}
  : forall
    (f : S -> S')
    (b : {P} + {P'})
    (a_opt a_opt' : option S),
    DecodeOpt2_fmap f (if b then a_opt else a_opt') =
    if b then (DecodeOpt2_fmap f a_opt)
    else (DecodeOpt2_fmap f a_opt').
Proof.
  intros; find_if_inside; reflexivity.
Qed.

Lemma BindOpt_map_if
      {S S' P P'}
  : forall
    (f : option S -> S')
    (b : {P} + {P'})
    (a_opt a_opt' : option S),
    f (if b then a_opt else a_opt') =
    if b then (f a_opt)
    else (f a_opt').
Proof.
  intros; find_if_inside; reflexivity.
Qed.

Lemma DecodeBindOpt2_assoc {S T V D E F G} :
  forall (a_opt : option (S * T * D))
         (f : S -> T -> D -> option (V * E * D))
         (g : V -> E -> D -> option (F * G * D)),
    DecodeBindOpt2 (DecodeBindOpt2 a_opt f) g =
    DecodeBindOpt2 a_opt (fun a b c => DecodeBindOpt2 (f a b c) g).
Proof.
  destruct a_opt as [ [ [? ?] ?] | ]; simpl; intros; eauto.
Qed.

Lemma DecodeBindOpt2_under_bind {S T V D E} :
  forall (a_opt : option (S * T * D))
         (f f' : S -> T -> D -> option (V * E * D)),
    (forall a b d, f a b d = f' a b d)
    -> DecodeBindOpt2 a_opt f = DecodeBindOpt2 a_opt f'.
Proof.
  destruct a_opt as [ [ [? ?] ?] | ]; simpl; intros; eauto.
Qed.

Notation "`( a , b , env ) <- c ; k" :=
  (DecodeBindOpt2 c%format (fun a b env => k%format)) : format_scope.

Notation "`( a , b ) <- c ; k" :=
  (DecodeBindOpt c%format (fun a b => k%format)) : format_scope.

Open Scope format_scope.

Lemma optimize_If_td2_bool {S S' T T' V}
  : forall (c : bool)
           (t e : option (S * T * V))
           (k : S -> T -> V -> option (S' * T' * V)),
    (`(a, b, env) <- (If c Then t Else e); k a b env) =
    If c Then `(a, b, env) <- t; k a b env Else (`(a, b, env) <- e; k a b env).
Proof.
  destruct c; simpl; intros; reflexivity.
Qed.

Lemma If_sumbool_Then_Else_DecodeBindOpt {S T T' ResultT ResultT'} {c : Cache} {P}
  : forall (a_eq_dec : forall a a' : S, {P a a'} + {~ P a a'})
           a a'
           (k : _ -> _ -> _ -> option (ResultT' * T' * CacheDecode))
           (t : P a a' ->  option (ResultT * T * CacheDecode))
           (e : ~ P a a' -> option (ResultT * T * CacheDecode)),
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

Lemma optimize_under_DecodeBindOpt2_both {S T V D E} {T' }
  : forall (a_opt : option (S * T * V))
           (a_opt' : option (S * T' * V))
           (g : T' -> T)
           (a_opt_eq_Some : forall a' b' c,
               a_opt' = Some (a', b', c) ->
               a_opt = Some (a', g b', c))
           (a_opt_eq_None : a_opt' = None -> a_opt = None)
           (k : _ -> _ -> _ -> option (D * E * V))
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

Definition EquivFormat {S T} {cache : Cache}
           (format1 format2 : FormatM S T) :=
  forall s env, refineEquiv (format1 s env) (format2 s env).

Lemma EquivFormat_sym {S T} {cache : Cache} :
  forall (FormatSpec FormatSpec'  : FormatM S T),
    EquivFormat FormatSpec FormatSpec'
    -> EquivFormat FormatSpec' FormatSpec.
Proof.
  unfold EquivFormat, refineEquiv; intuition eauto;
    eapply H.
Qed.

Lemma EquivFormat_reflexive
      {S T : Type} {cache : Cache}
  : forall (format : FormatM S T),
    EquivFormat format format.
Proof.
  unfold EquivFormat; intros.
  reflexivity.
Qed.

Add Parametric Morphism
    S T V
    (cache : Cache)
    (monoid : Monoid T)
    (decode_inv : CacheDecode -> Prop)
  : (fun Source_Predicate View_Predicate view format decode =>
       @CorrectDecoder S T cache V monoid Source_Predicate View_Predicate
                                view format decode decode_inv)
    with signature (pointwise_relation _ iff
                                       --> pointwise_relation _ (flip impl)
                                       --> pointwise_relation _ (pointwise_relation _ iff)
                                       --> EquivFormat
                                       --> pointwise_relation _ (pointwise_relation _ eq)
                                       --> EquivFormat
                                       --> impl)
      as format_decode_correct_alt.
Proof.
  unfold EquivFormat, impl, pointwise_relation, CorrectDecoder; intros.
  intuition eauto; intros.
  - setoid_rewrite H3.
    setoid_rewrite H1.
    eapply H2 in H9.
    eapply H6 in H9.
    destruct_ex; split_and;
      eexists _, _; intuition eauto.
    eapply H4; eauto.
    eauto.
    eauto.
    eapply H; eauto.
  - eapply H7; eauto.
    rewrite <- H3; eauto.
  - rewrite H3 in H9.
    eapply H7 in H8; eauto.
    split_and; destruct_ex; split_and; subst.
    eexists _, _; intuition eauto.
    eapply H4; eauto.
Qed.

Add Parametric Morphism
    S T V
    (cache : Cache)
    (monoid : Monoid T)
    (decode_inv : CacheDecode -> Prop)
    View_Predicate
    view
    format
    decode
    view_format
  : (fun Source_Predicate  =>
       @CorrectDecoder S T cache V monoid Source_Predicate View_Predicate
                       view format decode decode_inv view_format)
    with signature (pointwise_relation _ impl
                                       --> impl)
      as weaken_source_pred.
Proof.
  unfold EquivFormat, impl, pointwise_relation, CorrectDecoder; intros.
  intuition eauto; intros.
Qed.

Add Parametric Morphism
    S T V
    (cache : Cache)
    (monoid : Monoid T)
    (Source_Predicate : S -> Prop)
    (View_Predicate : V -> Prop)
    view
    (decode : T -> CacheDecode -> option (V * T * CacheDecode))
    (decode_inv : CacheDecode -> Prop)
    view_format
  : (fun format =>
       @CorrectDecoder S T cache V monoid Source_Predicate View_Predicate
                                view format decode decode_inv view_format)
    with signature (EquivFormat --> impl)
      as format_decode_correct_refineEquiv.
Proof.
  unfold EquivFormat, impl, pointwise_relation; intros.
  eapply format_decode_correct_alt_Proper; eauto; try reflexivity.
  unfold flip, EquivFormat; intros; reflexivity.
Qed.

Add Parametric Morphism
    S T V
    (cache : Cache)
    (monoid : Monoid T)
    (View_Predicate : V -> Prop)
    format
    view
    (decode : T -> CacheDecode -> option (V * T * CacheDecode))
    (decode_inv : CacheDecode -> Prop)
    view_format
  : (fun Source_Predicate =>
       @CorrectDecoder S T cache V monoid Source_Predicate View_Predicate
                                view format decode decode_inv view_format)
    with signature (pointwise_relation _ iff --> impl)
      as format_decode_correct_EquivPred.
Proof.
  unfold EquivFormat, impl, pointwise_relation; intros.
  eapply format_decode_correct_alt_Proper; eauto; try reflexivity.
  unfold flip, EquivFormat; intros; reflexivity.
  unfold flip, EquivFormat; intros; reflexivity.
Qed.

Add Parametric Morphism
    S T
    (cache : Cache)
    (monoid : Monoid T)
    (Source_Predicate : S -> Prop)
    (View_Predicate : S -> Prop)
    view
    (decode : T -> CacheDecode -> option (S * T * CacheDecode))
    (decode_inv : CacheDecode -> Prop)
  : (fun format =>
       @CorrectDecoder S T cache S monoid Source_Predicate View_Predicate
                                view format decode decode_inv format)
    with signature (EquivFormat --> impl)
      as format_decode_correct_EquivFormatAndView.
Proof.
  unfold EquivFormat, impl, pointwise_relation; intros.
  eapply format_decode_correct_alt_Proper; eauto; try reflexivity.
Qed.

Add Parametric Morphism
    S T V
    (cache : Cache)
    (monoid : Monoid T)
    (Source_Predicate : S -> Prop)
    (View_Predicate : V -> Prop)
    format
    view
    (decode_inv : CacheDecode -> Prop)
    view_format
  : (fun decode =>
       @CorrectDecoder S T cache V monoid Source_Predicate View_Predicate
                                view format decode decode_inv view_format)
    with signature (pointwise_relation _ (pointwise_relation _ eq)
                                       --> impl)
      as format_decode_correct_EquivDecoder.
Proof.
  unfold impl, pointwise_relation; intros.
  eapply format_decode_correct_alt_Proper; eauto; try reflexivity;
    unfold flip, EquivFormat; reflexivity.
Qed.

Section DecodeWMeasure.
  Context {S : Type}. (* s type *)
  Context {T : Type}. (* t type *)
  Context {cache : Cache}.
  Context {monoid : Monoid T}.

  Variable format_S : S -> CacheFormat -> Comp (T * CacheFormat).
  Variable S_decode : T -> CacheDecode -> option (S * T * CacheDecode).

  Definition Decode_w_Measure_lt
             (b : T)
             (cd : CacheDecode)
             (S_decode_lt
              : forall  (b : T)
                        (cd : CacheDecode)
                        (a : S)
                        (b' : T)
                        (cd' : CacheDecode),
                 S_decode b cd = Some (a, b', cd')
                 -> lt_B b' b)
    : option (S * {b' : T | lt_B b' b} * CacheDecode).
    generalize (S_decode_lt b cd); clear.
    destruct (S_decode b cd) as [ [ [ a b' ] cd' ] | ]; intros;
      [ refine (Some (a, exist _ b' (H _ _ _ eq_refl), cd'))
      | exact None ].
  Defined.

  Lemma Decode_w_Measure_lt_eq
        (b : T)
        (cd : CacheDecode)
        (S_decode_lt
         : forall  (b : T)
                   (cd : CacheDecode)
                   (a : S)
                   (b' : T)
                   (cd' : CacheDecode),
            S_decode b cd = Some (a, b', cd')
            -> lt_B b' b)
    : forall a' b' cd',
      S_decode b cd = Some (a', b', cd')
      -> exists pf,
        Decode_w_Measure_lt b cd S_decode_lt =
        Some (a', exist _ b' pf , cd').
  Proof.
    clear; intros; unfold Decode_w_Measure_lt.
    remember (S_decode_lt b cd); clear Heql.
    destruct (S_decode b cd) as [ [ [? ?] ? ] | ].
    injections; eauto.
    discriminate.
  Qed.

  Lemma Decode_w_Measure_lt_eq'
        (b : T)
        (cd : CacheDecode)
        (S_decode_lt
         : forall  (b : T)
                   (cd : CacheDecode)
                   (a : S)
                   (b' : T)
                   (cd' : CacheDecode),
            S_decode b cd = Some (a, b', cd')
            -> lt_B b' b)
    : S_decode b cd = None
      -> Decode_w_Measure_lt b cd S_decode_lt = None.
  Proof.
    clear; intros; unfold Decode_w_Measure_lt.
    remember (S_decode_lt b cd); clear Heql.
    destruct (S_decode b cd) as [ [ [? ?] ? ] | ]; eauto.
    discriminate.
  Qed.

  Definition Decode_w_Measure_le
             (b : T)
             (cd : CacheDecode)
             (S_decode_le
              : forall  (b : T)
                        (cd : CacheDecode)
                        (a : S)
                        (b' : T)
                        (cd' : CacheDecode),
                 S_decode b cd = Some (a, b', cd')
                 -> le_B b' b)
    : option (S * {b' : T | le_B b' b} * CacheDecode).
    generalize (S_decode_le b cd); clear.
    destruct (S_decode b cd) as [ [ [ a b' ] cd' ] | ]; intros;
      [ refine (Some (a, exist _ b' (H _ _ _ eq_refl), cd'))
      | exact None ].
  Defined.

  Lemma Decode_w_Measure_le_eq
        (b : T)
        (cd : CacheDecode)
        (S_decode_le
         : forall  (b : T)
                   (cd : CacheDecode)
                   (a : S)
                   (b' : T)
                   (cd' : CacheDecode),
            S_decode b cd = Some (a, b', cd')
            -> le_B b' b)
    : forall a' b' cd',
      S_decode b cd = Some (a', b', cd')
      -> exists pf,
        Decode_w_Measure_le b cd S_decode_le =
        Some (a', exist _ b' pf , cd').
  Proof.
    clear; intros; unfold Decode_w_Measure_le.
    remember (S_decode_le b cd); clear Heql.
    destruct (S_decode b cd) as [ [ [? ?] ? ] | ].
    injections; eauto.
    discriminate.
  Qed.

  Lemma Decode_w_Measure_le_eq'
        (b : T)
        (cd : CacheDecode)
        (S_decode_le
         : forall  (b : T)
                   (cd : CacheDecode)
                   (a : S)
                   (b' : T)
                   (cd' : CacheDecode),
            S_decode b cd = Some (a, b', cd')
            -> le_B b' b)
    : S_decode b cd = None
      -> Decode_w_Measure_le b cd S_decode_le = None.
  Proof.
    clear; intros; unfold Decode_w_Measure_le.
    remember (S_decode_le b cd); clear Heql.
    destruct (S_decode b cd) as [ [ [? ?] ? ] | ]; eauto.
    discriminate.
  Qed.

  Lemma Decode_w_Measure_le_eq'':
    forall (b : T) (cd : CacheDecode)
           (S_decode_le : forall (b0 : T) (cd0 : CacheDecode) (a : S) (b' : T) (cd' : CacheDecode),
               S_decode b0 cd0 = Some (a, b', cd') -> le_B b' b0),
      Decode_w_Measure_le b cd S_decode_le = None ->
      S_decode b cd = None.
  Proof.
    clear; intros ? ? ?; unfold Decode_w_Measure_le in *.
    remember (S_decode_le b cd); clear Heql.
    destruct (S_decode b cd) as [ [ [? ?] ? ] | ]; eauto.
    intros; discriminate.
  Qed.

  Lemma Decode_w_Measure_lt_eq'':
    forall (b : T) (cd : CacheDecode)
           (S_decode_lt : forall (b0 : T) (cd0 : CacheDecode) (a : S) (b' : T) (cd' : CacheDecode),
               S_decode b0 cd0 = Some (a, b', cd') -> lt_B b' b0),
      Decode_w_Measure_lt b cd S_decode_lt = None ->
      S_decode b cd = None.
  Proof.
    clear; intros ? ? ?; unfold Decode_w_Measure_lt in *.
    remember (S_decode_lt b cd); clear Heql.
    destruct (S_decode b cd) as [ [ [? ?] ? ] | ]; eauto.
    discriminate.
  Qed.

End DecodeWMeasure.

Global Unset Implicit Arguments.

Definition CorrectDecoderFor {S T} {cache : Cache}
           {monoid : Monoid T} Invariant FormatSpec :=
  { decodePlusCacheInv : _ |
    exists P_inv,
    (cache_inv_Property (snd decodePlusCacheInv) P_inv
     -> CorrectDecoder (S := S) monoid Invariant Invariant eq
                                FormatSpec
                                (fst decodePlusCacheInv)
                                (snd decodePlusCacheInv) FormatSpec)
    /\ cache_inv_Property (snd decodePlusCacheInv) P_inv}.

Definition CorrectEncoderFor {S T} {cache : Cache}
      {monoid : Monoid T} FormatSpec :=
  { encoder' : EncodeM S T & forall a env,
        (forall benv', encoder' a env = Some benv' ->
                       refine (FormatSpec a env) (ret benv'))
        /\ (encoder' a env = None ->
            forall benv', ~ computes_to (FormatSpec a env) benv')}.

(* Here are the expected correctness lemmas for synthesized functions. *)
Lemma CorrectDecodeEncode
      {S T} {cache : Cache}
      {monoid : Monoid T}
  : forall Invariant
           (FormatSpec : FormatM S T)
           (encoder : CorrectEncoderFor FormatSpec)
           (decoder : CorrectDecoderFor Invariant FormatSpec),
    forall a envE envD b envE',
      Equiv envE envD
      -> Invariant a
      -> snd (proj1_sig decoder) envD
      -> projT1 encoder a envE = Some (b, envE')
      -> exists envD',
          fst (proj1_sig decoder) b envD = Some (a, mempty, envD').
Proof.
  intros.
  destruct encoder as [encoder encoder_OK].
  destruct decoder as [decoder [Inv [decoder_OK Inv_cd] ] ]; simpl in *.
  specialize (proj1 (encoder_OK a envE) _ H2); intro.
  specialize (decoder_OK Inv_cd).
  destruct decoder_OK as [decoder_OK _].
  unfold cache_inv_Property in Inv_cd.
  eapply decoder_OK  with (ext := mempty) in H3; eauto.
  destruct_ex; intuition.
  subst; rewrite mempty_right in H4; eauto.
Qed.

Lemma CorrectEncodeDecode
      {S T}
      {cache : Cache}
      {monoid : Monoid T}
  : forall Invariant
           (FormatSpec : FormatM S T)
           (decoder : CorrectDecoderFor Invariant FormatSpec),
    forall bs ce cd cd' s ext,
      Equiv ce cd
      -> snd (proj1_sig decoder) cd
      -> fst (proj1_sig decoder) bs cd = Some (s, ext, cd')
      -> Invariant s /\
         exists ce' bs',
           bs = mappend bs' ext
           /\ Equiv ce' cd' /\ FormatSpec s ce (bs', ce').
Proof.
  intros.
  destruct decoder as [decoder [Inv [decoder_OK Inv_cd] ] ]; simpl in *.
  specialize (decoder_OK Inv_cd).
  destruct decoder_OK as [_ decoder_OK].
  eapply decoder_OK in H1; eauto.
  intuition; destruct_ex; intuition eauto.
Qed.

Lemma Start_CorrectDecoderFor
      {S T} {cache : Cache}
      {monoid : Monoid T}
      Invariant
      FormatSpec
      (decoder decoder_opt : T -> CacheDecode -> option (S * T * CacheDecode))
      (cache_inv : CacheDecode -> Prop)
      (P_inv : (CacheDecode -> Prop) -> Prop)
      (decoder_OK :
         cache_inv_Property cache_inv P_inv
         -> CorrectDecoder monoid Invariant Invariant
                           eq FormatSpec decoder cache_inv FormatSpec)
      (cache_inv_OK : cache_inv_Property cache_inv P_inv)
      (decoder_opt_OK : forall b cd, decoder b cd = decoder_opt b cd)
  : @CorrectDecoderFor S T cache monoid Invariant FormatSpec.
Proof.
  exists (decoder_opt, cache_inv); exists P_inv; split; simpl; eauto.
  unfold CorrectDecoder in *; intuition; intros.
  - destruct (H1 _ _ _ _ _ ext env_OK H0 H3 H4).
    rewrite decoder_opt_OK in H5; eauto.
  - rewrite <- decoder_opt_OK in H4; destruct (H2 _ _ _ _ _ _ H0 H3 H4); eauto.
  - rewrite <- decoder_opt_OK in H4; destruct (H2 _ _ _ _ _ _ H0 H3 H4); eauto.
Defined.

(* Shorthand for nondeterministically decoding a value. *)
Definition Pick_Decoder_For
           {S T} {cache : Cache}
           {monoid : Monoid T}
           Invariant
           FormatSpec
           (b : T)
           (ce : CacheFormat)
  := {a : option S |
      forall a' : S,
        a = Some a' <->
        (exists b1 b2 (ce' : CacheFormat),
            computes_to (FormatSpec a' ce) (b1, ce')
            /\ b = mappend b1 b2
            /\ Invariant a')}%comp.

Lemma refine_Pick_Decoder_For
      {S T} {cache : Cache}
      {monoid : Monoid T}
      {Invariant}
      {FormatSpec}
      (decoderImpl : @CorrectDecoderFor S T cache monoid Invariant FormatSpec)
  : forall b ce cd,
    Equiv ce cd
    -> snd (proj1_sig decoderImpl) cd
    -> refine (Pick_Decoder_For Invariant FormatSpec b ce)
              (ret match fst (proj1_sig decoderImpl) b cd
                   with
                   | Some (a, _, _) => Some a
                   | None => None
                   end).
Proof.
  intros.
  pose proof (proj2_sig (decoderImpl)).
  cbv beta in H1.
  destruct_ex; intuition.
  destruct H1 as [? ?].
  intros v Comp_v; computes_to_inv; subst;
    apply PickComputes; intros.
  split; intros.
  - destruct (fst (proj1_sig decoderImpl) b cd) as [ [ [? ?] ?] | ] eqn: ?; try discriminate.
    injections.
    eapply H2 in Heqo; eauto.
    destruct Heqo as [? [? [? [? ?] ] ] ].
    intuition.
    subst.
    eexists _, _, _ ; split; eauto.
  - destruct_ex; intuition; subst.
    eapply H1 in H5; eauto.
    destruct_ex; intuition.
    rewrite H5; simpl; congruence.
Qed.

Notation "a ∋ b" := (@computes_to _ a b) (at level 65) : format_scope.
Notation "a ∌ b" := (~ @computes_to _ a b) (at level 65) : format_scope.

(* Nicer notation for formating constants *)
Notation "'constant' n" := (fun _ => n) (at level 20) : format_scope.
