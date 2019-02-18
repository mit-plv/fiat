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

  Variable A : Type. (* Source Type. (in-memory data) *)
  Variable B : Type. (* Target Type. (usually ByteStrings) *)
  Context {store : Cache}. (* Store Type. *)

  (* Formats are a quaternary relation on an source value, initial store,
     target value, and final store. *)
  Definition FormatM : Type :=
    A -> CacheFormat -> Comp (B * CacheFormat).

  (* Decoders consume a target value and store and produce either
     - a source value, remaining target value, and updated store
     - or an error value, i.e. None. *)

  Definition DecodeM : Type :=
    B -> CacheDecode -> option (A * CacheDecode).

  (* Encoders take a source value and store and produce either a
     - target value and updated store
     - or an error value, i.e. None. *)

  Definition EncodeM : Type :=
    A -> CacheFormat -> option (B * CacheFormat).

  Local Notation "a ∋ b" := (@computes_to _ a b) (at level 90).
  Local Notation "a ∌ b" := (~ @computes_to _ a b) (at level 90).

  Definition format_decode_correct
             (monoid : Monoid B)
             (predicate : A -> Prop)
             (format : A -> CacheFormat -> B * CacheFormat)
             (decode : B -> CacheDecode -> A * B * CacheDecode) :=
    forall env env' xenv xenv' data data' bin ext ext',
      Equiv env env' ->
      predicate data ->
      format data env = (bin, xenv) ->
      decode (mappend bin ext) env' = (data', ext', xenv') ->
      Equiv xenv xenv' /\ data = data' /\ ext = ext'.

  Definition CorrectDecoder {C}
             (monoid : Monoid B)
             (predicate : A -> Prop)
             (proj : A -> C)
             (format : FormatM)
             (decode : B -> CacheDecode -> option (C * B * CacheDecode))
             (decode_inv : CacheDecode -> Prop) :=
    (forall env env' xenv data bin ext
            (env_OK : decode_inv env'),
        Equiv env env' ->
        predicate data ->
        format data env ∋ (bin, xenv) ->
        exists xenv',
          decode (mappend bin ext) env' = Some (proj data, ext, xenv')
          /\ Equiv xenv xenv' /\ decode_inv xenv') /\
    (forall (env : CacheFormat) (env' xenv' : CacheDecode) (c : C) (bin ext : B),
        Equiv env env' ->
        decode_inv env' ->
        decode bin env' = Some (c, ext, xenv') ->
        decode_inv xenv' /\
        (exists (data : A) (bin' : B) (xenv : CacheFormat),
            computes_to (format data env) (bin', xenv)
               /\ bin = mappend bin' ext
               /\ predicate data
               /\ Equiv xenv xenv'
               /\ proj data = c)).

  Definition CorrectEncoder
             (format : FormatM)
             (encode : EncodeM)
    :=
      (forall (a : A) (env : CacheFormat) (b : B) (xenv : CacheFormat),
          encode a env = Some (b, xenv)
          -> format a env ∋ (b, xenv))
      /\ (forall (a : A) (env : CacheFormat),
             encode a env = None
             -> forall b xenv, ~ (format a env ∋ (b, xenv))).

    (* Definition that identifies properties of cache invariants for automation. *)
  Definition cache_inv_Property
             (P : CacheDecode -> Prop)
             (P_inv : (CacheDecode -> Prop) -> Prop) :=
    P_inv P.

  Lemma CorrectDecoderNone
        (monoid : Monoid B)
        {C}
    : forall (predicate : A -> Prop)
             (proj : A -> C)
             (format : FormatM)
             (decode : _)
             (decode_inv : CacheDecode -> Prop),
      CorrectDecoder _ predicate proj format decode decode_inv
      -> forall b b' s_d,
        decode_inv s_d
        -> decode (mappend b b') s_d = None
        -> forall a s_e s_e',
            Equiv s_e s_d
            -> predicate a
            -> format a s_e ∌ (b, s_e').
  Proof.
    unfold not, CorrectDecoder; intros.
    split_and.
    eapply H5 in H4; eauto.
    destruct_ex; split_and.
    rewrite H6 in H1; discriminate.
  Qed.

  Definition CorrectDecoder_id
             (monoid : Monoid B)
             (predicate : A -> Prop)
             (format : FormatM)
             (decode : B -> CacheDecode -> option (A * B * CacheDecode))
             (decode_inv : CacheDecode -> Prop) :=
    (forall env env' xenv data bin ext
            (env_OK : decode_inv env'),
        Equiv env env' ->
        predicate data ->
        format data env ∋ (bin, xenv) ->
        exists xenv',
          decode (mappend bin ext) env' = Some (data, ext, xenv')
          /\ Equiv xenv xenv' /\ decode_inv xenv') /\
    (forall env env' xenv' data bin ext,
        Equiv env env'
        -> decode_inv env'
        -> decode bin env' = Some (data, ext, xenv')
        -> decode_inv xenv'
           /\ exists bin' xenv,
            (format data env ∋ (bin', xenv))
            /\ bin = mappend bin' ext
            /\ predicate data
            /\ Equiv xenv xenv').

  (* The current definition of decoder correctness is equivalent to an
   e arlier one, when the projection is the identity function. *)
  Lemma CorrectDecoder_equiv_CorrectDecoder_id
    : forall (monoid : Monoid B)
             (predicate : A -> Prop)
             (format : FormatM)
             encode
             (correctEncode : CorrectEncoder format encode)
             (decode : B -> CacheDecode -> option (A * B * CacheDecode))
             (decode_inv : CacheDecode -> Prop),
      (CorrectDecoder_id monoid predicate format decode decode_inv <->
      CorrectDecoder monoid predicate id format decode decode_inv).
  Proof.
    unfold CorrectDecoder_id, CorrectDecoder; intuition eauto.
    - eapply H1; eauto.
    - eapply H1 in H3; intuition eauto.
      destruct_ex; intuition.
      eexists _, _, _; intuition eauto.
    - eapply H1; eauto.
    - eapply H1 in H3; intuition eauto.
      destruct_ex; intuition.
      unfold id in *; subst; eexists _, _; intuition eauto.
  Qed.

  Corollary CorrectDecoderNone_dec_predicates
            (monoid : Monoid B)
            {C}
    : forall (predicate : A -> Prop)
             (proj : A -> C)
             (predicate_dec : forall a, predicate a \/ ~ predicate a)
             (format : FormatM)
             (decode : _)
             (decode_inv : CacheDecode -> Prop),
      CorrectDecoder _ predicate proj format decode decode_inv
      -> forall b b' s_d,
        decode_inv s_d
        -> decode (mappend b b') s_d = None
        -> forall a ,
            (~ predicate a)
            \/ forall s_e s_e',
                Equiv s_e s_d
                -> format a s_e ∌ (b, s_e').
  Proof.
    intros.
    destruct (predicate_dec a); intuition.
    right; intros; eapply CorrectDecoderNone; eauto.
  Qed.

  Lemma decode_None :
    forall (monoid : Monoid B)
           {C}
           (predicate : A -> Prop)
           (proj : A -> C)
           (format : A -> CacheFormat -> Comp (B * CacheFormat))
           (decode : B -> CacheDecode -> option (C * B * CacheDecode))
           (decode_inv : CacheDecode -> Prop)
           (predicate_dec : forall a, {predicate a} + {~ predicate a}),
      CorrectDecoder monoid predicate proj format decode decode_inv
      -> forall b env' env,
        Equiv env env'
        -> decode b env' = None
        -> decode_inv env'
        -> forall data,
          ~ predicate data
          \/ ~ exists xenv, format data env ∋ (b, xenv).
  Proof.
    intros.
    destruct (predicate_dec data); try (solve [intuition]).
    right.
    intros [? ?].
    destruct ((proj1 H) env env' _ data _ mempty H2 H0 p H3); intuition.
    rewrite mempty_right in H5; congruence.
  Qed.

  Local Transparent computes_to.

  (* We can always strengthen a format to disallow invalid data. *)
  Lemma CorrectDecoderStrengthenFormat :
    forall (monoid : Monoid B)
           {C}
           (predicate : A -> Prop)
           (proj : A -> C)
           (format : A -> CacheFormat -> Comp (B * CacheFormat))
           (decode : B -> CacheDecode -> option (C * B * CacheDecode))
           (decode_inv : CacheDecode -> Prop)
           (predicate_dec : forall a, {predicate a} + {~ predicate a}),
      CorrectDecoder monoid predicate proj format decode decode_inv
      ->
      CorrectDecoder monoid predicate proj  (fun a s b => (format a s ∋ b) /\ predicate a) decode decode_inv.
  Proof.
    intros; destruct H; unfold CorrectDecoder; split; intros.
    eapply H; eauto.
    apply (proj1 H3).
    destruct (H0 env env' xenv' c bin ext) as [? [? [? [? ?] ] ] ]; intuition eauto.
    eexists _, _, _; intuition eauto.
    unfold computes_to; eauto.
  Qed.

  Local Opaque computes_to.

  Definition BindOpt {A' A''}
             (a_opt : option A')
             (k : A' -> option A'') :=
    Ifopt a_opt as a Then k a Else None.

  Lemma BindOpt_assoc {A''' A' A''} :
    forall (a_opt : option A''')
           (f : A''' -> option A')
           (g : A' -> option A''),
      BindOpt (BindOpt a_opt f) g =
      BindOpt a_opt (fun a => BindOpt (f a) g).
  Proof.
    destruct a_opt as [ ? | ]; simpl; intros; eauto.
  Qed.

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

Definition Cache_plus_inv (cache : Cache)
           (decode_inv : @CacheDecode cache -> Prop): Cache :=
  {| CacheFormat := @CacheFormat cache;
     CacheDecode := @CacheDecode cache;
     Equiv ce cd := Equiv ce cd /\ decode_inv cd|}.

Definition decode_strict
           {A B}
           {cache : Cache}
           {monoid : Monoid B}
           (decode : DecodeM A B)
  : DecodeM (A * B) B :=
  fun cd bs => Ifopt decode cd bs
    as abscd'
         Then Some (fst abscd', mempty, snd abscd')
         Else None.

Definition RestrictFormat
           {A B}
           {cache : Cache}
           (format : FormatM A B)
           (predicate : A -> Prop)
  : FormatM A B :=
  fun data env binxenv => format data env binxenv /\ predicate data.

(* DoneLax 'appends' a supplied bytestring onto the end of a format *)
Definition DoneLax {A B}
           {cache : Cache}
           {monoid : Monoid B}
           (format : FormatM A B)
  : FormatM (A * B) B :=
  fun data_rest env binxenv =>
    exists bin', fst binxenv = mappend bin' (snd data_rest) /\
                 format (fst data_rest) env (bin', snd binxenv).

Definition decode_obliviously
           {A B}
           {cache : Cache}
           {monoid : Monoid B}
           (decode : DecodeM (A * B) B)
  : B -> CacheDecode -> option (A * CacheDecode) :=
  fun bs cd => option_map (fun abc => (fst (fst abc), snd abc)) (decode bs cd).

(*Lemma CorrectDecoder_simpl_lax_equiv
      {A B}
      (cache : Cache)
      (monoid : Monoid B)
      (predicate : A -> Prop)
  : forall (decode_inv : CacheDecode -> Prop)
           (format : FormatM A B)
           (decode : DecodeM (A * B) B),
    CorrectDecoder (store := cache) monoid predicate (fun _ _ => True)  format
                   decode
                   decode_inv
    <-> CorrectDecoder_simpl
         (store := Cache_plus_inv cache decode_inv)
         (DoneLax (RestrictFormat format predicate))
         decode.
Proof.
  unfold CorrectDecoder, CorrectDecoder_simpl, DoneLax, RestrictFormat, decode_obliviously; split.
  - intuition.
    + rewrite unfold_computes in H2; simpl in *; destruct_ex; intuition.
      destruct (H0 env env' xenv a x b); simpl; intuition eauto.
      rewrite H, H7; simpl; eauto.
    + destruct (decode bin env') as [ [ [? ?] ?] | ] eqn: ?; destruct_ex;
        simpl in *; try discriminate; intuition; injections; eauto.
      eapply H1 in Heqo; intuition eauto; destruct_ex; intuition.
      rewrite H2; eexists; rewrite unfold_computes; intuition eauto.
      rewrite unfold_computes in H5; simpl; eauto.
  - intros; split_and; split; intros.
    + destruct (H0 env env' xenv (data, ext) (mappend bin ext)).
      simpl; intuition.
      apply unfold_computes; simpl.
      eexists; intuition eauto.
      split_and; eauto.
    + destruct (H1 env env' xenv' (data, ext) bin); eauto.
      split_and. rewrite unfold_computes in H5; destruct_ex; split_and.
      subst; split; eauto.
      eexists _, _; intuition eauto.
      eauto using unfold_computes.
Qed. *)

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

Lemma If_Opt_Then_Else_BindOpt {A B C}
  : forall (a_opt : option A)
           (t : A -> option B)
           (e : option B)
           (k : _ -> option C),
    BindOpt (Ifopt a_opt as a Then t a Else e) k
    = Ifopt a_opt as a Then (BindOpt (t a) k) Else (BindOpt e k).
Proof.
  destruct a_opt; simpl; intros; reflexivity.
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
  (DecodeBindOpt2 c%format (fun a b env => k%format)) : format_scope.

Notation "`( a , b ) <- c ; k" :=
  (DecodeBindOpt c%format (fun a b => k%format)) : format_scope.

Open Scope format_scope.

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

Add Parametric Morphism
    A B C
    (cache : Cache)
    (monoid : Monoid B)
    (predicate : A -> Prop)
    proj
    (decode : B -> CacheDecode -> option (C * B * CacheDecode))
    (decode_inv : CacheDecode -> Prop)
  : (fun format =>
       @CorrectDecoder A B cache C monoid predicate
                                proj format decode decode_inv)
    with signature (EquivFormat --> impl)
      as format_decode_correct_refineEquiv.
Proof.
  unfold EquivFormat, impl, pointwise_relation, CorrectDecoder;
    intuition eauto; intros.
  - eapply H1; eauto; apply H; eauto.
  - eapply H2; eauto.
  - destruct (H2 _ _ _ _ _ _ H0 H3 H4) as [ ? [? [? [? ?] ] ] ];
      intuition.
    repeat eexists; intuition eauto; apply H; eauto.
Qed.

Section DecodeWMeasure.
  Context {A : Type}. (* data type *)
  Context {B : Type}. (* bin type *)
  Context {cache : Cache}.
  Context {monoid : Monoid B}.

  Variable format_A : A -> CacheFormat -> Comp (B * CacheFormat).
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

Definition CorrectDecoderFor {A B C} {cache : Cache}
           {monoid : Monoid B} (proj : A -> C) Invariant FormatSpec :=
  { decodePlusCacheInv : _ |
    exists P_inv,
    (cache_inv_Property (snd decodePlusCacheInv) P_inv
     -> CorrectDecoder (A := A) monoid Invariant proj
                                FormatSpec
                                (fst decodePlusCacheInv)
                                (snd decodePlusCacheInv))
    /\ cache_inv_Property (snd decodePlusCacheInv) P_inv}.

Definition CorrectEncoderFor {A B} {cache : Cache}
      {monoid : Monoid B} FormatSpec :=
  { encoder' : EncodeM A B & forall a env,
        (forall benv', encoder' a env = Some benv' ->
                       refine (FormatSpec a env) (ret benv'))
        /\ (encoder' a env = None ->
            forall benv', ~ computes_to (FormatSpec a env) benv')}.

(* Here are the expected correctness lemmas for synthesized functions. *)
Lemma CorrectDecodeEncode
      {A B C} {cache : Cache}
      {monoid : Monoid B}
  : forall Invariant
           (proj : A -> C)
           (FormatSpec : FormatM A B)
           (encoder : CorrectEncoderFor FormatSpec)
           (decoder : CorrectDecoderFor proj Invariant FormatSpec),
    forall a envE envD b envE',
      Equiv envE envD
      -> Invariant a
      -> snd (proj1_sig decoder) envD
      -> projT1 encoder a envE = Some (b, envE')
      -> exists envD',
          fst (proj1_sig decoder) b envD = Some (proj a, mempty, envD').
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
  rewrite mempty_right in H4; eauto.
Qed.

Lemma CorrectEncodeDecode
      {A B C} {cache : Cache}
      {monoid : Monoid B}
  : forall Invariant
           (proj : A -> C)
           (FormatSpec : FormatM A B)
           (decoder : CorrectDecoderFor proj Invariant FormatSpec),
    forall bs ce cd cd' c ext,
      Equiv ce cd
      -> snd (proj1_sig decoder) cd
      -> fst (proj1_sig decoder) bs cd = Some (c, ext, cd')
      -> exists a,
          c = proj a /\
          Invariant a /\
         exists ce' bs',
           bs = mappend bs' ext
           /\ Equiv ce' cd' /\ FormatSpec a ce (bs', ce').
Proof.
  intros.
  destruct decoder as [decoder [Inv [decoder_OK Inv_cd] ] ]; simpl in *.
  specialize (decoder_OK Inv_cd).
  destruct decoder_OK as [_ decoder_OK].
  eapply decoder_OK in H1; eauto.
  intuition; destruct_ex; intuition eauto.
  eexists; intuition eauto.
Qed.

Lemma Start_CorrectDecoderFor
      {A B C} {cache : Cache}
      {monoid : Monoid B}
      (proj : A -> C)
      Invariant
      FormatSpec
      (decoder decoder_opt : B -> CacheDecode -> option (C * B * CacheDecode))
      (cache_inv : CacheDecode -> Prop)
      (P_inv : (CacheDecode -> Prop) -> Prop)
      (decoder_OK :
         cache_inv_Property cache_inv P_inv
         -> CorrectDecoder (A := A) monoid Invariant proj
                                    FormatSpec decoder cache_inv)
      (cache_inv_OK : cache_inv_Property cache_inv P_inv)
      (decoder_opt_OK : forall b cd, decoder b cd = decoder_opt b cd)
  : @CorrectDecoderFor A B C cache monoid proj Invariant FormatSpec.
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
           {A B} {cache : Cache}
           {monoid : Monoid B}
           Invariant
           FormatSpec
           (b : B)
           (ce : CacheFormat)
  := {a : option A |
      forall a' : A,
        a = Some a' <->
        (exists b1 b2 (ce' : CacheFormat),
            computes_to (FormatSpec a' ce) (b1, ce')
            /\ b = mappend b1 b2
            /\ Invariant a')}%comp.

Lemma refine_Pick_Decoder_For
      {A B} {cache : Cache}
      {monoid : Monoid B}
      {Invariant}
      {FormatSpec}
      (decoderImpl : @CorrectDecoderFor A B _ cache monoid id Invariant FormatSpec)
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
  destruct H1.
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
    rewrite H5; reflexivity.
Qed.

Notation "a ∋ b" := (@computes_to _ a b) (at level 65) : format_scope.
Notation "a ∌ b" := (~ @computes_to _ a b) (at level 65) : format_scope.
