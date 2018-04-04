Require Import
        Fiat.Computation
        Fiat.Common.DecideableEnsembles
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.ComposeOpt.

Section ComplementaryFormats.

  Variable A : Type.  (* Source Type, i.e. in-memory data *)
  Variable NA : Type. (* Not Source Type used to generate invalid target data *)
  Variable B : Type.  (* Target Type, usually ByteStrings *)
  Context {monoid_B : Monoid B}. (* Target type needs to be a monoid. *)

  Variable store : Cache. (* Store Type *)
  Variable Nstore : Cache. (* Not Store Type *)

  Variable Format : @FormatM A B store. (* The source format *)
  Variable NFormat : @FormatM NA B Nstore. (* The format of invalid bytestrings *)
  Variable NA_OK : NA -> Prop. (* Not source data property that ensures it will
                                generate invalid bytestrings *)

  Notation "a ∋ b" := (@computes_to _ a b) (at level 90).
  Notation "a ∌ b" := (~ @computes_to _ a b) (at level 90).

  (* To start, we define the set of invalid bytestrings for a format. *)
  Definition ComplementaryFormat
             (decode_inv : @CacheDecode store -> Prop) :=
    forall na b ns ns',
      NFormat na ns ∋ (b, ns') (* If a bytestring is in the invalid format *)
      -> NA_OK na              (* and the data was not okay *)
      -> forall a s s' s'',
        decode_inv s'' (* The binary string could not have been produced by *)
        -> Equiv s s'' (* an formatr that was started in a state equivalent to a *)
        -> Format a s ∌ (b, s')  (* valid decoder state (this should be the empty state) *).

  (* We can use a correct decoder to ensure that an invalid format is
     complementary.

     N.B. This specification is satsified whenever that the
     bytestrings in the complementary format will always be
     malformed. If the complementary format formats data
     appropriately, and then appends a bunch of junk data on the end,
     it won't satisfy this property, even though none of its
     bytestrings are included in the format. *)
  Definition ComplementaryDecoder
             (decode : @DecodeM A B store)
             (decode_inv : @CacheDecode store -> Prop) :=
    forall na b ns ns',
      NA_OK na
      -> NFormat na ns ∋ (b, ns')
      -> forall s b',
          decode_inv s
          -> decode (mappend b b') s = None.

  Theorem CorrectDecoderComplementary
    : forall (predicate : A -> Prop)
             (predicate_OK :
                forall a s b s',
                  Format a s ∋ (b, s')
                  -> predicate a)
             (rest_predicate : A -> B -> Prop := fun _ _ => True)
             (decode : @DecodeM A B store)
             (decode_inv : CacheDecode -> Prop),
      CorrectDecoder _ predicate rest_predicate Format decode decode_inv
      -> ComplementaryDecoder decode decode_inv
      -> ComplementaryFormat decode_inv.
  Proof.
    unfold ComplementaryFormat, CorrectDecoder, ComplementaryDecoder; intros.
    intro.
    eapply H0 in H1; eauto.
    exact (@CorrectDecoderNone _ _ _ _ _ _ _ _ _ H _ mempty _ H3 H1 _ _ _ H4 (predicate_OK _ _ _ _ H5) I H5).
  Qed.

End ComplementaryFormats.

Local Transparent computes_to.

Require Fiat.Narcissus.Stores.EmptyStore.
(* Given a proof that a decoder is correct, can we use it to derive
   an invalid format?*)
Definition DeriveComplementaryDecoder
           {A B monoid_B Format}
           (store := Fiat.Narcissus.Stores.EmptyStore.test_cache) (* Pure Formats are easier to deal with *)
  : forall (predicate predicate' : A -> Prop)
           (rest_predicate : A -> B -> Prop := fun _ _ => True)
           (decode : @DecodeM A B store)
           (decode_inv : CacheDecode -> Prop)
           (monoid_inj : forall b1 b2 b1' b2', mappend b1 b2 = mappend b1' b2' -> b1 = b1' /\ b2 = b2'),
    CorrectDecoder monoid_B predicate rest_predicate Format decode decode_inv
    -> (forall a, predicate a -> predicate' a)
    -> (forall a a' b s s' s'',
           predicate' a
           -> computes_to (Format a s) (b, s')
           -> computes_to (Format a' s) (b, s'')
           -> a = a')
    -> ComplementaryDecoder A _ B store _ Format
                            (fun a => ~ predicate' a) decode decode_inv.
Proof.
  unfold ComplementaryDecoder; simpl; intros.
  unfold CorrectDecoder in H.
  destruct (decode (mappend b b') s) as [ [ [? ?] ?] | ] eqn:?; eauto.
  destruct ((proj2 H) tt _ _ _ _ _ I H4 Heqo) as [? [? [? [? [? [? ?] ] ] ] ] ]; subst.
  rewrite H7 in Heqo.
  destruct ns, ns', s.
  apply monoid_inj in H7; intuition; subst.
  pose proof (H1 _ _ _ _ _ _ (H0 _ H8) H6 H3); subst; intuition.
Qed.

(* Similiar rule, but for formating a projection of a type. *)
Definition DeriveComplementaryDecoder_hetero
           {A NA B monoid_B Format}
           (store := Fiat.Narcissus.Stores.EmptyStore.test_cache) (* Pure Formats are easier to deal with *)
  : forall (predicate : A -> Prop)
           (predicate' : NA -> Prop)
           (proj : A -> NA)
           (rest_predicate : A -> B -> Prop := fun _ _ => True)
           (decode : @DecodeM A B store)
           (decode_inv : CacheDecode -> Prop)
           (monoid_inj : forall b1 b2 b1' b2', mappend b1 b2 = mappend b1' b2' -> b1 = b1' /\ b2 = b2'),
    CorrectDecoder monoid_B predicate rest_predicate (fun a => Format (proj a)) decode decode_inv
    -> (forall a, predicate a -> predicate' (proj a))
    -> (forall na na' b s s' s'',
           predicate' na
           -> computes_to (Format na s) (b, s')
           -> computes_to (Format na' s) (b, s'')
           -> na = na')
    -> ComplementaryDecoder A _ B store _ Format
                            (fun a => ~ predicate' a) decode decode_inv.
Proof.
  unfold ComplementaryDecoder; simpl; intros.
  unfold CorrectDecoder in H.
  destruct (decode (mappend b b') s) as [ [ [? ?] ?] | ] eqn:?; eauto.
  destruct ((proj2 H) tt _ _ _ _ _ I H4 Heqo) as [? [? [? [? [? [? ?] ] ] ] ] ]; subst.
  rewrite H7 in Heqo.
  destruct ns, ns', s.
  apply monoid_inj in H7; intuition; subst.
  pose proof (H1 _ _ _ _ _ _ (H0 _ H8) H6 H3); subst; intuition.
Qed.

Lemma ComplementFormatByInvertingPredicate
      (* If a format places any invariants on the source data, we can
      generate a invalid input by formatting data violating that
      invariant. *)
      {A NA B monoid_B Format}
      (store := Fiat.Narcissus.Stores.EmptyStore.test_cache) (* Pure Formats are easier to deal with *)
  : forall (predicate : A -> Prop)
           (predicate' : NA -> Prop)
           (proj : A -> NA)
           (rest_predicate : A -> B -> Prop := fun _ _ => True)
           (decode : @DecodeM A B store)
           (decode_inv : CacheDecode -> Prop)
           (monoid_inj : forall b1 b2 b1' b2', mappend b1 b2 = mappend b1' b2' -> b1 = b1' /\ b2 = b2'),
    CorrectDecoder monoid_B predicate rest_predicate (fun a => Format (proj a)) decode decode_inv
    -> (forall a, predicate a -> predicate' (proj a))
    -> (forall na na' b s s' s'',
           predicate' na
           -> computes_to (Format na s) (b, s')
           -> computes_to (Format na' s) (b, s'')
           -> na = na')
    -> ComplementaryFormat A NA B store store (fun a s b => Format (proj a) s b /\ predicate a)
                           Format (fun a => ~ predicate' a) decode_inv.
Proof.
  intros; eapply CorrectDecoderComplementary; eauto.
  3: eapply DeriveComplementaryDecoder_hetero; eauto.
  intros.
  unfold computes_to in H2; exact (proj2 H2).
  revert H; clear.
  unfold CorrectDecoder; intros [? ?]; split; intros.
  eapply H; eauto.
  apply (proj1 H4).
  destruct (H0 env env' xenv' data bin ext) as [? [? [? ?] ] ]; intuition eauto.
  eexists _, _; intuition eauto.
  unfold computes_to; eauto.
Qed.

Require Import Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedList
        Fiat.Narcissus.BinLib.AlignedDecoders
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.NatOpt
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Automation.Solver.
Require Import Bedrock.Word.

Section ExampleRecord.

  Instance ByteStringQueueMonoid : Monoid ByteString := ByteStringQueueMonoid.
  Instance store : Cache := Fiat.Narcissus.Stores.EmptyStore.test_cache. (* Pure Formats are easier to deal with *)

  Record TwoLists := { list1 : list (word 8); list2 : list (word 16)}.

  Definition TwoLists_Format
             (tl : TwoLists) :=
        format_nat 8 (|list1 tl|)
  ThenC format_nat 8 (|list2 tl|)
  ThenC format_list format_word (list2 tl)
  ThenC format_list format_word (list1 tl)
  DoneC.

  Definition TwoLists_OK (p : TwoLists) :=
    ((|list1 p|) < pow2 8 /\ ((|list2 p|) < pow2 8))%nat.

  Definition Simple_Format_decoder
    : CorrectDecoderFor TwoLists_OK TwoLists_Format.
  Proof.
    start_synthesizing_decoder.
    normalize_compose monoid.
    repeat decode_step idtac.
    intros; eauto using FixedList_predicate_rest_True.
    synthesize_cache_invariant.
    cbv beta; optimize_decoder_impl.
  Defined.

  Record MoreLists := { mlen1 : nat;
                        mlen2 : nat;
                        mlist1 : list (word 8);
                        mlist2 : list (word 16)}.

  Definition MoreListFormat
             (ml : MoreLists) :=
        format_nat 8 (mlen1 ml)
  ThenC format_nat 8 (mlen2 ml)
  ThenC format_list format_word (mlist2 ml)
  ThenC format_list format_word (mlist1 ml)
  DoneC.

  Lemma ComplementaryListFormat
    : exists decode_inv,
      ComplementaryFormat TwoLists MoreLists _ store store TwoLists_Format
                          MoreListFormat
                          (fun ml => (|mlist2 ml| + |mlist1 ml|) <> mlen1 ml + mlen2 ml)
                          decode_inv.
  Proof.
    eexists. 
    unfold ComplementaryFormat; intros.
    unfold MoreListFormat, compose, Bind2 in H.
    computes_to_inv; subst; simpl in *.
    injections.
    (* Okay, what do we do from here?*)
  Abort.

(* Lemma ComplementComposeFormat *)
(*       (* If a format places any invariants on the source data, we can *)
(*          generate a invalid input by formatting data violating that *)
(*          invariant. *) *)
(* {A A' NA B monoid_B Format1 Format2 NAFormat1 NAFormat2 NAFormat_OK} *)
(*       (store := Fiat.Narcissus.Stores.EmptyStore.test_cache) (* Pure Formats are easier to deal with *) *)
(*   : forall (predicate : A -> Prop) *)
(*            (predicate' : A' -> Prop) *)
(*            (predicate'' : NA -> Prop) *)
(*            (project : A -> A') *)
(*            (rest_predicate : A -> B -> Prop := fun _ _ => True) *)
(*            (decode : @DecodeM A B store) *)
(*            (decode_inv : CacheDecode -> Prop) *)
(*            (monoid_inj : forall b1 b2 b1' b2', mappend b1 b2 = mappend b1' b2' -> b1 = b1' /\ b2 = b2'), *)
(*     CorrectDecoder monoid_B predicate rest_predicate (fun a => Format1 (project a)) decode decode_inv *)
(*     -> (forall a, predicate a -> predicate' (project a)) *)
(*     -> (forall na na' b s s' s'', *)
(*            predicate' na *)
(*            -> computes_to (Format1 na s) (b, s') *)
(*            -> computes_to (Format1 na' s) (b, s'') *)
(*            -> na = na') *)
(*     -> ComplementaryFormat A _ B store store *)
(*                           (fun (data : A) (ctx : CacheFormat) => *)
(*                              compose _ (Format1 (project data)) (Format2 data) ctx)%comp *)
(*                           (fun (data : A' * NA) (ctx : CacheFormat) => *)
(*                              compose _ (NAFormat1 (fst data)) (NAFormat2 (snd data)) ctx)%comp *)
(*                           NAFormat_OK decode_inv *)
(* . *)


(*   : forall (predicate : A -> Prop) *)
(*            (predicate' : NA -> Prop) *)
(*            (proj : A -> NA) *)
(*            (rest_predicate : A -> B -> Prop := fun _ _ => True) *)
(*            (decode : @DecodeM A B store) *)
(*            (decode_inv : CacheDecode -> Prop) *)
(*            (monoid_inj : forall b1 b2 b1' b2', mappend b1 b2 = mappend b1' b2' -> b1 = b1' /\ b2 = b2'), *)
(*     CorrectDecoder monoid_B predicate rest_predicate (fun a => Format (proj a)) decode decode_inv *)
(*     -> (forall a, predicate a -> predicate' (proj a)) *)
(*     -> (forall na na' b s s' s'', *)
(*            predicate' na *)
(*            -> computes_to (Format na s) (b, s') *)
(*            -> computes_to (Format na' s) (b, s'') *)
(*            -> na = na') *)

(*       {A A' B} *)
(*       {cache : Cache} *)
(*       {P  : CacheDecode -> Prop} *)
(*       {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop} *)
(*       (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P)) *)
(*       (monoid : Monoid B) *)
(*       (project : A -> A') *)
(*       (predicate : A -> Prop) *)
(*       (predicate' : A' -> Prop) *)
(*       (predicate_rest' : A -> B -> Prop) *)
(*       (predicate_rest : A' -> B -> Prop) *)
(*       (format1 : A' -> CacheFormat -> Comp (B * CacheFormat)) *)
(*       (format2 : A -> CacheFormat -> Comp (B * CacheFormat)) *)
(*       (decode1 : B -> CacheDecode -> option (A' * B * CacheDecode)) *)
(*       (decode1_pf : *)
(*          cache_inv_Property P P_inv1 *)
(*          -> CorrectDecoder *)
(*               monoid predicate' *)
(*               predicate_rest *)
(*               format1 decode1 P) *)
(*       (pred_pf : forall data, predicate data -> predicate' (project data)) *)
(*       (predicate_rest_impl : *)
(*          forall a' b *)
(*                 a ce ce' ce'' b' b'', *)
(*            computes_to (format1 a' ce) (b', ce') *)
(*            -> project a = a' *)
(*            -> predicate a *)
(*            -> computes_to (format2 a ce') (b'', ce'') *)
(*            -> predicate_rest' a b *)
(*            -> predicate_rest a' (mappend b'' b)) *)
(*       (decode2 : A' -> B -> CacheDecode -> option (A * B * CacheDecode)) *)
(*       (decode2_pf : forall proj, *)
(*           predicate' proj ->c *)
(*           cache_inv_Property P P_inv2 -> *)
(*           CorrectDecoder monoid *)
(*                                   (fun data => predicate data /\ project data = proj) *)
(*                                   predicate_rest' *)
(*                                   format2 *)
(*                                   (decode2 proj) P) *)
(*   : ComplementaryFormat A NA B store store *)
(*                         (fun (data : A) (ctx : CacheFormat) => *)
(*                            compose _ (format1 (project data)) (format2 data)  ctx)%comp *)
(*                         (fun (data : A) (ctx : CacheFormat) => *)
(*                            compose _ (format1 (project data)) (format2 data)  ctx *)
(*                         )%comp. *)

(*     CorrectDecoder *)
(*       monoid *)
(*       (fun a => predicate a) *)
(*       predicate_rest' *)
(*       (fun (data : A) (ctx : CacheFormat) => *)
(*          compose _ (format1 (project data)) (format2 data)  ctx *)
(*       )%comp *)
(*       (fun (bin : B) (env : CacheDecode) => *)
(*          `(proj, rest, env') <- decode1 bin env; *)
(*            decode2 proj rest env') P. *)
(* Proof. *)

(* Lemma ComplementFormatByInvertingPredicate *)
(*       (* If a format places any invariants on the source data, we can *)
(*       generate a invalid input by formatting data violating that *)
(*       invariant. *) *)
(*       {A NA B monoid_B Format} *)
(*       (store := Fiat.Narcissus.Stores.EmptyStore.test_cache) (* Pure Formats are easier to deal with *) *)
(*   : forall (predicate : A -> Prop) *)
(*            (predicate' : NA -> Prop) *)
(*            (proj : A -> NA) *)
(*            (rest_predicate : A -> B -> Prop := fun _ _ => True) *)
(*            (decode : @DecodeM A B store) *)
(*            (decode_inv : CacheDecode -> Prop) *)
(*            (monoid_inj : forall b1 b2 b1' b2', mappend b1 b2 = mappend b1' b2' -> b1 = b1' /\ b2 = b2'), *)
(*     CorrectDecoder monoid_B predicate rest_predicate (fun a => Format (proj a)) decode decode_inv *)
(*     -> (forall a, predicate a -> predicate' (proj a)) *)
(*     -> (forall na na' b s s' s'', *)
(*            predicate' na *)
(*            -> computes_to (Format na s) (b, s') *)
(*            -> computes_to (Format na' s) (b, s'') *)
(*            -> na = na') *)
(*     -> ComplementaryFormat A NA B store store (fun a s b => Format (proj a) s b /\ predicate a) *)
(*                            Format (fun a => ~ predicate' a) decode_inv. *)
(* Proof. *)
(*   intros; eapply CorrectDecoderComplementary; eauto. *)
(*   3: eapply DeriveComplementaryDecoder_hetero; eauto. *)
(*   intros. *)
(*   unfold computes_to in H2; exact (proj2 H2). *)
(*   revert H; clear. *)
(*   unfold CorrectDecoder; intros [? ?]; split; intros. *)
(*   eapply H; eauto. *)
(*   apply (proj1 H4). *)
(*   destruct (H0 env env' xenv' data bin ext) as [? [? [? ?] ] ]; intuition eauto. *)
(*   eexists _, _; intuition eauto. *)
(*   unfold computes_to; eauto. *)
(* Qed. *)
