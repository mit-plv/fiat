Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Require Import
        Bedrock.Word
        Coq.ZArith.ZArith
        Coq.NArith.NArith
        Coq.Arith.Arith
        Coq.Numbers.Natural.Peano.NPeano
        Coq.Logic.Eqdep_dec
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.BinLib.AlignedByteString.

Section AlignedDecodeM.

  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Definition AlignedDecodeM
             (A : Type)
             (n : nat):=
    ByteBuffer.t n (* Vector of bytes that is being decoded *)
    -> nat          (* The current vector index *)
    -> CacheDecode  (* The current environment *)
    -> option (A * nat * CacheDecode) (* Error monad + value + updated index + updated cache *).

  Definition BindAlignedDecodeM
             {A B : Type}
             {n : nat}
             (a : AlignedDecodeM A n)
             (b : A -> AlignedDecodeM B n)
    : AlignedDecodeM B n :=
    fun v idx c => (Ifopt a v idx c  as a' Then (b (fst (fst a')) v (snd (fst a')) (snd a')) Else None).

  Definition BindResetAlignedDecodeM
             {A B : Type}
             {n : nat}
             (a : AlignedDecodeM A n)
             (b : A -> AlignedDecodeM B n)
    : AlignedDecodeM B n :=
    fun v idx c => (Ifopt a v idx c  as a' Then (b (fst (fst a')) v idx (snd a')) Else None).

  Definition ReturnAlignedDecodeM
             {A : Type}
             {n : nat}
             (a : A)
    : AlignedDecodeM A n :=
    fun v idx c => Some (a, idx, c).

  Definition AlignedDecodeMEquiv
             {A} {n}
             (a1 a2 : AlignedDecodeM A n) : Prop :=
    forall v idx c, a1 v idx c = a2 v idx c.

  Lemma AlignedDecodeMEquiv_refl {A : Type} {n}:
    forall (a : AlignedDecodeM A n),
      AlignedDecodeMEquiv a a.
  Proof.
    unfold AlignedDecodeMEquiv; intros; reflexivity.
  Qed.

  Lemma AlignedDecodeMEquiv_sym {A : Type} {n}:
    forall (a1 a2 : AlignedDecodeM A n),
      AlignedDecodeMEquiv a1 a2 -> AlignedDecodeMEquiv a2 a1.
  Proof.
    unfold AlignedDecodeMEquiv; intros; congruence.
  Qed.

  Lemma AlignedDecodeMEquiv_trans {A : Type} {n}:
    forall (a1 a2 a3 : AlignedDecodeM A n),
      AlignedDecodeMEquiv a1 a2 ->
      AlignedDecodeMEquiv a2 a3 ->
      AlignedDecodeMEquiv a1 a3.
  Proof.
    unfold AlignedDecodeMEquiv; intros; congruence.
  Qed.

  Global Instance Equivalence_AlignedDecodeMEquiv {A : Type} {n} :
    Equivalence (@AlignedDecodeMEquiv A n) :=
    {| Equivalence_Reflexive := AlignedDecodeMEquiv_refl;
      Equivalence_Symmetric := AlignedDecodeMEquiv_sym;
      Equivalence_Transitive := AlignedDecodeMEquiv_trans |}.

  Lemma BindAlignedDecodeM_assoc {A B C : Type} {n}:
    forall (a : AlignedDecodeM A n)
           (f : A -> AlignedDecodeM B n)
           (g : B -> AlignedDecodeM C n),
      AlignedDecodeMEquiv (BindAlignedDecodeM (BindAlignedDecodeM a f) g)
                          (BindAlignedDecodeM a (fun a => BindAlignedDecodeM (f a) g)).
  Proof.
    unfold BindAlignedDecodeM, AlignedDecodeMEquiv; simpl; intros.
    destruct (a v idx c); simpl; eauto.
  Qed.

  Lemma ReturnAlignedDecodeM_LeftUnit {A B : Type} {n}:
    forall (a : A)
           (f : A -> AlignedDecodeM B n),
      AlignedDecodeMEquiv (BindAlignedDecodeM (ReturnAlignedDecodeM a) f)
                          (f a).
  Proof.
    unfold ReturnAlignedDecodeM, BindAlignedDecodeM, AlignedDecodeMEquiv; simpl; intros.
    reflexivity.
  Qed.

  Lemma ReturnAlignedDecodeM_RightUnit {A B : Type} {n}:
    forall (f : AlignedDecodeM A n),
      AlignedDecodeMEquiv (BindAlignedDecodeM f ReturnAlignedDecodeM) f.
  Proof.
    unfold ReturnAlignedDecodeM, BindAlignedDecodeM, AlignedDecodeMEquiv; simpl; intros.
    destruct (f v idx c) as [ [ [? ?] ?] | ] ; simpl; reflexivity.
  Qed.

  Definition ThrowAlignedDecodeM
             {A : Type}
             {n : nat}
    : AlignedDecodeM A n:=
    fun _ _ _ => None.

  Fixpoint Vector_nth_opt
           {A : Type}
           {n : nat}
           (v : Vector.t A n)
           (m : nat)
    : option A :=
    match m, v with
    | 0,  Vector.cons a _ _ => Some a
    | S m', Vector.cons _ _ v' => Vector_nth_opt v' m'
    | _, _ => None
    end.

  Definition nth_opt
             {n : nat}
             (v : ByteBuffer.t n)
             (m : nat)
    : option char := Vector_nth_opt v m.

  Lemma nth_opt_some_lt n (v : ByteBuffer.t n) idx c :
    nth_opt v idx = Some c ->
    (idx < n)%nat.
  Proof.
    revert idx.
    induction v; intros []; cbn; intros; try discriminate; injections.
    lia.
    eapply IHv in H.
    lia.
  Qed.

  Definition GetCurrentByte (* Gets the current byte and increments the current index. *)
             {n : nat}
    : AlignedDecodeM char n :=
    fun v idx c => Ifopt (nth_opt v idx) as b Then Some (b, S idx, addD c 8) Else None.

  Definition GetByteAt (* Gets the byte at the specified index, but leaves
                          the current index and state unchanged. *)
             {n : nat}
             (idx : nat)
    : AlignedDecodeM char n :=
    fun v idx' c => Ifopt (nth_opt v idx) as b Then Some (b, idx', c) Else None.

  Definition SkipCurrentByte (* Gets the current byte and increments the current index. *)
             {n : nat}
    : AlignedDecodeM () n :=
    fun v idx c => Ifopt (nth_opt v idx) as b Then Some ((), S idx, addD c 8) Else None.

  Fixpoint SkipCurrentBytes (* Skips the next m bytes and increments the current index. *)
           {n : nat}
           (m : nat)
    : AlignedDecodeM () n :=
    match m return AlignedDecodeM () n with
    | 0 => ReturnAlignedDecodeM ()
    | S m' => BindAlignedDecodeM
                SkipCurrentByte
                (fun _ => BindAlignedDecodeM
                            (SkipCurrentBytes m')
                            (fun _ => ReturnAlignedDecodeM ()))
    end.

  Definition plus_comm_transparent :
    forall x y, x + y = y + x.
  Proof.
    induction x; simpl.
    - induction y; simpl; congruence.
    - intros.
      rewrite IHx.
      induction y.
      + reflexivity.
      + simpl; rewrite IHy; reflexivity.
  Defined.

  Fixpoint GetCurrentBytes (* Gets the current byte and increments the current index. *)
           {n : nat}
           (m : nat)
    : AlignedDecodeM (word (m * 8)) n :=
    match m return AlignedDecodeM (word (m * 8)) n with
    | 0 => ReturnAlignedDecodeM WO
    | S m' => BindAlignedDecodeM
                GetCurrentByte
                (fun w => BindAlignedDecodeM
                            (GetCurrentBytes m')
                            (fun w' =>  ReturnAlignedDecodeM (
                                            eq_rect _ _ (Core.append_word w' w) _ (plus_comm_transparent (m' * 8) 8))))
    end.

  Fixpoint GetBytesAt (* Gets the current byte and increments the current index. *)
           {n : nat}
           (idx : nat)
           (m : nat)
    : AlignedDecodeM (word (m * 8)) n :=
    match m return AlignedDecodeM (word (m * 8)) n with
    | 0 => ReturnAlignedDecodeM WO
    | S m' => BindAlignedDecodeM
                (GetByteAt idx)
                (fun w => BindAlignedDecodeM
                            (GetBytesAt (S idx) m')
                            (fun w' =>  ReturnAlignedDecodeM (
                                            eq_rect _ _ (Core.append_word w' w) _ (plus_comm_transparent (m' * 8) 8))))
    end.

  (* Equivalence Criteria:
     A bit-aligned decoder and byte-aligned decoder are equivalent when
     - the byte aligned decoder fails when the bit aligned decoder does,
     - decodes the same values as the bit-aligned decoder
     - updates the cache in the same way as the bit-aligned decoder,
       - and consumes the same number of bytes as the bit-aligned decoder.
   *)

  Definition DecodeMEquivAlignedDecodeM
             {C : Type}
             (f : DecodeM (C * ByteString) ByteString)
             (f' : forall {numBytes}, AlignedDecodeM C numBytes)
    := (forall numBytes_hd
               (n : nat)
               (v : Vector.t _ (S numBytes_hd)) cd,
           f' v (S n) cd =
           Ifopt (f' (Vector.tl v) n cd) as a Then Some (fst (fst a), S (snd (fst a)), snd a) Else None)
       /\ (forall n (v : ByteBuffer.t n) cd c b' cd',
             f (build_aligned_ByteString v) cd = Some (c, b', cd') ->
             length_ByteString (build_aligned_ByteString v) >= length_ByteString b')%nat
       /\ (forall n (v : ByteBuffer.t n) cd,
              (f (build_aligned_ByteString v) cd = None <->
               f' v 0 cd = None)
              /\
              (forall c bs' cd',
                  f (build_aligned_ByteString v) cd = Some (c, bs', cd') ->
                  f' v 0 cd = Some (c, n - (numBytes bs'), cd')
                  /\ exists v' : Vector.t _ (n - (numBytes bs')),
                      (build_aligned_ByteString v) = ByteString_enqueue_ByteString (build_aligned_ByteString v') bs'
          ))
  (*       /\ (forall n (v : ByteBuffer.t n) cd c n' cd', *)
  (* f' v 0 cd = Some (c, n', cd') -> *)
  (* exists m', *)
  (*   {H : n = n' + m' & *)
  (*        f (build_aligned_ByteString v) cd = *)
  (*        Some (c, build_aligned_ByteString (snd (Vector_split _ _ (eq_rect _ _ v _ H))), cd')}) *).

  (* This definition is indexed by the available bytes in the buffer. *)
  Definition DecodeMEquivAlignedDecodeM'
             (avail : nat)
             {C : Type}
             (f : DecodeM (C * ByteString) ByteString)
             (f' : forall {numBytes}, AlignedDecodeM C numBytes)
    := (forall numBytes_hd
               (n : nat)
               (v : Vector.t _ (S numBytes_hd)) cd,
           avail = numBytes_hd - n ->
           f' v (S n) cd =
           Ifopt (f' (Vector.tl v) n cd) as a Then Some (fst (fst a), S (snd (fst a)), snd a) Else None)
       /\ (forall n (v : ByteBuffer.t n) cd c b' cd',
             avail = n ->
             f (build_aligned_ByteString v) cd = Some (c, b', cd') ->
             length_ByteString (build_aligned_ByteString v) >= length_ByteString b')%nat
       /\ (forall n (v : ByteBuffer.t n) cd,
              avail = n ->
              (f (build_aligned_ByteString v) cd = None <->
               f' v 0 cd = None)
              /\
              (forall c bs' cd',
                  f (build_aligned_ByteString v) cd = Some (c, bs', cd') ->
                  f' v 0 cd = Some (c, n - (numBytes bs'), cd')
                  /\ exists v' : Vector.t _ (n - (numBytes bs')),
                      (build_aligned_ByteString v) = ByteString_enqueue_ByteString (build_aligned_ByteString v') bs'
          )).

  Arguments Nat.div : simpl never.

  Lemma DecodeMEquivAlignedDecodeM'_equiv C f f' :
    @DecodeMEquivAlignedDecodeM C f f' <->
      (forall avail, @DecodeMEquivAlignedDecodeM' avail C f f').
  Proof.
    split; intros H;
      (split; [ | split ]; intros; subst; eapply H; eauto).
  Qed.

  Lemma DecodeMEquivAlignedDecodeM'_trans  {C} avail :
    forall bit_decoder1 byte_decoder1 bit_decoder2 byte_decoder2,
      DecodeMEquivAlignedDecodeM' avail (C := C) bit_decoder1 byte_decoder1
      -> (forall b cd, bit_decoder1 b cd  = bit_decoder2 b cd)
      -> (forall n, AlignedDecodeMEquiv (byte_decoder1 n) (byte_decoder2 n))
      -> DecodeMEquivAlignedDecodeM' avail bit_decoder2 byte_decoder2.
  Proof.
    unfold DecodeMEquivAlignedDecodeM'.
    unfold AlignedDecodeMEquiv.
    intros * H H1 H2. repeat setoid_rewrite <- H1. repeat setoid_rewrite <- H2.
    split; [ | split ]; intuition eauto.
  Qed.

  Lemma DecodeMEquivAlignedDecodeM_trans  {C} :
    forall bit_decoder1 byte_decoder1 bit_decoder2 byte_decoder2,
      DecodeMEquivAlignedDecodeM (C := C) bit_decoder1 byte_decoder1
      -> (forall b cd, bit_decoder1 b cd  = bit_decoder2 b cd)
      -> (forall n, AlignedDecodeMEquiv (byte_decoder1 n) (byte_decoder2 n))
      -> DecodeMEquivAlignedDecodeM bit_decoder2 byte_decoder2.
  Proof.
    setoid_rewrite DecodeMEquivAlignedDecodeM'_equiv.
    eauto using DecodeMEquivAlignedDecodeM'_trans.
  Qed.

  Lemma Return_DecodeMEquivAlignedDecodeM' {A : Type} avail
        (a : A)
    : DecodeMEquivAlignedDecodeM' avail
        (fun (b : ByteString) (cd : CacheDecode) => Some (a, b, cd))
        (fun numBytes => ReturnAlignedDecodeM a).
  Proof.
    unfold ReturnAlignedDecodeM.
    split; [ | split ]; intros.
    - reflexivity.
    - injections. lia.
    - intuition eauto; injections; try discriminate.
      cbn. repeat f_equal. lia.
      setoid_rewrite <- build_aligned_ByteString_append.
      cbn. replace (n - n) with 0 by lia.
      exists (@Vector.nil _).
      reflexivity.
  Qed.

  Lemma Return_DecodeMEquivAlignedDecodeM {A : Type}
        (a : A)
    : DecodeMEquivAlignedDecodeM
        (fun (b : ByteString) (cd : CacheDecode) => Some (a, b, cd))
        (fun numBytes => ReturnAlignedDecodeM a).
  Proof.
    setoid_rewrite DecodeMEquivAlignedDecodeM'_equiv.
    eauto using Return_DecodeMEquivAlignedDecodeM'.
  Qed.

  Lemma A_decode_aligned_shift {A : Type}
        (A_decode_aligned : forall {numBytes}, AlignedDecodeM A numBytes)
    : (forall (numBytes_hd n : nat) (v : Vector.t char (S numBytes_hd)) (cd : CacheDecode),
          @A_decode_aligned (S numBytes_hd) v (S n) cd =
          (Ifopt @A_decode_aligned numBytes_hd (Vector.tl v) n cd as a0
                                                                       Then Some (fst (fst a0), S (snd (fst a0)), snd a0) Else None))
      -> forall (numBytes_hd numBytes_tl : nat)
                (v : Vector.t char (numBytes_hd + numBytes_tl)) (cd : CacheDecode),
        @A_decode_aligned _ v numBytes_hd cd =
        (Ifopt @A_decode_aligned _ (snd (Vector_split _ _ v)) 0 cd as a0
                                                                        Then Some (fst (fst a0), numBytes_hd + (snd (fst a0)), snd a0) Else None).
  Proof.
    induction numBytes_hd; simpl; intros.
    - destruct ( A_decode_aligned numBytes_tl v 0 cd) as [ [ [? ?] ?]  | ]; reflexivity.
    - rewrite H.
      rewrite IHnumBytes_hd; destruct (Vector_split numBytes_hd numBytes_tl (Vector.tl v)) eqn: ?; simpl.
      match goal with
        |- context [Vector_split ?m ?n ?v] => replace (Vector_split m n v) with (t, t0)
      end; simpl.
      destruct (A_decode_aligned numBytes_tl t0 0 cd); simpl; reflexivity.
      rewrite <- Heqp;  reflexivity.
  Qed.

  (* Lemma A_decode_aligned_shift' {A : Type}
        (A_decode_aligned : forall {numBytes}, AlignedDecodeM A numBytes)
    : (forall (numBytes_hd n : nat) (v : Vector.t char (S numBytes_hd)) (cd : CacheDecode),
          @A_decode_aligned (S numBytes_hd) v (S n) cd =
          (Ifopt @A_decode_aligned numBytes_hd (Vector.tl v) n cd as a0
        Then Some (fst (fst a0), S (snd (fst a0)), snd a0) Else None))
      -> forall (numBytes_hd numBytes_tl : nat)
                (v : Vector.t char (numBytes_hd + numBytes_tl)) (cd : CacheDecode),
        @A_decode_aligned _ (snd (Vector_split _ _ v)) 0 cd =
          (Ifopt @A_decode_aligned _ v numBytes_hd cd as a0
        Then Some (fst (fst a0), (snd (fst a0)) - numBytes_hd, snd a0) Else None).
  Proof.
    induction numBytes_hd; simpl; intros.
    - destruct ( A_decode_aligned numBytes_tl v 0 cd) as [ [ [? ?] ?]  | ]; simpl; eauto.
      rewrite <- minus_n_O; reflexivity.
    - rewrite H.
      destruct (Vector_split numBytes_hd numBytes_tl (Vector.tl v)) eqn: ?; simpl.
      match goal with
        |- context [Vector_split ?m ?n ?v] => replace (Vector_split m n v) with (t, t0)
      end; simpl.
      destruct (A_decode_aligned (numBytes_hd + numBytes_tl) (Vector.tl v) numBytes_hd cd) as [ [ [? ?] ?] | ]
                                                                                                eqn: ?; simpl.
      specialize (IHnumBytes_hd _ (Vector.append
                                     (fst (Vector_split numBytes_hd numBytes_tl (Vector.tl v)))
                                     (snd (Vector_split numBytes_hd numBytes_tl (Vector.tl v)))) cd);
        simpl in *.
      rewrite Heqp in IHnumBytes_hd; simpl in *.
      replace (snd (Vector_split numBytes_hd numBytes_tl (Vector.append t t0))) with
          t0 in IHnumBytes_hd.
      + rewrite IHnumBytes_hd.
      destruct (A_decode_aligned numBytes_tl t0 0 cd); simpl; reflexivity.
      rewrite <- Heqp;  reflexivity.
  Qed. *)

  Lemma proper_consumer_t_None {C} avail
        (t' : forall {numBytes}, AlignedDecodeM C numBytes)
        (t'_OK : forall (numBytes_hd n0 : nat) (v0 : Vector.t char (S numBytes_hd)) (cd0 : CacheDecode),
            avail = numBytes_hd - n0 ->
            @t' (S numBytes_hd) v0 (S n0) cd0 =
            (Ifopt @t' numBytes_hd (Vector.tl v0) n0 cd0 as a0 Then
                                                               Some (fst (fst a0), S (snd (fst a0)), snd a0) Else None))
    : forall {n m} (v : ByteBuffer.t (m + n)) (v1 : Vector.t char m) (v2 : Vector.t char n) cd,
      avail = n ->
      build_aligned_ByteString v = build_aligned_ByteString (Vector.append v1 v2) ->
      t' v2 0 cd = None <->
      t' v m cd = None.
  Proof.
    intros.
    apply build_aligned_ByteString_inj in H0. subst v.
    revert H.
    revert n v2 cd; induction v1.
    - easy.
    - simpl; intros.
      rewrite t'_OK by lia.
      rewrite IHv1 by lia.
      destruct t'; easy.
  Qed.

  Lemma proper_consumer_t_Some {C} avail
        (t' : forall {numBytes}, AlignedDecodeM C numBytes)
        (t'_OK : forall (numBytes_hd n0 : nat) (v0 : Vector.t char (S numBytes_hd)) (cd0 : CacheDecode),
            avail = numBytes_hd - n0 ->
            @t' (S numBytes_hd) v0 (S n0) cd0 =
            (Ifopt @t' numBytes_hd (Vector.tl v0) n0 cd0 as a0 Then
                                                               Some (fst (fst a0), S (snd (fst a0)), snd a0) Else None))
    : forall {n m} (v : ByteBuffer.t (m + n)) (v1 : Vector.t char m) (v2 : Vector.t char n) cd c k cd',
      avail = n ->
      build_aligned_ByteString v = build_aligned_ByteString (Vector.append v1 v2) ->
      t' v2 0 cd = Some (c, k, cd') <->
      t' v m cd = Some (c, m + k, cd').
  Proof.
    intros.
    apply build_aligned_ByteString_inj in H0. subst v.
    revert H.
    revert n v2 cd; induction v1.
    - easy.
    - simpl; intros.
      rewrite t'_OK by lia.
      rewrite IHv1 by lia.
      simpl.
      destruct t'; try easy.
      destruct_conjs; simpl in *; split; intros; injections; eauto.
  Qed.

  Lemma Seq_DecodeMEquivAlignedDecodeM' {A C : Type} avail
        (A_decode : DecodeM (A * ByteString) ByteString)
        (A_decode_aligned : forall {numBytes}, AlignedDecodeM A numBytes)
        (t : A -> DecodeM (C * ByteString) ByteString)
        (t' : A -> forall {numBytes}, AlignedDecodeM C numBytes)
        (u : DecodeM (C * ByteString) ByteString)
        (u' : forall {numBytes}, AlignedDecodeM C numBytes)
        (* We can strengthen this by taking "equivalent" functions on buffer and
        indices. However, it doesn't seem worth the effort as it complicates the
        proof significantly. *)
        (reset : bool)
        (fcd : CacheDecode -> CacheDecode -> CacheDecode)
    : DecodeMEquivAlignedDecodeM' avail A_decode (@A_decode_aligned)
      -> (if reset
          then (forall a, DecodeMEquivAlignedDecodeM' avail (t a) (@t' a))
          else (forall a numBytes (v : ByteBuffer.t numBytes) idx cd idx' cd',
                   A_decode_aligned v idx cd = Some (a, idx', cd') ->
                   avail = numBytes - idx ->
                   DecodeMEquivAlignedDecodeM' (numBytes - idx') (t a) (@t' a)))
      -> DecodeMEquivAlignedDecodeM' avail u (@u')
      -> DecodeMEquivAlignedDecodeM' avail
           (fun b cd =>
              match A_decode b cd with
              | Some (a, b', cd') => t a (if reset then b else b') (fcd cd cd')
              | None => u b cd
              end)
           (fun numBytes v idx cd =>
              match A_decode_aligned v idx cd with
              | Some (a, idx', cd') => t' a v (if reset then idx else idx') (fcd cd cd')
              | None => u' v idx cd
              end).
  Proof.
    intros Ha Ht Hu. split; [| split].
    - intros. subst.
      rewrite (proj1 Ha) by eauto.
      destruct A_decode_aligned as [ [[??]?] |] eqn:?; simpl.
      2: eapply Hu; eauto.
      destruct reset; eapply Ht; eauto.
    - intros * -> H.
      destruct A_decode as [ [[??]?] |] eqn:Heq; simpl.
      2: eapply Hu; eauto.

      destruct reset; intros. eapply Ht; eauto.

      pose proof Heq as Heq'.
      eapply (proj1 (proj2 Ha)) in Heq'; eauto.
      eapply (proj2 (proj2 Ha)) in Heq; eauto.
      destruct Heq as [Heq [ ? Hb]].
      eapply Ht in Heq; try lia.
      eapply build_aligned_ByteString_split' in Hb.
      destruct Hb as [? Hb].
      rewrite Hb in H.
      eapply (proj1 (proj2 Heq)) in H; try lia.
      rewrite <- Hb in H. lia.
    - intros n v cd ->.
      destruct A_decode as [ [[a b] cd'] |] eqn:Heq.
      2: eapply Ha in Heq; eauto; rewrite Heq; eapply Hu; eauto.

      assert (numBytes b <= n)%nat as L. {
        eapply (proj1 (proj2 Ha)) in Heq.
        eapply length_ByteString_le_numBytes in Heq; eauto.
        reflexivity.
      }

      eapply Ha in Heq; eauto.
      destruct Heq as [Heq [v' Hv]].
      rewrite Heq.
      destruct reset; try eapply Ht; eauto.
      rewrite Hv.

      destruct (build_aligned_ByteString_split' _ _ _ Hv) as [vb Hb].
      assert (numBytes b = n - (n - numBytes b)) as Hnb by lia.
      destruct Hnb.
      rewrite Hb in Hv at 2.
      rewrite <- build_aligned_ByteString_append in Hv.

      assert (n - numBytes b + numBytes b = n) as Hn by lia.
      revert dependent v. revert v'. revert Hn.
      generalize (n - numBytes b). intros m Hm.
      rewrite <- Hm.
      intros.

      eapply Ht in Heq; try lia.
      split.
      + rewrite Hb at 1.
        rewrite <- proper_consumer_t_None; eauto;
          intros; apply Heq; lia.
      + intros ??? H.

        assert (numBytes bs' <= numBytes b)%nat. {
          rewrite Hb in H.
          eapply (proj1 (proj2 Heq)) in H; try lia.
          rewrite <- Hb in H.
          eauto using length_ByteString_le_numBytes.
        }

        rewrite Hb in H.
        eapply Heq in H; try lia. destruct H as [H [ v'' Hvb ]].
        eapply proper_consumer_t_Some in H;
          intros; try eapply Heq; eauto; try lia.
        rewrite H.
        rewrite <- Nat.add_sub_assoc by eauto.
        split; eauto.
        exists (Vector.append v' v'').
        rewrite !build_aligned_ByteString_append.
        rewrite <- ByteString_enqueue_ByteString_assoc.
        congruence.
  Qed.

  Lemma Seq_DecodeMEquivAlignedDecodeM {A C : Type}
        (A_decode : DecodeM (A * ByteString) ByteString)
        (A_decode_aligned : forall {numBytes}, AlignedDecodeM A numBytes)
        (t : A -> DecodeM (C * ByteString) ByteString)
        (t' : A -> forall {numBytes}, AlignedDecodeM C numBytes)
        (u : DecodeM (C * ByteString) ByteString)
        (u' : forall {numBytes}, AlignedDecodeM C numBytes)
        (reset : bool)
        (fcd : CacheDecode -> CacheDecode -> CacheDecode)
    : DecodeMEquivAlignedDecodeM A_decode (@A_decode_aligned)
      -> (forall a, DecodeMEquivAlignedDecodeM (t a) (@t' a))
      -> (DecodeMEquivAlignedDecodeM u (@u'))
      -> DecodeMEquivAlignedDecodeM
           (fun (b : ByteString) (cd : CacheDecode) =>
              match A_decode b cd with
              | Some (a, b', cd') => t a (if reset then b else b') (fcd cd cd')
              | None => u b cd
              end)
           (fun numBytes v idx cd =>
              match A_decode_aligned v idx cd with
              | Some (a, idx', cd') => t' a v (if reset then idx else idx') (fcd cd cd')
              | None => u' v idx cd
              end).
  Proof.
    setoid_rewrite DecodeMEquivAlignedDecodeM'_equiv.
    intros.
    eapply Seq_DecodeMEquivAlignedDecodeM'; eauto.
    destruct reset; eauto.
  Qed.

  Lemma AlignedDecode_Throw' {A} avail
    : DecodeMEquivAlignedDecodeM' avail
                                  (fun (_ : ByteString) (_ : CacheDecode) => None)
                                  (fun sz : nat => ThrowAlignedDecodeM (A := A)).
  Proof.
    unfold DecodeMEquivAlignedDecodeM'; intuition; try discriminate.
  Qed.

  Lemma AlignedDecode_Throw {A}
    : DecodeMEquivAlignedDecodeM (fun (_ : ByteString) (_ : CacheDecode) => None)
                                 (fun sz : nat => ThrowAlignedDecodeM (A := A)).
  Proof.
    setoid_rewrite DecodeMEquivAlignedDecodeM'_equiv.
    eauto using AlignedDecode_Throw'.
  Qed.

  Lemma Bind_DecodeMEquivAlignedDecodeM {A C : Type}
        (A_decode : DecodeM (A * ByteString) ByteString)
        (A_decode_aligned : forall {numBytes}, AlignedDecodeM A numBytes)
        (t : A -> DecodeM (C * ByteString) ByteString)
        (t' : A -> forall {numBytes}, AlignedDecodeM C numBytes)
    : DecodeMEquivAlignedDecodeM A_decode (@A_decode_aligned)
      -> (forall a, DecodeMEquivAlignedDecodeM (t a) (@t' a))
      -> DecodeMEquivAlignedDecodeM
           (fun (b : ByteString) (c : CacheDecode) =>
              `(a, bs, cd') <- A_decode b c; t a bs cd')
           (fun numBytes => BindAlignedDecodeM A_decode_aligned (fun a => @t' a numBytes)).
  Proof.
    intros.
    eapply DecodeMEquivAlignedDecodeM_trans.
    eapply Seq_DecodeMEquivAlignedDecodeM with
      (reset := false)
      (fcd := fun _ cd' => cd')
      (u := fun _ _ => None)
      (u' := fun _ _ _ _ => None); eauto using AlignedDecode_Throw.
    reflexivity.
    intros. hnf. intros.
    unfold BindAlignedDecodeM.
    destruct A_decode_aligned; simpl; intuition eauto.
  Qed.

  Lemma Bind_Duplicate_DecodeMEquivAlignedDecodeM {A C : Type}
        (A_decode : DecodeM (A * ByteString) ByteString)
        (A_decode_aligned : forall {numBytes}, AlignedDecodeM A numBytes)
        (t : A -> DecodeM (C * ByteString) ByteString)
        (t' : A -> forall {numBytes}, AlignedDecodeM C numBytes)
    : DecodeMEquivAlignedDecodeM A_decode (@A_decode_aligned)
      -> (forall a, DecodeMEquivAlignedDecodeM (t a) (@t' a))
      -> DecodeMEquivAlignedDecodeM
           (fun (b : ByteString) (c : CacheDecode) =>
              `(a, bs, cd') <- A_decode b c; t a b cd')
           (fun numBytes => BindResetAlignedDecodeM A_decode_aligned (fun a => @t' a numBytes)).
  Proof.
    intros.
    eapply DecodeMEquivAlignedDecodeM_trans.
    eapply Seq_DecodeMEquivAlignedDecodeM with
      (reset := true)
      (fcd := fun _ cd' => cd')
      (u := fun _ _ => None)
      (u' := fun _ _ _ _ => None); eauto using AlignedDecode_Throw.
    reflexivity.
    intros. hnf. intros.
    unfold BindResetAlignedDecodeM.
    destruct A_decode_aligned; simpl; intuition eauto.
  Qed.

  Lemma AlignedDecode_assoc {A B C : Type}
        (decode_A : DecodeM (A * ByteString) ByteString)
        (decode_B : A -> DecodeM (B * ByteString) ByteString)
        (decode_C : A -> B -> DecodeM (C * ByteString) ByteString)
        (aligned_decoder : forall numBytes : nat, AlignedDecodeM C numBytes)
    : DecodeMEquivAlignedDecodeM
        (fun bs cd => `(ab, bs', cd') <- (`(a, bs', cd') <- decode_A bs cd;
                                            `(b, bs', cd') <- decode_B a bs' cd';
                                            Some (a, b, bs', cd'));
                        decode_C (fst ab) (snd ab) bs' cd')
        aligned_decoder
      -> DecodeMEquivAlignedDecodeM
           (fun bs cd => `(a, bs', cd') <- decode_A bs cd;
                           `(b, bs', cd') <- decode_B a bs' cd';
                           decode_C a b bs' cd')
           aligned_decoder.
  Proof.
    intros; eapply DecodeMEquivAlignedDecodeM_trans; eauto;
      intros; simpl; try reflexivity.
    simpl; destruct (decode_A b cd) as [ [ [? ?] ?] | ]; simpl; eauto.
    destruct (decode_B a b0 c) as [ [ [? ?] ?] | ]; simpl; eauto.
  Qed.

  Lemma AlignedDecode_ifb_both' {A : Type} avail
        (decode_T decode_E : DecodeM (A * ByteString) ByteString)
        (cond : bool)
        (aligned_decoder_T
           aligned_decoder_E : forall numBytes : nat, AlignedDecodeM A numBytes)
    : DecodeMEquivAlignedDecodeM' avail decode_T aligned_decoder_T
      -> DecodeMEquivAlignedDecodeM' avail decode_E aligned_decoder_E
      -> DecodeMEquivAlignedDecodeM' avail
           (fun bs cd => if cond
                         then decode_T bs cd
                         else decode_E bs cd)
           (fun sz => if cond
                      then aligned_decoder_T sz
                      else aligned_decoder_E sz).
  Proof.
    intros; destruct cond; simpl; eauto using AlignedDecode_Throw.
  Qed.

  Lemma AlignedDecode_ifb_both {A : Type}
        (decode_T decode_E : DecodeM (A * ByteString) ByteString)
        (cond : bool)
        (aligned_decoder_T
           aligned_decoder_E : forall numBytes : nat, AlignedDecodeM A numBytes)
    : DecodeMEquivAlignedDecodeM decode_T aligned_decoder_T
      -> DecodeMEquivAlignedDecodeM decode_E aligned_decoder_E
      -> DecodeMEquivAlignedDecodeM
           (fun bs cd => if cond
                         then decode_T bs cd
                         else decode_E bs cd)
           (fun sz => if cond
                      then aligned_decoder_T sz
                      else aligned_decoder_E sz).
  Proof.
    setoid_rewrite DecodeMEquivAlignedDecodeM'_equiv.
    eauto using AlignedDecode_ifb_both'.
  Qed.

  Lemma AlignedDecode_ifb {A : Type}
        (decode_A : DecodeM (A * ByteString) ByteString)
        (cond : bool)
        (aligned_decoder : forall numBytes : nat, AlignedDecodeM A numBytes)
    : DecodeMEquivAlignedDecodeM
        decode_A
        aligned_decoder
      -> DecodeMEquivAlignedDecodeM
           (fun bs cd => if cond
                         then decode_A bs cd
                         else None)
           (fun sz => if cond
                      then aligned_decoder sz
                      else ThrowAlignedDecodeM).
  Proof.
    intros; destruct cond; simpl; eauto using AlignedDecode_Throw.
  Qed.

  Lemma AlignedDecode_ifopt
        {A A' : Type}
        (decode_A : A' -> DecodeM (A * ByteString) ByteString)
        (cond : option A')
        (aligned_decoder : A' -> forall numBytes : nat, AlignedDecodeM A numBytes)
    : (forall a', DecodeMEquivAlignedDecodeM
                    (decode_A a')
                    (aligned_decoder a'))
      -> DecodeMEquivAlignedDecodeM
           (fun bs cd => Ifopt cond as a'
                                         Then decode_A a' bs cd
                                         Else None)
           (fun sz => Ifopt cond as a'
                                      Then aligned_decoder a' _
                                      Else ThrowAlignedDecodeM).
  Proof.
    intros; destruct cond; simpl; eauto using AlignedDecode_Throw.
  Qed.

  Lemma AlignedDecode_Sumb {A : Type}
        (decode_A : DecodeM (A * ByteString) ByteString)
        (P : Prop)
        (cond : {P} + {~P})
        (aligned_decoder : forall numBytes : nat, AlignedDecodeM A numBytes)
    : DecodeMEquivAlignedDecodeM
        decode_A
        aligned_decoder
      -> DecodeMEquivAlignedDecodeM
           (fun bs cd => if cond
                         then decode_A bs cd
                         else None)
           (fun sz => if cond
                      then aligned_decoder sz
                      else ThrowAlignedDecodeM).
  Proof.
    intros; destruct cond; simpl; eauto using AlignedDecode_Throw.
  Qed.

  Ltac DecodeMEquivAlignedDecodeM_conv :=
    match goal with
    | |- DecodeMEquivAlignedDecodeM _ _ =>
        rewrite DecodeMEquivAlignedDecodeM'_equiv
    | |- DecodeMEquivAlignedDecodeM' ?avail _ _ =>
        generalize avail at 1; rewrite <- DecodeMEquivAlignedDecodeM'_equiv
    end.

  (* These bind lemmas are convenient when using the recursion combinator. *)
  Lemma Bind_DecodeMEquivAlignedDecodeM' {A C : Type} avail
        (A_decode : DecodeM (A * ByteString) ByteString)
        (A_decode_aligned : forall {numBytes}, AlignedDecodeM A numBytes)
        (t : A -> DecodeM (C * ByteString) ByteString)
        (t' : A -> forall {numBytes}, AlignedDecodeM C numBytes)
    : DecodeMEquivAlignedDecodeM' avail A_decode (@A_decode_aligned)
      -> (forall a, DecodeMEquivAlignedDecodeM (t a) (@t' a))%nat
      -> DecodeMEquivAlignedDecodeM' avail
           (fun (b : ByteString) (c : CacheDecode) =>
              `(a, bs, cd') <- A_decode b c; t a bs cd')
           (fun numBytes => BindAlignedDecodeM A_decode_aligned (fun a => @t' a numBytes)).
  Proof.
    intros.
    eapply DecodeMEquivAlignedDecodeM'_trans.
    eapply Seq_DecodeMEquivAlignedDecodeM' with
      (reset := false)
      (fcd := fun _ cd' => cd')
      (u := fun _ _ => None)
      (u' := fun _ _ _ _ => None); eauto using AlignedDecode_Throw'.

    intros. DecodeMEquivAlignedDecodeM_conv. eauto.

    reflexivity.
    intros. hnf. intros.
    unfold BindAlignedDecodeM.
    destruct A_decode_aligned; simpl; intuition eauto.
  Qed.

  (* This lemma is somewhat restricted, although good enough for our current
  applications. Ideally, we should allow [A_decode_aligned] to consume more than
  1 byte, i.e. [avail' < avail] and [idx < idx' <= n]. However, it is nontrival
  to support it. To do that, we probably need either or both of the following
  two generalizations:

  1. in [DecodeMEquivAlignedDecodeM'], instead of [avail = ...], we should write
  [avail <= ...]. In this case, the index [avail] no longer means the two
  decoders are equivalent on buffers with [avail] bytes available, but with _at
  least_ [avail] bytes available. We also need to update all combinator lemmas.

  2. we might need to show "continuous" property of [A_decode_aligned], i.e. it
  will return the same result given more fuels than [avail]. *)
  Lemma Bind_DecodeMEquivAlignedDecodeM_S {A C : Type} avail
        (A_decode : DecodeM (A * ByteString) ByteString)
        (A_decode_aligned : forall {numBytes}, AlignedDecodeM A numBytes)
        (t : A -> DecodeM (C * ByteString) ByteString)
        (t' : A -> forall {numBytes}, AlignedDecodeM C numBytes)
    : (forall n (v : ByteBuffer.t n) idx cd a idx' cd',
          A_decode_aligned v idx cd = Some (a, idx', cd') ->
          S idx = idx' /\ idx < n)%nat
      -> DecodeMEquivAlignedDecodeM' avail A_decode (@A_decode_aligned)
      -> (forall a avail',
             S avail' = avail ->
             DecodeMEquivAlignedDecodeM' avail' (t a) (@t' a))%nat
      -> DecodeMEquivAlignedDecodeM' avail
           (fun (b : ByteString) (c : CacheDecode) =>
              `(a, bs, cd') <- A_decode b c; t a bs cd')
           (fun numBytes => BindAlignedDecodeM A_decode_aligned (fun a => @t' a numBytes)).
  Proof.
    intros.
    eapply DecodeMEquivAlignedDecodeM'_trans.
    eapply Seq_DecodeMEquivAlignedDecodeM' with
      (reset := false)
      (fcd := fun _ cd' => cd')
      (u := fun _ _ => None)
      (u' := fun _ _ _ _ => None); eauto using AlignedDecode_Throw'.

    intros * H' ->.
    eapply H1. eapply H in H'.
    lia.

    reflexivity.
    intros. hnf. intros.
    unfold BindAlignedDecodeM.
    destruct A_decode_aligned; simpl; intuition eauto.
  Qed.

  Lemma AlignedDecode_avail_subst {A : Type} avail
        (dec : nat -> DecodeM (A * ByteString) ByteString)
        (aligned_dec : nat -> forall numBytes, AlignedDecodeM A numBytes)
    : DecodeMEquivAlignedDecodeM'
        avail
        (fun b cd => dec (bin_measure b / 8) b cd)
        (fun numBytes v idx cd =>
           aligned_dec (numBytes - idx) numBytes v idx cd) <->
        DecodeMEquivAlignedDecodeM'
          avail
          (dec avail)
          (aligned_dec avail).
  Proof.
    split; intros H.
    - split; [ | split ]; intros; subst; try eapply H;
        try rewrite build_aligned_ByteString_length in *; eauto.
      destruct H as [_ [_ ?]].
      specialize (H n).
      simpl in H.
      setoid_rewrite build_aligned_ByteString_length in H.
      rewrite Nat.sub_0_r in H.
      eauto.
    - split; [ | split ]; intros; subst; try eapply H;
        try rewrite build_aligned_ByteString_length in *; eauto.
      rewrite Nat.sub_0_r.
      eapply H. eauto.
  Qed.

  Lemma AlignedDecode_avail_subst_iter {A : Type} avail
        (bot : DecodeM (A * ByteString) ByteString)
        (body :
          DecodeM (A * ByteString) ByteString -> DecodeM (A * ByteString) ByteString)
        (aligned_body :
          forall numBytes, AlignedDecodeM A numBytes -> AlignedDecodeM A numBytes)
        (aligned_bot : forall numBytes, AlignedDecodeM A numBytes)
    : DecodeMEquivAlignedDecodeM'
        avail
        (fun b cd => Nat.iter (bin_measure b / 8) body bot b cd)
        (fun numBytes v idx cd =>
           Nat.iter (numBytes - idx) (aligned_body numBytes) (aligned_bot numBytes) v idx cd) <->
        DecodeMEquivAlignedDecodeM'
          avail
          (Nat.iter avail body bot)
          (fun numBytes => Nat.iter avail (aligned_body numBytes) (aligned_bot numBytes)).
  Proof.
    eapply AlignedDecode_avail_subst with
      (dec := fun n => Nat.iter n body bot)
      (aligned_dec := fun n numBytes => Nat.iter n (aligned_body numBytes) (aligned_bot numBytes)).
  Qed.

  Lemma AlignedDecode_iter' {A : Type}
        (bot : DecodeM (A * ByteString) ByteString)
        (body :
          DecodeM (A * ByteString) ByteString -> DecodeM (A * ByteString) ByteString)
        (aligned_body :
          forall numBytes, AlignedDecodeM A numBytes -> AlignedDecodeM A numBytes)
        (aligned_bot : forall numBytes, AlignedDecodeM A numBytes)
        (H0: DecodeMEquivAlignedDecodeM' 0 bot aligned_bot)
        (IH: forall avail,
            DecodeMEquivAlignedDecodeM'
              avail
              (Nat.iter avail body bot)
              (fun numBytes =>
                 Nat.iter avail (aligned_body numBytes) (aligned_bot numBytes)) ->
            DecodeMEquivAlignedDecodeM'
              (S avail)
              (body (Nat.iter avail body bot))
              (fun numBytes =>
                 aligned_body numBytes
                              (Nat.iter avail
                                        (aligned_body numBytes)
                                        (aligned_bot numBytes))))

    : forall avail,
      DecodeMEquivAlignedDecodeM'
        avail
        (fun b cd => Nat.iter (bin_measure b / 8) body bot b cd)
        (fun numBytes v idx cd =>
           Nat.iter (numBytes - idx)
                    (aligned_body numBytes)
                    (aligned_bot numBytes)
                    v idx cd).
  Proof.
    induction avail;
      rewrite AlignedDecode_avail_subst_iter in *; eauto.
  Qed.

  Lemma AlignedDecode_iter {A : Type}
        (bot : DecodeM (A * ByteString) ByteString)
        (body :
          DecodeM (A * ByteString) ByteString -> DecodeM (A * ByteString) ByteString)
        (aligned_body :
          forall numBytes, AlignedDecodeM A numBytes -> AlignedDecodeM A numBytes)
        (aligned_bot : forall numBytes, AlignedDecodeM A numBytes)
        (H0: DecodeMEquivAlignedDecodeM bot aligned_bot)
        (IH: forall rec aligned_rec avail,
            DecodeMEquivAlignedDecodeM' avail rec aligned_rec ->
            DecodeMEquivAlignedDecodeM'
              (S avail)
              (body rec)
              (fun numBytes => aligned_body numBytes (aligned_rec numBytes)))
    : DecodeMEquivAlignedDecodeM
        (fun b cd => Nat.iter (bin_measure b / 8) body bot b cd)
        (fun numBytes v idx cd =>
           Nat.iter (numBytes - idx)
                    (aligned_body numBytes)
                    (aligned_bot numBytes)
                    v idx cd).
  Proof.
    DecodeMEquivAlignedDecodeM_conv.
    eapply AlignedDecode_iter'; eauto.
    DecodeMEquivAlignedDecodeM_conv; eauto.
  Qed.

  Lemma AlignedDecode_iter_easy {A : Type}
        (body :
          DecodeM (A * ByteString) ByteString -> DecodeM (A * ByteString) ByteString)
        (aligned_body :
          forall numBytes, AlignedDecodeM A numBytes -> AlignedDecodeM A numBytes)
        (IH: forall rec aligned_rec avail,
            DecodeMEquivAlignedDecodeM' avail rec aligned_rec ->
            DecodeMEquivAlignedDecodeM'
              (S avail)
              (body rec)
              (fun numBytes => aligned_body numBytes (aligned_rec numBytes)))
    : DecodeMEquivAlignedDecodeM
        (fun b cd => Nat.iter (bin_measure b / 8) body (fun _ _ => None) b cd)
        (fun numBytes v idx cd =>
           Nat.iter (numBytes - idx)
                    (aligned_body numBytes)
                    ThrowAlignedDecodeM
                    v idx cd).
  Proof.
    eapply AlignedDecode_iter; eauto using AlignedDecode_Throw.
  Qed.

  Definition CorrectAlignedDecoder {S : Type}
             (predicate : S -> Prop)
             (format : FormatM S ByteString)
             (decoder : forall sz, AlignedDecodeM S sz)
    := {decodePlusCacheInv : _ &
                             (exists P_inv : (CacheDecode -> Prop) -> Prop,
                                 (cache_inv_Property (snd decodePlusCacheInv) P_inv ->
                                  CorrectDecoder _ predicate predicate eq format (fst decodePlusCacheInv) (snd decodePlusCacheInv) format) /\
                                 cache_inv_Property (snd decodePlusCacheInv) P_inv)
                             /\  DecodeMEquivAlignedDecodeM (fst decodePlusCacheInv) decoder}.

  Definition CorrectAlignedDecoderFor
             {S : Type}
             (predicate : S -> Prop)
             (format : FormatM S ByteString)
    := {decoder : forall sz, AlignedDecodeM S sz &
                             {decodePlusCacheInv : _ &
                                                   (exists P_inv : (CacheDecode -> Prop) -> Prop,
                                                       (cache_inv_Property (snd decodePlusCacheInv) P_inv ->
                                                        CorrectDecoder _ predicate predicate eq format (fst decodePlusCacheInv) (snd decodePlusCacheInv) format) /\
                                                       cache_inv_Property (snd decodePlusCacheInv) P_inv)
                                                   /\  DecodeMEquivAlignedDecodeM (fst decodePlusCacheInv) decoder} }.

  Lemma Refine_CorrectAlignedDecoderFormat
        {S}
    : forall (Invariant : S -> Prop)
             (FormatSpec FormatSpec'  : FormatM S ByteString),
      EquivFormat FormatSpec FormatSpec'
      -> CorrectAlignedDecoderFor Invariant FormatSpec
      -> CorrectAlignedDecoderFor Invariant FormatSpec'.
  Proof.
    unfold EquivFormat; intros.
    exists (projT1 X), (projT1 (projT2 X)).
    pose proof (projT2 (projT2 X)).
    abstract (split_and; destruct_ex; intuition eauto;
              eexists; split; eauto;
              intros; eapply Specs.format_decode_correct_alt;
              try first [unfold flip, impl, pointwise_relation; reflexivity
                        | unfold flip, impl, pointwise_relation; solve [eauto]
                        | eapply EquivFormat_sym; eassumption];
              eauto).
  Defined.

  Lemma Start_CorrectAlignedDecoderFor
        {S : Type}
        Invariant
        FormatSpec
        (decoder decoder_opt : DecodeM (S * _) ByteString)
        (decoderM : forall sz, AlignedDecodeM S sz)
        (cache_inv : CacheDecode -> Prop)
        (P_inv : (CacheDecode -> Prop) -> Prop)
        (decoder_OK :
           cache_inv_Property cache_inv P_inv
           -> CorrectDecoder (S := S) _ Invariant Invariant eq
                             FormatSpec decoder cache_inv FormatSpec)
        (cache_inv_OK : cache_inv_Property cache_inv P_inv)
        (decoder_opt_OK : forall b cd, decoder b cd = decoder_opt b cd)
        (monadized_decoder : DecodeMEquivAlignedDecodeM decoder_opt decoderM)
    : @CorrectAlignedDecoderFor S Invariant FormatSpec.
  Proof.
    exists decoderM.
    exists (decoder_opt, cache_inv); split. exists P_inv; split; simpl; eauto.
    unfold CorrectDecoder in *; intuition; intros.
    - destruct (H1 _ _ _ _ _ ext env_OK H0 H3 H4 ).
      rewrite decoder_opt_OK in H5; eauto.
    - rewrite <- decoder_opt_OK in H4; destruct (H2 _ _ _ _ _ _ H0 H3 H4); eauto.
    - rewrite <- decoder_opt_OK in H4; destruct (H2 _ _ _ _ _ _ H0 H3 H4); eauto.
    - apply monadized_decoder.
  Defined.

End AlignedDecodeM.

Lemma AlignedDecodeDuplicate  {C D : Type}
      {cache : Cache}
      (f : ByteString -> D)
      (f' : forall sz, ByteBuffer.t sz -> nat -> D)
      (t : D -> DecodeM (C * ByteString) ByteString)
      (t' : D -> forall {numBytes}, AlignedDecodeM C numBytes)
      (f'_OK : forall sz v n,
          (f' (S sz) v (S n) =
           f' sz (Vector.tl v) n))
  : (forall d,
        DecodeMEquivAlignedDecodeM (t d)
                                   (@t' d))
    -> (forall sz v, f (build_aligned_ByteString v) = f' sz v 0)
    -> DecodeMEquivAlignedDecodeM (fun v cd => t (f v) v cd)
                                  (fun numBytes v0 n => (@t' (f' _ v0 n) _ v0 n)).
Proof.
  unfold DecodeMEquivAlignedDecodeM; intros; intuition.
  - specialize (H (f' (S numBytes_hd) v (S n))); intuition.
    rewrite H1; eauto.
    rewrite f'_OK; eauto.
  - specialize (H (f (build_aligned_ByteString v))); intuition eauto.
  - specialize (H (f' _ v 0)); intuition.
    specialize (H4 n v cd); split_and.
    eapply H3.
    rewrite H0 in H1.
    eauto.
  - specialize (H (f' _ v 0)); intuition eauto.
    specialize (H4 n v cd); split_and.
    eapply H3 in H1.
    rewrite H0.
    eauto.
  - specialize (H (f' _ v 0)); intuition eauto.
    specialize (H4 n v cd); split_and.
    eapply H4.
    rewrite H0 in H1; eauto.
  - specialize (H (f' _ v 0)); intuition eauto.
    specialize (H4 n v cd); split_and.
    rewrite H0 in H1; eauto.
Qed.

Lemma AlignedDecodeBindDuplicate {A C D : Type}
      {cache : Cache}
      (decode_A : DecodeM (A * ByteString) ByteString)
      (f : ByteString -> D)
      (f' : forall sz, ByteBuffer.t sz -> nat -> D)
      (t : D -> A -> DecodeM (C * ByteString) ByteString)
      (t' : D -> forall {numBytes}, AlignedDecodeM C numBytes)
      (t'' : DecodeM (C * ByteString) ByteString)
  : (forall v cd, (`(a, t'', cd') <- decode_A v cd;
                        t (f v) a t'' cd') = t'' v cd)
    -> (forall d,
           DecodeMEquivAlignedDecodeM (fun v cd => `(a, t'', cd') <- decode_A v cd;
                                                     t d a t'' cd')
                                      (@t' d))
    -> (forall sz v, f (build_aligned_ByteString v) = f' sz v 0)
    -> (forall sz v idx, f' (S sz) v (S idx) = f' sz (Vector.tl v) idx)
    -> DecodeMEquivAlignedDecodeM t''
                                  (fun numBytes v0 idx => (@t' (f' _ v0 idx) _ v0 idx)).
Proof.
  intros.
  eapply DecodeMEquivAlignedDecodeM_trans.
  eapply AlignedDecodeDuplicate with (t0 := fun b (v : ByteString) (cd : CacheDecode) =>
                                              `(a, t'', cd') <- decode_A v cd;
                                              t b a t'' cd'); eauto.
  intros; simpl; apply H.
  intros; reflexivity.
Qed.

Lemma FindFuncBind {A C D : Type}
      {cache : Cache}
  : forall (decode_A : DecodeM (A * ByteString) ByteString)
           (t : A -> DecodeM (C * ByteString) ByteString)
           (t' : D -> A -> DecodeM (C * ByteString) ByteString)
           (d : D),
    (forall a t'' cd', (t a t'' cd') = t' d a t'' cd')
    ->  (forall v cd, (`(a, t'', cd') <- decode_A v cd; t a t'' cd')
                      = (`(a, t'', cd') <- decode_A v cd; t' d a t'' cd')).
Proof.
  intros.
  destruct (decode_A v cd) as [ [ [? ?] ?] | ]; simpl; eauto.
Qed.

Lemma FindFuncIf {A C D : Type}
      {cache : Cache}
  : forall
    (a : A)
    v
    cd
    (b : bool)
    (d : D)
    (f : D -> A -> bool)
    (tt' te' : option (C * ByteString * CacheDecode))
    (tt te : A -> DecodeM (C * ByteString) ByteString),
    (b = f d a)
    -> (tt' = tt a v cd)
    -> (te' = te a v cd)
    -> ((if b then tt' else te')
        = (fun (b' : A -> bool) a v cd => if b' a then tt a v cd else te a v cd) (f d) a v cd).
Proof.
  intros.
  rewrite H, H0, H1.
  eauto.
Qed.


Declare Scope AlignedDecodeM_scope.
Delimit Scope AlignedDecodeM_scope with AlignedDecodeM.
Notation "x <- y ; z" := (BindAlignedDecodeM y (fun x => z)) : AlignedDecodeM_scope.
Notation "'return' x" := (ReturnAlignedDecodeM x) (at level 10): AlignedDecodeM_scope.

Ltac DecodeMEquivAlignedDecodeM_conv :=
  match goal with
  | |- DecodeMEquivAlignedDecodeM _ _ =>
      rewrite DecodeMEquivAlignedDecodeM'_equiv
  | |- DecodeMEquivAlignedDecodeM' ?avail _ _ =>
      generalize avail at 1; rewrite <- DecodeMEquivAlignedDecodeM'_equiv
  end.
