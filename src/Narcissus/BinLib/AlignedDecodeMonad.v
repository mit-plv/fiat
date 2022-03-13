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

  Global Instance PreOrder_AlignedDecodeMEquiv {A : Type} {n} :
    PreOrder (@AlignedDecodeMEquiv A n) :=
    {| PreOrder_Reflexive := AlignedDecodeMEquiv_refl;
       PreOrder_Transitive := AlignedDecodeMEquiv_trans|}.

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
       /\ (forall b cd c b' cd', f b cd = Some (c, b', cd')
                                 -> length_ByteString b >= length_ByteString b')%nat
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

  Lemma DecodeMEquivAlignedDecodeM_trans  {C} :
    forall bit_decoder1 byte_decoder1 bit_decoder2 byte_decoder2,
      DecodeMEquivAlignedDecodeM (C := C) bit_decoder1 byte_decoder1
      -> (forall b cd, bit_decoder1 b cd  = bit_decoder2 b cd)
      -> (forall n, AlignedDecodeMEquiv (byte_decoder1 n) (byte_decoder2 n))
      -> DecodeMEquivAlignedDecodeM bit_decoder2 byte_decoder2.
  Proof.
    unfold DecodeMEquivAlignedDecodeM; intros; intuition; rewrite <- ?H0, <- ?H1; eauto.
    - eapply H; rewrite H0; eauto.
    - eapply H4; rewrite H0; eauto.
    - eapply H4; rewrite H1; eauto.
    - eapply H4; rewrite H0; eauto.
    - rewrite <- H0 in H3; apply H4 in H3; destruct H3 as [? [? ?] ];
        eauto.
  Qed.

  Lemma Return_DecodeMEquivAlignedDecodeM {A : Type}
        (a : A)
    : DecodeMEquivAlignedDecodeM
        (fun (b : ByteString) (cd : CacheDecode) => Some (a, b, cd))
        (fun numBytes => ReturnAlignedDecodeM a).
  Proof.
    unfold DecodeMEquivAlignedDecodeM; intros; intuition.
    - injections; eauto.
    - discriminate.
    - discriminate.
    - unfold ReturnAlignedDecodeM, numBytes; injections.
      simpl; repeat f_equal; lia.
    - unfold ReturnAlignedDecodeM in H; injections.
      assert ((n - numBytes (build_aligned_ByteString v)) = 0)
        by (unfold numBytes; simpl; lia).
      rewrite H.
      setoid_rewrite <- build_aligned_ByteString_append.
      simpl; eexists (@Vector.nil _); reflexivity.
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

  Lemma proper_consumer_t_None {C}
        (t' : forall {numBytes}, AlignedDecodeM C numBytes)
        (t'_OK : forall (numBytes_hd n0 : nat) (v0 : Vector.t char (S numBytes_hd)) (cd0 : CacheDecode),
            @t' (S numBytes_hd) v0 (S n0) cd0 =
            (Ifopt @t' numBytes_hd (Vector.tl v0) n0 cd0 as a0 Then
                                                               Some (fst (fst a0), S (snd (fst a0)), snd a0) Else None))
    : forall {n m} (v : ByteBuffer.t (m + n)) (v1 : Vector.t char m) (v2 : Vector.t char n) cd,
      build_aligned_ByteString v = build_aligned_ByteString (Vector.append v1 v2) ->
      t' v2 0 cd = None <->
      t' v m cd = None.
  Proof.
    intros.
    apply build_aligned_ByteString_inj in H; subst.
    revert n v2 cd; induction v1.
    - easy.
    - simpl; intros.
      rewrite t'_OK.
      rewrite IHv1.
      destruct t'; easy.
  Qed.

  Lemma proper_consumer_t_Some {C}
        (t' : forall {numBytes}, AlignedDecodeM C numBytes)
        (t'_OK : forall (numBytes_hd n0 : nat) (v0 : Vector.t char (S numBytes_hd)) (cd0 : CacheDecode),
            @t' (S numBytes_hd) v0 (S n0) cd0 =
            (Ifopt @t' numBytes_hd (Vector.tl v0) n0 cd0 as a0 Then
                                                               Some (fst (fst a0), S (snd (fst a0)), snd a0) Else None))
    : forall {n m} (v : ByteBuffer.t (m + n)) (v1 : Vector.t char m) (v2 : Vector.t char n) cd c k cd',
      t' v2 0 cd = Some (c, k, cd')
      -> build_aligned_ByteString v = build_aligned_ByteString (Vector.append v1 v2)
      -> t' v m cd = Some (c, m + k, cd').
  Proof.
    intros.
    apply build_aligned_ByteString_inj in H0; subst.
    revert n v2 cd H; induction v1.
    - simpl; intros; eauto.
    - simpl; intros.
      rewrite t'_OK.
      eapply IHv1 in H.
      simpl; rewrite H; reflexivity.
  Qed.

  Lemma Seq_DecodeMEquivAlignedDecodeM {A C : Type}
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
    intros Ha Ht Hu. split; [| split].
    - intros.
      rewrite (proj1 Ha).
      destruct A_decode_aligned as [ [[??]?] |]; simpl.
      2: eapply Hu; eauto.
      destruct reset; apply Ht.
    - intros ????? H.
      destruct A_decode as [ [[??]?] |] eqn:Heq; simpl.
      2: eapply Hu; eauto.
      repeat
        match goal with
        | H : context [ DecodeMEquivAlignedDecodeM _ _ ], Heq : _ = Some _ |- _ =>
            apply H in Heq
        end.
      destruct reset; lia.
    - intros n v cd.
      destruct A_decode as [ [[a b] cd'] |] eqn:Heq.
      2: eapply Ha in Heq; rewrite Heq; eapply Hu; eauto.

      assert (numBytes b <= n)%nat as L. {
        eapply (proj1 (proj2 Ha)) in Heq.
        eapply length_ByteString_le_numBytes in Heq; eauto.
      }

      eapply Ha in Heq.
      destruct Heq as [Heq [v' Hv]].
      rewrite Heq.
      destruct reset; try eapply Ht.
      rewrite Hv.

      destruct (build_aligned_ByteString_split' _ _ _ Hv) as [vb Hb].
      assert (numBytes b = n - (n - numBytes b)) as Hnb by lia.
      destruct Hnb.
      rewrite Hb in Hv at 2.
      rewrite <- build_aligned_ByteString_append in Hv.

      assert (n - numBytes b + numBytes b = n) as Hn by lia.
      revert dependent v. revert v'. revert Hn.
      generalize (n - numBytes b). intros m []. intros.

      split.
      + rewrite Hb at 1.
        rewrite <- proper_consumer_t_None; eauto; try eapply Ht.
      + intros ??? H.

        assert (numBytes bs' <= numBytes b)%nat. {
          apply Ht in H.
          eauto using length_ByteString_le_numBytes.
        }

        rewrite Hb in H.
        apply Ht in H. destruct H as [H [ v'' Hvb ]].
        eapply proper_consumer_t_Some in H; eauto; try apply Ht.
        rewrite H.
        rewrite <- Nat.add_sub_assoc by eauto.
        split; eauto.
        exists (Vector.append v' v'').
        rewrite !build_aligned_ByteString_append.
        rewrite <- ByteString_enqueue_ByteString_assoc.
        congruence.
  Qed.

  Lemma AlignedDecode_Throw {A}
    : DecodeMEquivAlignedDecodeM (fun (_ : ByteString) (_ : CacheDecode) => None)
                                 (fun sz : nat => ThrowAlignedDecodeM (A := A)).
  Proof.
    unfold DecodeMEquivAlignedDecodeM; intuition; try discriminate.
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
  - specialize (H (f b)); intuition eauto.
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
