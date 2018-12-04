Require Import
        Bedrock.Word
        Coq.omega.Omega
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
             (A : Set)
             (n : nat):=
    Vector.t char n (* Vector of bytes that is being decoded *)
    -> nat          (* The current vector index *)
    -> CacheDecode  (* The current environment *)
    -> option (A * nat * CacheDecode) (* Error monad + value + updated index + updated cache *).

  Definition BindAlignedDecodeM
             {A B : Set}
             {n : nat}
             (a : AlignedDecodeM A n)
             (b : A -> AlignedDecodeM B n)
    : AlignedDecodeM B n :=
    fun v idx c => (Ifopt a v idx c  as a' Then (b (fst (fst a')) v (snd (fst a')) (snd a')) Else None).

  Definition ReturnAlignedDecodeM
             {A : Set}
             {n : nat}
             (a : A)
    : AlignedDecodeM A n :=
    fun v idx c => Some (a, idx, c).

  Definition AlignedDecodeMEquiv
             {A} {n}
             (a1 a2 : AlignedDecodeM A n) : Prop :=
    forall v idx c, a1 v idx c = a2 v idx c.

  Lemma AlignedDecodeMEquiv_refl {A : Set} {n}:
    forall (a : AlignedDecodeM A n),
      AlignedDecodeMEquiv a a.
  Proof.
    unfold AlignedDecodeMEquiv; intros; reflexivity.
  Qed.

  Lemma AlignedDecodeMEquiv_sym {A : Set} {n}:
    forall (a1 a2 : AlignedDecodeM A n),
      AlignedDecodeMEquiv a1 a2 -> AlignedDecodeMEquiv a2 a1.
  Proof.
    unfold AlignedDecodeMEquiv; intros; congruence.
  Qed.

  Lemma AlignedDecodeMEquiv_trans {A : Set} {n}:
    forall (a1 a2 a3 : AlignedDecodeM A n),
      AlignedDecodeMEquiv a1 a2 ->
      AlignedDecodeMEquiv a2 a3 ->
      AlignedDecodeMEquiv a1 a3.
  Proof.
    unfold AlignedDecodeMEquiv; intros; congruence.
  Qed.

  Global Instance PreOrder_AlignedDecodeMEquiv {A : Set} {n} :
    PreOrder (@AlignedDecodeMEquiv A n) :=
    {| PreOrder_Reflexive := AlignedDecodeMEquiv_refl;
       PreOrder_Transitive := AlignedDecodeMEquiv_trans|}.

  Lemma BindAlignedDecodeM_assoc {A B C : Set} {n}:
    forall (a : AlignedDecodeM A n)
           (f : A -> AlignedDecodeM B n)
           (g : B -> AlignedDecodeM C n),
      AlignedDecodeMEquiv (BindAlignedDecodeM (BindAlignedDecodeM a f) g)
                          (BindAlignedDecodeM a (fun a => BindAlignedDecodeM (f a) g)).
  Proof.
    unfold BindAlignedDecodeM, AlignedDecodeMEquiv; simpl; intros.
    destruct (a v idx c); simpl; eauto.
  Qed.

  Lemma ReturnAlignedDecodeM_LeftUnit {A B : Set} {n}:
    forall (a : A)
           (f : A -> AlignedDecodeM B n),
      AlignedDecodeMEquiv (BindAlignedDecodeM (ReturnAlignedDecodeM a) f)
                          (f a).
  Proof.
    unfold ReturnAlignedDecodeM, BindAlignedDecodeM, AlignedDecodeMEquiv; simpl; intros.
    reflexivity.
  Qed.

  Lemma ReturnAlignedDecodeM_RightUnit {A B : Set} {n}:
    forall (f : AlignedDecodeM A n),
      AlignedDecodeMEquiv (BindAlignedDecodeM f ReturnAlignedDecodeM) f.
  Proof.
    unfold ReturnAlignedDecodeM, BindAlignedDecodeM, AlignedDecodeMEquiv; simpl; intros.
    destruct (f v idx c) as [ [ [? ?] ?] | ] ; simpl; reflexivity.
  Qed.

  Definition ThrowAlignedDecodeM
             {A : Set}
             {n : nat}
    : AlignedDecodeM A n:=
    fun _ _ _ => None.

  Fixpoint nth_opt
    {A : Set}
    {n : nat}
    (v : Vector.t A n)
    (m : nat)
    : option A :=
    match m, v with
    | 0,  Vector.cons a _ _ => Some a
    | S m', Vector.cons _ _ v' => nth_opt v' m'
    | _, _ => None
    end.

  Definition GetCurrentByte (* Gets the current byte and increments the current index. *)
             {n : nat}
    : AlignedDecodeM char n :=
    fun v idx c => Ifopt (nth_opt v idx) as b Then Some (b, S idx, addD c 8) Else None.

  (* Equivalence Criteria:
     A bit-aligned decoder and byte-aligned decoder are equivalent when
     - the byte aligned decoder fails when the bit aligned decoder does,
     - decodes the same values as the bit-aligned decoder
     - updates the cache in the same way as the bit-aligned decoder,
       - and consumes the same number of bytes as the bit-aligned decoder.
   *)

  Definition DecodeMEquivAlignedDecodeM
             {C : Set}
             (f : DecodeM C ByteString)
             (f' : forall {numBytes}, AlignedDecodeM C numBytes)
    := (forall {numBytes_hd}
               (n : nat)
               (v : Vector.t _ (S numBytes_hd)) cd,
           f' v (S n) cd =
           Ifopt (f' (Vector.tl v) n cd) as a Then Some (fst (fst a), S (snd (fst a)), snd a) Else None)
       /\ (forall b cd c b' cd', f b cd = Some (c, b', cd')
                                 -> length_ByteString b >= length_ByteString b')%nat
       /\ (forall n (v : Vector.t (word 8) n) cd,
              (f (build_aligned_ByteString v) cd = None <->
               f' v 0 cd = None)
              /\
              (forall c bs' cd',
                  f (build_aligned_ByteString v) cd = Some (c, bs', cd') ->
                  f' v 0 cd = Some (c, n - (numBytes bs'), cd')
                  /\ exists v' : Vector.t _ (n - (numBytes bs')),
                    (build_aligned_ByteString v) = ByteString_enqueue_ByteString (build_aligned_ByteString v') bs'
                                                                                 ))
              (*       /\ (forall n (v : Vector.t (word 8) n) cd c n' cd', *)
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

  Lemma Return_DecodeMEquivAlignedDecodeM {A : Set}
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
      simpl; repeat f_equal; omega.
    - unfold ReturnAlignedDecodeM in H; injections.
      assert ((n - numBytes (build_aligned_ByteString v)) = 0)
             by (unfold numBytes; simpl; omega).
      rewrite H.
      setoid_rewrite <- build_aligned_ByteString_append.
      simpl; eexists (@Vector.nil _); reflexivity.
  Qed.

  Lemma A_decode_aligned_shift {A : Set}
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

  (* Lemma A_decode_aligned_shift' {A : Set}
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
    : forall {n m} (v : Vector.t (word 8) (m + n)) (v1 : Vector.t char m) (v2 : Vector.t char n) cd,
      t' v2 0 cd = None ->
      build_aligned_ByteString v = build_aligned_ByteString (Vector.append v1 v2)  ->
      t' v m cd = None.
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

  Lemma proper_consumer_t_None' {C}
        (t' : forall {numBytes}, AlignedDecodeM C numBytes)
        (t'_OK : forall (numBytes_hd n0 : nat) (v0 : Vector.t char (S numBytes_hd)) (cd0 : CacheDecode),
            @t' (S numBytes_hd) v0 (S n0) cd0 =
            (Ifopt @t' numBytes_hd (Vector.tl v0) n0 cd0 as a0 Then
        Some (fst (fst a0), S (snd (fst a0)), snd a0) Else None))
    : forall {n m} (v : Vector.t (word 8) (m + n)) (v1 : Vector.t char m) (v2 : Vector.t char n) cd,
      t' v m cd = None ->
      build_aligned_ByteString v = build_aligned_ByteString (Vector.append v1 v2) ->
      t' v2 0 cd = None.

  Proof.
    intros.
    apply build_aligned_ByteString_inj in H0; subst.
    revert n v2 cd H; induction v1.
    - simpl; intros; eauto.
    - simpl; intros.
      rewrite t'_OK in H.
      eapply IHv1.
      simpl in *;
        destruct (t' (n + n0) (Vector.append v1 v2) n cd)
        as [ [ [? ?] ?] | ]; simpl in *; eauto; discriminate.
  Qed.

  Lemma proper_consumer_t_Some {C}
        (t' : forall {numBytes}, AlignedDecodeM C numBytes)
        (t'_OK : forall (numBytes_hd n0 : nat) (v0 : Vector.t char (S numBytes_hd)) (cd0 : CacheDecode),
            @t' (S numBytes_hd) v0 (S n0) cd0 =
            (Ifopt @t' numBytes_hd (Vector.tl v0) n0 cd0 as a0 Then
        Some (fst (fst a0), S (snd (fst a0)), snd a0) Else None))
    : forall {n m} (v : Vector.t (word 8) (m + n)) (v1 : Vector.t char m) (v2 : Vector.t char n) cd c k cd',
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

  Lemma Bind_DecodeMEquivAlignedDecodeM {A C : Set}
        (A_decode : DecodeM A ByteString)
        (A_decode_aligned : forall {numBytes}, AlignedDecodeM A numBytes)
        (t : A -> DecodeM C ByteString)
        (t' : A -> forall {numBytes}, AlignedDecodeM C numBytes)
    : DecodeMEquivAlignedDecodeM A_decode (@A_decode_aligned)
      -> (forall a, DecodeMEquivAlignedDecodeM (t a) (@t' a))
      -> DecodeMEquivAlignedDecodeM
     (fun (b : ByteString) (c : CacheDecode) =>
        `(a, bs, cd') <- A_decode b c; t a bs cd')
     (fun numBytes => BindAlignedDecodeM A_decode_aligned (fun a => @t' a numBytes)).
  Proof.
    unfold DecodeMEquivAlignedDecodeM; intros; intuition.
    - unfold BindAlignedDecodeM.
      rewrite H1.
      destruct (A_decode_aligned numBytes_hd (Vector.tl v) n cd) as [ [ [? ?] ?] | ]; simpl.
      + specialize (H0 a); intuition.
      + reflexivity.
    - eapply DecodeBindOpt2_inv in H2; destruct_ex; intuition.
      specialize (H0 x); intuition.
      eapply H in H4.
      symmetry in H5; eapply H0 in H5; omega.
    - destruct (A_decode (build_aligned_ByteString v) cd) as [ [ [? ?] ?] | ] eqn: ?;
        simpl in *; try discriminate.
      assert (numBytes b <= n)%nat as nb_le_n.
      { eapply H in Heqo.
        unfold build_aligned_ByteString, length_ByteString in Heqo; simpl in Heqo;
          omega. }
      unfold BindAlignedDecodeM.
      apply H3 in Heqo; destruct_ex; intuition; subst; destruct_ex.
      rewrite H4; simpl; eauto.
      specialize (H0 a); intuition.
      generalize (build_aligned_ByteString_split' _ _ _ H5); intros; destruct_ex.
      rewrite H7 in *.
      apply H8 in H2.
      assert ((n - (n - numBytes b)) = numBytes b).
      {rewrite sub_plus; try omega.
       rewrite H7; auto.
      }
      pose proof (fun v => proper_consumer_t_None (m := n - numBytes b) (t' a) H6 v x _ _ H2).
      assert (forall v0 : Vector.t (word 8) n,
        build_aligned_ByteString v0 = build_aligned_ByteString (Vector.append x x0) ->
        t' a n v0 (n - numBytes b) c = None).
      { revert H10; clear; intro.
        assert (n = n - numBytes b + (n - (n - numBytes b))) by omega.
        intros.
        specialize (H10 (eq_rect _ _ v0 _ H)).
        destruct H.
        eapply H10.
        apply H0.
      }
      replace (n - numBytes (build_aligned_ByteString x0)) with
          (n - numBytes b) by
          (unfold numBytes at 2; simpl; clear; omega).
      apply H11.
      rewrite H5.
      rewrite build_aligned_ByteString_append; f_equal; assumption.
      unfold BindAlignedDecodeM; apply H3 in Heqo; rewrite Heqo; reflexivity.
    - unfold BindAlignedDecodeM in H2.
      destruct (A_decode (build_aligned_ByteString v) cd) as [ [ [? ?] ?] | ] eqn: ? ;
        simpl in *; try eauto.
      assert (numBytes b <= n)%nat as nb_le_n.
      { eapply H in Heqo.
        unfold build_aligned_ByteString, length_ByteString in Heqo; simpl in Heqo;
          omega. }
      apply H3 in Heqo; destruct_ex; intuition; subst; destruct_ex.
      rewrite H4 in H2; simpl in H2; eauto.
      specialize (H0 a); intuition.
      generalize (build_aligned_ByteString_split' _ _ _ H5); intros; destruct_ex.
      rewrite H7 in *.
      apply H8.
      assert ((n - (n - numBytes b)) = numBytes b).
      {rewrite sub_plus; try omega.
       rewrite H7; auto.
      }
      assert (n = n - numBytes b + (n - (n - numBytes b))) by omega.
      eapply proper_consumer_t_None' with (v1 := x) (v0 := (eq_rect _ _ v _ H10)); eauto.
      revert H2; clear.
      destruct H10; simpl; intros.
      rewrite <- H2; f_equal; omega.
      revert H5 H7; clear; destruct H10; simpl; intros.
      rewrite H5, build_aligned_ByteString_append; f_equal; assumption.
    - eapply DecodeBindOpt2_inv in H2; destruct_ex; intuition.
      assert (numBytes x0 <= n)%nat as nb_le_n.
      { eapply H in H4.
        unfold build_aligned_ByteString, length_ByteString in H4; simpl in H4;
          omega. }
      assert (numBytes bs' <= numBytes x0)%nat as nbs_le_x0.
      { symmetry in H5.
        eapply H0 in H5.
        eapply H3 in H4; intuition; destruct_ex.
        generalize (build_aligned_ByteString_split' _ _ _ H4); intros; destruct_ex.
        rewrite H6 in H5.
        unfold length_ByteString in H5; simpl in H5.
        replace (n - (n - numBytes x0)) with (numBytes x0) in H5
          by (revert nb_le_n; clear; intro; omega).
        omega. }
      assert (numBytes bs' <= n)%nat as nbs_le_n.
      { etransitivity.
        apply nbs_le_x0.
        apply nb_le_n.
      }
      eapply H3 in H4.
      intuition.
      unfold BindAlignedDecodeM; rewrite H2; simpl; destruct_ex;
        intuition.
      symmetry in H5.
      specialize (H0 x); intuition.
      generalize (build_aligned_ByteString_split' _ _ _ H4); intros; destruct_ex.
      rewrite H7 in *|-*.
      eapply H8 in H5; intuition.
      unfold numBytes at 1; simpl.
      destruct_ex; intuition.
      assert (n = n - numBytes x0 + (n - (n - numBytes x0))) by omega.
      pose proof (proper_consumer_t_Some _ H6 (eq_rect _ _ v _ H10) x2 x3 _ _ _ _ H9).
      destruct H10.
      simpl in H11.
      assert (n >= numBytes x0)%nat by
          (rewrite H7; omega).
      replace (n - (n - numBytes x0)) with (numBytes x0) by omega.
      rewrite H11.
      f_equal; f_equal; f_equal.
      assert (numBytes x0 >= numBytes bs')%nat.
      rewrite H7; omega.
      omega.
      rewrite H4.
      rewrite build_aligned_ByteString_append; f_equal; eauto.
    - eapply DecodeBindOpt2_inv in H2; destruct_ex; intuition.
      assert (numBytes x0 <= n)%nat as nb_le_n.
      { eapply H in H4.
        unfold build_aligned_ByteString, length_ByteString in H4; simpl in H4;
          omega. }
      assert (numBytes bs' <= n)%nat as nbs_le_n.
      { symmetry in H5.
        eapply H0 in H5.
        eapply H3 in H4; intuition; destruct_ex.
        generalize (build_aligned_ByteString_split' _ _ _ H4); intros; destruct_ex.
        etransitivity.
        2: apply nb_le_n.
        rewrite H6 in H5.
        unfold length_ByteString in H5; simpl in H5.
        replace (n - (n - numBytes x0)) with (numBytes x0) in H5
          by (revert nb_le_n; clear; intro; omega).
        omega. }
      eapply H3 in H4; intuition; destruct_ex.
      setoid_rewrite H4.
      eapply build_aligned_ByteString_split' in H4; destruct_ex.
      rewrite H4 in *.
      symmetry in H5.
      eapply H0 in H5; intuition; destruct_ex.
      rewrite H5 in H4.
      assert ((n - numBytes x0 + (n - (n - numBytes x0) - numBytes bs')) =
              n - numBytes bs').
      { assert (n >= numBytes x0)%nat by
            (rewrite H4; rewrite H5 in nb_le_n; omega).
        replace (n - (n - numBytes x0)) with (numBytes x0).
        assert (numBytes x0 >= numBytes bs')%nat.
        { rewrite H4.
          generalize (build_aligned_ByteString_split' _ _ _ H5); intros; destruct_ex.
          replace (ByteString_enqueue_ByteString (build_aligned_ByteString x4) bs') with
              (build_aligned_ByteString (Vector.append x4 x5)).
          generalize x4 x5 H8; clear.
          generalize (n - (n - numBytes x0) - numBytes bs').
          intro.
          generalize (n - (n - numBytes x0) - n0); intros.
          rewrite H8.
          unfold numBytes; simpl; omega.
          rewrite build_aligned_ByteString_append; f_equal; eauto.
        }
        omega.
        omega.
      }
      generalize H7 H4; clear; intros.
      rewrite <- H7.
      eexists (Vector.append x2 x4).
      rewrite build_aligned_ByteString_append.
      rewrite <- ByteString_enqueue_ByteString_assoc.
      rewrite <- H4; reflexivity.
  Qed.

  Print Assumptions Bind_DecodeMEquivAlignedDecodeM.

End AlignedDecodeM.

Delimit Scope AlignedDecodeM_scope with AlignedDecodeM.
Notation "x <- y ; z" := (BindAlignedDecodeM y (fun x => z)) : AlignedDecodeM_scope.
Notation "'return' x" := (ReturnAlignedDecodeM x) (at level 10): AlignedDecodeM_scope.
