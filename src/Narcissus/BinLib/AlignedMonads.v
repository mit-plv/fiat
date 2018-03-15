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
    Vector.t char n
    -> nat
    -> CacheDecode
    -> option (A * nat * CacheDecode).

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
                  f' v 0 cd = Some (c, n - (numBytes bs'), cd')))
       /\ (forall n m o (v : Vector.t (word 8) (n + (m + o))) cd c cd' H,
              f' v n cd = Some (c, o, cd') ->
              f (build_aligned_ByteString (snd (Vector_split n (m + o) v))) cd =
              Some (c, build_aligned_ByteString (snd (Vector_split (n + m) o (eq_rect _ _ v _ H))), cd')
          ).

  Lemma DecodeMEquivAlignedDecodeM_trans  {C} :
    forall bit_decoder1 byte_decoder1 bit_decoder2 byte_decoder2,
      DecodeMEquivAlignedDecodeM (C := C) bit_decoder1 byte_decoder1
      -> (forall b cd, bit_decoder1 b cd  = bit_decoder2 b cd)
      -> (forall n, AlignedDecodeMEquiv (byte_decoder1 n) (byte_decoder2 n))
      -> DecodeMEquivAlignedDecodeM bit_decoder2 byte_decoder2.
  Proof.
    unfold DecodeMEquivAlignedDecodeM; intros; intuition; rewrite <- ?H0, <- ?H1; eauto.
    - eapply H; rewrite H0; eauto.
    - eapply H3; rewrite H0; eauto.
    - eapply H3; rewrite H1; eauto.
    - eapply H3; rewrite H0; eauto.
    - eapply H5; rewrite H1; eauto.
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
    - unfold ReturnAlignedDecodeM in H0; injections; simpl.
      repeat f_equal.
  Admitted.

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
    - eapply DecodeBindOpt2_inv in H3; destruct_ex; intuition.
      specialize (H0 x); intuition.
      eapply H in H5.
      symmetry in H6; eapply H0 in H6; omega.
    - destruct (A_decode (build_aligned_ByteString v) cd) as [ [ [? ?] ?] | ] eqn: ?;
        simpl in *; try discriminate.
      unfold BindAlignedDecodeM.
      apply H2 in Heqo; destruct_ex; intuition; subst.
      rewrite Heqo; simpl; eauto.
      admit.
      unfold BindAlignedDecodeM; eapply H2 in Heqo; rewrite Heqo; reflexivity.
    - admit.
    - eapply DecodeBindOpt2_inv in H3; destruct_ex; intuition.
      eapply H2 in H5.
      unfold BindAlignedDecodeM; rewrite H5; simpl.
      symmetry in H6.
      specialize (H0 x); intuition.
      admit.
    - admit.
  Qed.

End AlignedDecodeM.

Delimit Scope AlignedDecodeM_scope with AlignedDecodeM.
Notation "x <- y ; z" := (BindAlignedDecodeM y (fun x => z)) : AlignedDecodeM_scope.
Notation "'return' x" := (ReturnAlignedDecodeM x) (at level 10): AlignedDecodeM_scope.
