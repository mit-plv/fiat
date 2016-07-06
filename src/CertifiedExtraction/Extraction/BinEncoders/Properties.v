Require Import CertifiedExtraction.Extraction.BinEncoders.Basics.

Definition encode_continue {E B}
           (transformer : Transformer.Transformer B)
           (encode : E -> B * E)
           acc :=
  let (p, e') := encode (snd acc) in
  (Transformer.transform (fst acc) p, e').

Definition compose_acc {E B}
           (transformer : Transformer.Transformer B)
           (encode1 : E -> B * E)
           (encode2 : E -> B * E) e0 :=
  encode_continue transformer encode2 (encode1 e0).

Lemma Compose_compose_acc {E B} :
  forall transformer encode1 encode2 e0,
    @Compose.compose E B transformer encode1 encode2 e0 =
    @compose_acc E B transformer encode1 encode2 e0.
Proof.
  intros; unfold compose_acc, Compose.compose, encode_continue.
  destruct (encode1 _); simpl; destruct (encode2 _); reflexivity.
Qed.

Fixpoint addE_n {H: Cache.Cache} {C: Cache.CacheAdd H N} n (cache: @Cache.CacheEncode H) : @Cache.CacheEncode H :=
  match n with
  | O => cache
  | S n => (addE_n n (Cache.addE cache 1%N))
  end.

Lemma IList_encode_bools_is_copy {H: Cache.Cache} {C: Cache.CacheAdd H N}:
forall bits (cache: @Cache.CacheEncode H),
  (IList.IList_encode' H Core.btransformer Bool.Bool_encode bits cache) =
  (bits, (addE_n (List.length bits) cache)).
Proof.
  induction bits; simpl in *.
  + reflexivity.
  + intros; rewrite (IHbits (Cache.addE cache 1%N)); reflexivity.
Qed.

Require Import Coq.Lists.List.
Require Import Bedrock.Word.

Fixpoint ListBoolToWord (bs: list bool) : word (List.length bs) :=
  match bs as l return (word (Datatypes.length l)) with
  | nil => WO
  | b :: bs0 => WS b (ListBoolToWord bs0)
  end.

Theorem exist_irrel : forall A (P : A -> Prop) x1 pf1 x2 pf2,
    (forall x (pf1' pf2' : P x), pf1' = pf2')
    -> x1 = x2
    -> exist P x1 pf1 = exist P x2 pf2.
Proof.
  intros; subst; f_equal; auto.
Qed.

Module DecidableNat.
  Definition U := nat.
  Definition eq_dec := Peano_dec.eq_nat_dec.
End DecidableNat.

Module UipNat := Eqdep_dec.DecidableEqDepSet(DecidableNat).

Lemma WS_commute : forall n1 n2 (pf : S n1 = S n2) b w,
    match pf in _ = n return word n with
    | eq_refl => WS b w
    end
    = WS b (match NPeano.Nat.succ_inj _ _ pf in _ = n return word n with
            | eq_refl => w
            end).
Proof.
  intros.
  pose proof (NPeano.Nat.succ_inj _ _ pf); subst.
  rewrite (UipNat.UIP _ _ pf eq_refl).
  rewrite (UipNat.UIP _ _ (NPeano.Nat.succ_inj _ _ eq_refl) eq_refl).
  reflexivity.
Qed.

Lemma WS_commute' {n1 n2} :
  forall (pf : n1 = n2) f (g: forall {n}, word n -> word (f n)) w,
    match pf in _ = n return word (f n) with
    | eq_refl => g w
    end
    = g (match pf in _ = n return word n with
            | eq_refl => w
            end).
Proof.
  destruct pf; reflexivity.
Qed.

Lemma ListBoolToWord_inj : forall n ls1 ls2 (pf1 : List.length ls1 = n) (pf2 : List.length ls2 = n),
    match pf1 in _ = n return word n with
    | eq_refl => ListBoolToWord ls1
    end
    = match pf2 in _ = n return word n with
      | eq_refl => ListBoolToWord ls2
      end
    -> ls1 = ls2.
Proof.
  induction n; destruct ls1, ls2; simpl; intuition; try congruence.
  repeat rewrite (WS_commute) in H.
  inversion H; clear H; subst.
  apply UipNat.inj_pair2 in H2.
  f_equal; eauto.
Qed.

Definition Word16ToWord32 (w: Word.word 16) : Word.word 32 :=
  w~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0.

Lemma Word16ToWord32_inj :
  forall w1 w2,
    Word16ToWord32 w1 = Word16ToWord32 w2 ->
    w1 = w2.
Proof.
  inversion 1; auto using UipNat.inj_pair2.
Qed.

Definition PadToLength encoded length :=
  FixInt.pad encoded (length - Datatypes.length encoded).

Lemma FixInt_pad_length :
  forall encoded delta,
    List.length (FixInt.pad encoded delta) = delta + List.length encoded.
Proof.
  induction delta; simpl; try rewrite IHdelta; reflexivity.
Qed.

Definition PadToLength_length encoded length :
  (List.length encoded <= length)%nat ->
  List.length (PadToLength encoded length) = length.
Proof.
  unfold PadToLength; rewrite FixInt_pad_length; omega.
Qed.

Lemma FixInt_encode'_length:
  forall (size : nat) (n : BoundedN size),
    (length (FixInt.encode' (proj1_sig n)) <= size)%nat.
Proof.
  destruct n; eauto using FixInt.encode'_size.
Qed.

Definition EncodeAndPad1 {size} (n: BoundedN size) : list bool :=
  let encoded := FixInt.encode' (proj1_sig n) in
  PadToLength encoded size.

Lemma EncodeAndPad1_length {size} (n: BoundedN size) :
  length (EncodeAndPad1 n) = size.
Proof.
  intros; eauto using PadToLength_length, FixInt_encode'_length.
Qed.

Definition EncodeAndPad {size} (n: BoundedN size) :
  {xs : list bool | length xs = size} :=
  exist _ (EncodeAndPad1 n) (EncodeAndPad1_length n).

Lemma FixInt_encode_is_copy {size} {H: Cache.Cache} {C: Cache.CacheAdd H N}:
  forall num (cache: @Cache.CacheEncode H),
    (FixInt.FixInt_encode (size := size) num cache) =
    (proj1_sig (EncodeAndPad num), Cache.addE cache (N.of_nat size)).
Proof.
  reflexivity.
Qed.

(* Lemma FixInt_encode_is_copy {size}: *)
(*   forall num cache, *)
(*     (FixInt.FixInt_encode (size := size) num cache) = *)
(*     (proj1_sig (EncodeAndPad num), {| DnsMap.eMap := DnsMap.eMap cache; *)
(*                                       DnsMap.dMap := DnsMap.dMap cache; *)
(*                                       DnsMap.offs := DnsMap.offs cache + (N.of_nat size) |}). *)
(* Proof. *)
(*   destruct cache. *)
(*   unfold FixInt.FixInt_encode. *)
(*   reflexivity. *)
(* Qed. *)

(* Inductive ListBoolEq : (list bool) -> (list bool) -> Prop := *)
(* | ListBoolEqLeft : forall l1 l2, ListBoolEq l1 l2 -> ListBoolEq (false :: l1) l2 *)
(* | ListBoolEqRight : forall l1 l2, ListBoolEq l1 l2 -> ListBoolEq l1 (false :: l2) *)
(* | ListBoolEqEq : forall l1 l2, l1 = l2 -> ListBoolEq l1 l2. *)

(* Hint Constructors ListBoolEq : listBoolEq. *)

Require Import Program.

Lemma N_le_succ_plus_1 : forall n m : N, (n + 1 <= m)%N <-> (n < m)%N.
Proof.
  intros; rewrite N.add_1_r.
  apply N.le_succ_l.
Qed.

Lemma N_lt_double_lt:
  forall p p' : N,
    (p < p')%N ->
    (2 * p < 2 * p')%N.
Proof.
  intros; apply N.mul_lt_mono_pos_l; eauto; reflexivity.
Qed.

Lemma N_le_double:
  forall p : N,
    (p <= 2 * p)%N.
Proof.
  intros; replace (2 * p)%N with (p + p)%N by ring.
  replace p with (0 + p)%N at 1 by ring.
  rewrite <- N.add_le_mono_r.
  apply N.le_0_l.
Qed.

Lemma N_lt_double:
  forall p : N,
    (0 < p)%N ->
    (p < 2 * p)%N.
Proof.
  intros; replace (2 * p)%N with (p + p)%N by ring.
  replace p with (0 + p)%N at 1 by ring.
  rewrite <- N.add_lt_mono_r.
  assumption.
Qed.

Lemma Pos_times_2_0:
  forall p : positive, (2 * N.pos p)%N = N.pos p~0.
Proof.
  reflexivity.
Qed.

Lemma Pos_times_2_1:
  forall p : positive, (2 * N.pos p + 1)%N = N.pos p~1.
Proof.
  reflexivity.
Qed.

Lemma FixInt_exp2_S_lt:
  forall (n : nat) (p : positive),
    (N.pos p < FixInt.exp2 n)%N ->
    (N.pos p~0 < FixInt.exp2 (S n))%N.
Proof.
  unfold FixInt.exp2; simpl; intros.
  rewrite <- (Pos_times_2_0 p).
  rewrite <- (Pos_times_2_0 (FixInt.exp2' _)).
  auto using N_lt_double_lt.
Qed.

Lemma FixInt_exp2_S_lt_strong:
  forall (n : nat) (p : positive),
    (N.pos p < FixInt.exp2 n)%N ->
    (N.pos p~1 < FixInt.exp2 (S n))%N.
Proof.
  unfold FixInt.exp2; simpl; intros.
  rewrite <- (Pos_times_2_1 p).
  rewrite <- (Pos_times_2_0 (FixInt.exp2' _)).
  auto using N.double_above.
Qed.

Lemma wordToN_bound {size} (w: Word.word size):
  (wordToN w < FixInt.exp2 size)%N.
Proof.
  dependent induction w; simpl.
  + reflexivity.
  + destruct b, (wordToN w); simpl;
    auto using FixInt_exp2_S_lt, FixInt_exp2_S_lt_strong.
Qed.

Definition wordToN_bounded {size} (w: Word.word size) :
  { n | (n < FixInt.exp2 size)%N } :=
  exist _ (wordToN w) (wordToN_bound w).

Definition FixInt_exp2_increasing_step :
  forall n,
    (FixInt.exp2 n < FixInt.exp2 (S n))%N.
Proof.
  unfold FixInt.exp2.
  intros; simpl; rewrite <- Pos_times_2_0.
  apply N_lt_double; reflexivity.
Qed.

Definition FixInt_exp2_increasing :
  forall n n',
    (n < n')%nat ->
    (FixInt.exp2 n < FixInt.exp2 n')%N.
Proof.
  induction 1.
  + apply FixInt_exp2_increasing_step.
  + etransitivity; eauto using FixInt_exp2_increasing_step.
Qed.


Lemma NToWord_of_nat:
  forall (sz : nat) (n : nat),
    NToWord _ (N.of_nat n) = natToWord sz n.
Proof.
  intros; rewrite NToWord_nat, Nat2N.id; reflexivity.
Qed.

Lemma NToWord_WordToN:
  forall (sz : nat) (w : word sz),
    NToWord _ (wordToN w) = w.
Proof.
  intros; rewrite NToWord_nat, wordToN_nat, Nat2N.id.
  apply natToWord_wordToNat.
Qed.

Open Scope nat_scope.

Lemma length_of_fixed_length_list {A} :
  forall {size} (ls: BoundedList A size),
    List.length (proj1_sig ls) < size.
Proof.
  destruct ls; auto.
Qed.

Module DecidableComparison.
  Definition U := comparison.
  Definition eq_dec : forall x y : comparison, {x = y} + {x <> y}.
    decide equality.
  Qed.
End DecidableComparison.

Module UipComparison := Eqdep_dec.DecidableEqDepSet(DecidableComparison).

Corollary exist_irrel' : forall A (P : A -> Prop) (x1: sig P) (x2: sig P),
    (forall x (pf1' pf2' : P x), pf1' = pf2')
    -> `x1 = `x2
    -> x1 = x2.
Proof.
  destruct x1, x2; eauto using exist_irrel.
Qed.

Arguments N.mul: simpl never.

Lemma FixInt_exp2_Word_Npow2 {size} :
  FixInt.exp2 size = Word.Npow2 size.
Proof.
  induction size; simpl.
  + reflexivity.
  + unfold FixInt.exp2 in *; simpl.
    rewrite <- Pos_times_2_0, IHsize; reflexivity.
Qed.

Lemma Npow2_nat' {size} :
  Npow2 size = N.of_nat (pow2 size).
Proof.
  intros; apply N2Nat.inj; rewrite Nat2N.id, Npow2_nat; reflexivity.
Qed.

Lemma FixInt_exp2_Word_pow2_N {size} :
  FixInt.exp2 size = N.of_nat (Word.pow2 size).
Proof.
  rewrite <- Npow2_nat'; apply FixInt_exp2_Word_Npow2.
Qed.

Lemma FixInt_exp2_Word_pow2_nat {size} :
  N.to_nat (FixInt.exp2 size) = Word.pow2 size.
Proof.
  rewrite FixInt_exp2_Word_pow2_N; apply Nat2N.id.
Qed.

Lemma N_below_pow2_N {size} :
  forall (n: N),
    (n < FixInt.exp2 size)%N ->
    (n < N.of_nat (Word.pow2 size))%N.
Proof.
  intros; rewrite <- FixInt_exp2_Word_pow2_N; assumption.
Qed.

Require Import Nomega.

Lemma N_below_pow2_nat {size} :
  forall (n: N),
    (n < FixInt.exp2 size)%N ->
    (N.to_nat n < (Word.pow2 size))%nat.
Proof.
  intros.
  rewrite <- FixInt_exp2_Word_pow2_nat.
  auto using Nlt_out.
Qed.

Lemma FixList_is_IList :
  forall (A bin : Type) (cache : Cache.Cache) (transformer : Transformer.Transformer bin)
    (A_encode : A -> Cache.CacheEncode -> bin * Cache.CacheEncode)
    (xs : list A) (env : Cache.CacheEncode),
    @FixList.FixList_encode' A bin cache transformer A_encode xs env =
    @IList.IList_encode' A bin cache transformer A_encode xs env.
Proof.
  induction xs; simpl; intros.
  + reflexivity.
  + destruct (A_encode _ _).
    rewrite IHxs; reflexivity.
Qed.

Lemma IList_encode'_body_as_compose {HD bin : Type} :
  forall (cache : Cache.Cache) (transformer : Transformer.Transformer bin) f acc (head: HD),
    (IList.IList_encode'_body cache transformer f acc head) = (* Cache parameter isn't used *)
    Compose.compose transformer (fun c => (fst acc, c)) (f head) (snd acc).
Proof.
  intros; unfold IList.IList_encode'_body, Compose.compose; simpl.
  destruct acc; simpl; destruct (f _ _); reflexivity.
Qed.


Lemma wordToNat_inj {sz} :
  forall (w1 w2: word sz),
    wordToNat w1 = wordToNat w2 ->
    w1 = w2.
Proof.
  intros * H.
  apply (f_equal (@natToWord sz)) in H.
  rewrite !natToWord_wordToNat in H.
  assumption.
Qed.

Lemma BoundedN_BoundedNat {sz} :
  forall x, lt x (pow2 sz) -> N.lt (N.of_nat x) (Npow2 sz).
Proof.
  intros.
  apply Nomega.Nlt_in.
  rewrite Nat2N.id, Npow2_nat.
  assumption.
Qed.

Lemma zext_inj {sz} {sz'} :
  forall (w w' : word sz),
    (zext w sz') = (zext w' sz') ->
    w = w'.
Proof.
  unfold zext; intros * H.
  apply (f_equal (@Word.split1 _ _)) in H.
  rewrite !split1_combine in H.
  assumption.
Qed.

Lemma BtoW_inj :
  forall (v v' : B),
    BtoW v = BtoW v' ->
    v = v'.
Proof.
  intros; eapply zext_inj; apply H.
Qed.

Lemma ByteString_transform_padding_0_left :
  forall str1 str2,
    padding str1 = 0 ->
    padding (transform str1 str2) = padding str2.
Proof.
  intros * H; rewrite transform_padding_eq, H.
  apply NPeano.Nat.mod_small.
  destruct str2; assumption.
Qed.

Lemma ByteString_transform_padding_0 :
  forall str1 str2,
    padding str1 = 0 ->
    padding str2 = 0 ->
    padding (transform str1 str2) = 0.
Proof.
  intros * H H'; rewrite transform_padding_eq, H, H'.
  reflexivity.
Qed.

Require Bedrock.IL.

Lemma encode_char' :
  forall w, encode_word' 8 w =
       {| front := WO;
          paddingOK := Lt.lt_0_Sn _;
          byteString := w :: nil |}.
Proof.
  intros; change 8 with (8+0); rewrite encode_char.
  shatter_word w; simpl; rewrite ByteString_transform_id_right.
  reflexivity.
Qed.

Definition BoundedNat8ToByte (w: BoundedNat 8) :=
  natToWord 8 (`w).

Lemma BtoW_BoundedNat8ToByte_natToWord :
  forall w,
    BtoW (BoundedNat8ToByte w) = natToWord 32 (` w).
Proof.
  intros; apply wordToN_inj.
  unfold BoundedNat8ToByte, BtoW, zext.
  rewrite (InternetChecksum.wordToN_extend 8 24).
  destruct w as (? & pr); rewrite !IL.natToWordToN.
  - reflexivity.
  - simpl; apply BoundedN_BoundedNat in pr;
    etransitivity; eauto; reflexivity.
  - apply BoundedN_BoundedNat; assumption.
Qed.

Lemma EncodeBoundedNat8_simplify : (* {cache} {cacheAddNat : CacheAdd cache nat} : *)
  forall (w: BoundedNat 8), (* (c: @CacheEncode cache), *)
    EncodeBoundedNat w tt =
    ({| padding := 0; front := WO; paddingOK := Lt.lt_0_Sn 7; byteString := (BoundedNat8ToByte w :: nil) |}, addE tt 8).
Proof.
  unfold EncodeBoundedNat, encode_word_Impl; intros.
  rewrite encode_char', NToWord_of_nat.
  reflexivity.
Qed.

Lemma EncodeBoundedNat8_padding_0 : (* {cache} {cacheAddNat : CacheAdd cache nat} : *)
  forall (w: BoundedNat 8), (* (c: @CacheEncode cache), *)
    padding (fst (EncodeBoundedNat w tt)) = 0.
Proof.
  intros; rewrite EncodeBoundedNat8_simplify; reflexivity.
Qed.

Lemma ByteString_transform_length :
  forall str1 str2,
    padding str1 = 0 ->
    padding str2 = 0 ->
    List.length (byteString (transform str1 str2)) =
    List.length (byteString str1) + List.length (byteString str2).
Proof.
  unfold transform, ByteStringTransformer; intros.
  rewrite ByteString_transformer_eq_app by assumption; simpl.
  rewrite app_length; reflexivity.
Qed.

Lemma EncodeBoundedNat8_length :
  forall (w: BoundedNat 8),
    List.length (byteString (fst (EncodeBoundedNat w tt))) = 1.
Proof.
  intros; rewrite EncodeBoundedNat8_simplify; reflexivity.
Qed.
