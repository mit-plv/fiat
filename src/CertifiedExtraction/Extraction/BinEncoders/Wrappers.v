Require Import Coq.Program.Program.

Require Import
        Fiat.CertifiedExtraction.Core
        Fiat.CertifiedExtraction.FacadeWrappers.
Require Import
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Basics
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Properties.
Require Import
        Bedrock.Arrays.
Require Export
        Bedrock.Platform.Facade.examples.QsADTs.

Instance WrapListResources : FacadeWrapper ADTValue (list resource_t). Admitted.
Instance WrapListQuestions : FacadeWrapper ADTValue (list question_t). Admitted.
Instance WrapQuestion : (FacadeWrapper ADTValue question_t). Admitted.
Instance WrapResource : (FacadeWrapper ADTValue resource_t). Admitted.
(* Instance WrapCache : (FacadeWrapper ADTValue DnsMap.CacheT). Admitted. *)
Instance WrapDMapT : FacadeWrapper ADTValue DnsMap.DMapT. Admitted.
Instance WrapEMapT : FacadeWrapper ADTValue DnsMap.EMapT. Admitted.
Instance WrapN : FacadeWrapper (Value ADTValue) N. Admitted.
Instance WrapListBool : FacadeWrapper ADTValue (list bool). Admitted.
Instance WrapListOfBoundedValues :
  (* FIXME when the elements of the list inject into W, we should have a
     canonical into lists of words. *)
  FacadeWrapper ADTValue {l : list (BoundedN 16) | Datatypes.length l < exp2_nat 16}. Admitted.

Lemma pow2_weakly_monotone : forall n m,
    (n <= m)%nat
    -> (Word.pow2 n <= Word.pow2 m)%nat.
Proof.
  induction 1; simpl; intuition.
Qed.

Lemma BoundedN_below_pow2__le32 {size}:
  size <= 32 ->
  forall v : BoundedN size,
    (lt (N.to_nat (proj1_sig v)) (Word.pow2 32)).
Proof.
  intros; eapply Lt.lt_le_trans;
    eauto using BoundedN_below_pow2, pow2_weakly_monotone, BoundedN_below_pow2.
Qed.

Lemma WrapN_le32_inj {av} {size}:
  size <= 32 ->
  forall v v' : BoundedN size,
    wrap (FacadeWrapper := @FacadeWrapper_SCA av) (Word.NToWord 32 (` v)) =
    wrap (FacadeWrapper := @FacadeWrapper_SCA av) (Word.NToWord 32 (` v')) ->
    v = v'.
Proof.
  intros; rewrite !Word.NToWord_nat in H0.
  apply wrap_inj, Word.natToWord_inj, N2Nat.inj in H0;
  eauto using exist_irrel', UipComparison.UIP, BoundedN_below_pow2__le32.
Qed.

Definition WrapN_le32 {av} (n: nat) (p: n <= 32) : FacadeWrapper (Value av) (BoundedN n) :=
  {| wrap x := wrap (Word.NToWord 32 (` x));
     wrap_inj := WrapN_le32_inj p |}.

Definition WrapN_error {av} (n: nat) : (if Compare_dec.le_dec n 32 then
                                        FacadeWrapper (Value av) (BoundedN n)
                                      else True).
  destruct (Compare_dec.le_dec n 32); auto using WrapN_le32.
Defined.

Instance WrapN8 : FacadeWrapper (Value ADTValue) (BoundedN 8) := WrapN_error 8.
Instance WrapN16 : FacadeWrapper (Value ADTValue) (BoundedN 16) := WrapN_error 16.

Require Import Word.

Fixpoint ExtendWord {size} (w: Word.word size) n : Word.word (n + size) :=
  match n with
  | O => w
  | S x => Word.WS false (ExtendWord w x)
  end.

Definition PadWord {s1} s2 (w: Word.word s1) : Word.word ((s2 - s1) + s1) :=
  ExtendWord w (s2 - s1).

Lemma ExtendWord_inj :
  forall s2 s1 w1 w2,
    @ExtendWord s1 w1 s2 = @ExtendWord s1 w2 s2 ->
    w1 = w2.
Proof.
  induction s2; simpl; intros.
  + assumption.
  + inversion H; auto using UipNat.inj_pair2.
Qed.

Lemma PadWord_inj :
  forall s1 s2 w1 w2,
    @PadWord s1 s2 w1 = @PadWord s1 s2 w2 ->
    w1 = w2.
Proof.
  eauto using ExtendWord_inj.
Qed.

Lemma WrapListBool_le32_inj {av} {size} {W: FacadeWrapper (Value av) (Word.word (32 - size + size))}:
  size <= 32 ->
  forall v v' : BitArray size,
    wrap (FacadeWrapper := W) (PadWord 32 (FixListBoolToWord v)) =
    wrap (FacadeWrapper := W) (PadWord 32 (FixListBoolToWord v')) ->
    v = v'.
Proof.
  eauto using FixListBoolToWord_inj, PadWord_inj, wrap_inj.
Qed.

Definition WrapListBool_le32 {av} (n: nat) (p: n <= 32) (W: FacadeWrapper (Value av) (Word.word (32 - n + n)))
  : FacadeWrapper (Value av) (BitArray n) :=
  {| wrap x := wrap (PadWord 32 (FixListBoolToWord x));
     wrap_inj := WrapListBool_le32_inj p |}.


Definition WrapListBool_error {av} (n: nat) (W: FacadeWrapper (Value av) (Word.word (32 - n + n))) :
  (if Compare_dec.le_dec n 32 then
     FacadeWrapper (Value av) (BitArray n)
   else True).
  destruct (Compare_dec.le_dec n 32); auto using WrapListBool_le32.
Defined.

Instance WrapListBool8 : FacadeWrapper (Value ADTValue) (BitArray 8) := WrapListBool_error 8 FacadeWrapper_SCA.
Instance WrapListBool16 : FacadeWrapper (Value ADTValue) (BitArray 16) := WrapListBool_error 16 FacadeWrapper_SCA.

Lemma le_minus_plus_cancel :
  forall {x y}, x <= y -> y = y - x + x.
Proof.
  intros; omega.
Qed.

Lemma WrapN_WrapListBool {av} {size} (p: size <= 32):
  forall s : BoundedN size,
    let wrapper := match le_minus_plus_cancel p in _ = y return FacadeWrapper (Value av) (Word.word y) with
                  | eq_refl => FacadeWrapper_SCA
                  end in
    wrap (FacadeWrapper := WrapN_le32 p) s =
    wrap (FacadeWrapper := WrapListBool_le32 p wrapper) (EncodeAndPad s).
Proof.
  induction size; simpl; intros.
  unfold wrap.
Admitted.

Lemma WrapN8_WrapListBool8:
  forall s : BoundedN 8,
    wrap (FacadeWrapper := WrapN8) s =
    wrap (FacadeWrapper := WrapListBool8) (EncodeAndPad s).
Proof.
Admitted.

Lemma WrapN16_WrapListBool16:
  forall s : BoundedN 16,
    wrap (FacadeWrapper := WrapN16) s =
    wrap (FacadeWrapper := WrapListBool16) (EncodeAndPad s).
Proof.
Admitted.

