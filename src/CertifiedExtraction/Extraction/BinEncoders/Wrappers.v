Require Import Coq.Program.Program.

Require Import
        Fiat.CertifiedExtraction.Core
        Fiat.CertifiedExtraction.FacadeWrappers.
Require Import
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Basics
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Properties
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Map8.
Require Import
        Bedrock.Arrays.
Require Export
        Bedrock.Platform.Facade.examples.QsADTs.

Definition AsciiToByte (a: Ascii.ascii) : B :=
  match a with
  | Ascii.Ascii x x0 x1 x2 x3 x4 x5 x6 =>
    Word.WS x (Word.WS x0 (Word.WS x1 (Word.WS x2 (Word.WS x3 (Word.WS x4 (Word.WS x5 (Word.WS x6 Word.WO)))))))
  end.

Lemma AsciiToByte_ByteToAscii :
  forall a, (ByteToAscii (AsciiToByte a)) = a.
Proof.
  destruct a; reflexivity.
Qed.

Definition whd {n} (w: Word.word (S n)) :=
  match w with
    Word.WS b _ w' => b
  end.

Definition wtl {n} (w: Word.word (S n)) :=
  match w with
    Word.WS b _ w' => w'
  end.

Lemma whd_wtl {n} :
  forall w: Word.word (S n), w = Word.WS (whd w) (wtl w).
Proof.
  intros.
  refine (match w as w0 in (Word.word Sn)
                return (match Sn as Sn' return (Word.word Sn' -> Prop) with
                        | O => fun w0 => True
                        | S n => fun w => w = Word.WS (whd w) (wtl w)
                        end w0)
          with
          | Word.WO => I
          | Word.WS b _ w' => _
          end).
  reflexivity.
Qed.

Lemma WO_singleton :
  forall w : Word.word 0, Word.WO = w.
Proof.
  exact (fun w => match w as w0 in (Word.word zero)
                     return (match zero as z return Word.word z -> Prop with
                             | O => fun w: Word.word 0 => Word.WO = w
                             | S n => fun w: Word.word (S n) => True
                             end w0) with
               | Word.WO => eq_refl
               | Word.WS _ _ _ => I
               end).
Qed.

Lemma ByteToAscii_AsciiToByte :
  forall b, (AsciiToByte (ByteToAscii b)) = b.
Proof.
  intros; unfold ByteToAscii.
  repeat match goal with
         | [  |- context[match ?b with _ => _ end] ] => rewrite (whd_wtl b)
         end.
  simpl; repeat f_equal; apply WO_singleton.
Qed.

Print Assumptions ByteToAscii_AsciiToByte.

Lemma AsciiToByte_inj :
  forall a1 a2,
    AsciiToByte a1 = AsciiToByte a2 ->
    a1 = a2.
Proof.
  intros.
  rewrite <- (AsciiToByte_ByteToAscii a1), <- (AsciiToByte_ByteToAscii a2), H; reflexivity.
Qed.

Fixpoint StringToByteString s :=
  match s with
  | EmptyString => nil
  | String hd tl => cons (AsciiToByte hd) (StringToByteString tl)
  end.

Lemma StringToByteString_inj :
  forall s1 s2,
    StringToByteString s1 = StringToByteString s2 ->
    s1 = s2.
Proof.
  induction s1; destruct s2;
    repeat match goal with
           | _ => congruence
           | _ => progress intros
           | _ => progress simpl in *
           | _ => progress f_equal
           | _ => solve [eauto using AsciiToByte_inj]
           | [ H: cons _ _ = cons _ _ |- _ ] => inversion H; subst; clear H
           end.
Qed.

Lemma WrapString_inj {capacity} :
  forall v v' : string,
    ByteString capacity (StringToByteString v) =
    ByteString capacity (StringToByteString v') ->
    v = v'.
Proof.
  inversion 1; eauto using StringToByteString_inj.
Qed.

Definition WrapString {capacity: W} : FacadeWrapper ADTValue string :=
  {| wrap x := ByteString capacity (StringToByteString x);
     wrap_inj := WrapString_inj |}.

Instance WrapListResources : FacadeWrapper ADTValue (list resource_t). Admitted.
Instance WrapListQuestions : FacadeWrapper ADTValue (list question_t). Admitted.
Instance WrapQuestion : (FacadeWrapper ADTValue question_t). Admitted.
Instance WrapResource : (FacadeWrapper ADTValue resource_t). Admitted.
(* Instance WrapCache : (FacadeWrapper ADTValue DnsMap.CacheT). Admitted. *)
(* Instance WrapDMapT : FacadeWrapper ADTValue DnsMap.DMapT. Admitted. *)
(* Instance WrapEMapT : FacadeWrapper ADTValue DnsMap.EMapT. Admitted. *)

Instance WrapN : FacadeWrapper (Value ADTValue) N. Admitted.

(* Instance WrapListBool : FacadeWrapper ADTValue (list bool). Admitted. *)

Unset Implicit Arguments.

Require Import List.

Definition BoolsToB b0 b1 b2 b3 b4 b5 b6 b7 : B :=
  FixListBoolToWord (existT _ [b0; b1; b2; b3; b4; b5; b6; b7] eq_refl).

(* capacity introduced purely for TC resolution purposes *) (* FIXME does it work? *)
Definition BytableListOfBools (capacity: W) := { l: list bool & { p | List.length l = 8 * p } }.

Lemma WrapListBoolIntoListByte_inj:
  forall (capacity : W) (v v' : {l : list bool & {p : nat | Datatypes.length l = 8 * p} }),
    ByteString capacity (map8 BoolsToB false (projT1 v)) = ByteString capacity (map8 BoolsToB false (projT1 v')) ->
    v = v'.
Proof.
  intros; inversion H.
  eapply map8_inj; eauto.
  inversion 1; subst; intuition.
Qed.

Instance WrapListBoolIntoListByte {capacity: W} : FacadeWrapper ADTValue (BytableListOfBools capacity) :=
  {| wrap x := ByteString capacity (map8 BoolsToB false (projT1 x));
     wrap_inj := WrapListBoolIntoListByte_inj capacity |}.

Instance WrapListOfBoundedValues :
  (* FIXME when the elements of the list inject into W, we should have a
     canonical into lists of words. *)
  FacadeWrapper (Value ADTValue) (list (BoundedN 8)). Admitted.

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

Print IL.BtoW.

Definition PadWord {s1} s2 (w: Word.word s1) : Word.word ((s2 - s1) + s1) :=
  Word.combine (Word.wzero (s2 - s1)) w.

(* Lemma ExtendWord_inj : *)
(*   forall s2 s1 w1 w2, *)
(*     @ExtendWord s1 w1 s2 = @ExtendWord s1 w2 s2 -> *)
(*     w1 = w2. *)
(* Proof. *)
(*   induction s2; simpl; intros. *)
(*   + assumption. *)
(*   + inversion H; auto using UipNat.inj_pair2. *)
(* Qed. *)

Lemma Word_combine_inj1 {sz1 sz2}:
  forall w1 w2 w1' w2',
    @Word.combine sz1 w1 sz2 w2 = @Word.combine sz1 w1' sz2 w2' ->
    w1 = w1'.
Proof.
  intros; rewrite <- (Word.split1_combine w1 w2), H, Word.split1_combine; reflexivity.
Qed.

Lemma Word_combine_inj2 {sz1 sz2}:
  forall w1 w2 w1' w2',
    @Word.combine sz1 w1 sz2 w2 = @Word.combine sz1 w1' sz2 w2' ->
    w2 = w2'.
Proof.
  intros; rewrite <- (Word.split2_combine w1 w2), H, Word.split2_combine; reflexivity.
Qed.

Lemma PadWord_inj :
  forall s1 s2 w1 w2,
    @PadWord s1 s2 w1 = @PadWord s1 s2 w2 ->
    w1 = w2.
Proof.
  eauto using Word_combine_inj2.
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
    wrap (FacadeWrapper := WrapN_le32 _ p) s =
    wrap (FacadeWrapper := WrapListBool_le32 _ p wrapper) (EncodeAndPad s).
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

