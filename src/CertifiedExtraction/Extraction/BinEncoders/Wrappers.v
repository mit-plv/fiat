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
Require Import Bedrock.Word.

Unset Implicit Arguments.

(* FIXME move and use in more places, and generalize to other than ADTValue *)
Instance WrapSCA {A} {Wrp: FacadeWrapper W A} : FacadeWrapper (Value ADTValue) A.
Proof.
  refine {| wrap x := wrap (FacadeWrapper := FacadeWrapper_SCA) (wrap x);
            wrap_inj := _ |}; abstract (intros * H; repeat apply wrap_inj in H; assumption).
Defined.

Instance WrapWordList : FacadeWrapper ADTValue (list W).
Proof.
  refine {| wrap tl := WordList tl;
            wrap_inj := _ |}; abstract (inversion 1; reflexivity).
Defined.

Lemma map_inj {A B}:
  forall (f: A -> B),
    (forall x y, f x = f y -> x = y) ->
    (forall x y, (map f) x = (map f) y -> x = y).
Proof.
  induction x; destruct y; simpl; intros HH; try congruence.
  inversion HH; subst; f_equal; eauto.
Qed.

Instance WrapSCAList {A} {Wrp: FacadeWrapper W A} : FacadeWrapper (Value ADTValue) (list A) | 1.
Proof.
  refine {| wrap tl := wrap (FacadeWrapper := @WrapInstance _ _ WrapWordList) (map wrap tl);
            wrap_inj := _ |};
    abstract (intros * H; apply wrap_inj, map_inj in H; eauto using wrap_inj).
Defined.

Instance WrapByteIntoW : FacadeWrapper W byte | 2 :=
  (* Make this costly, to prefer byteStrings over lists of bytes as words *)
  {| wrap b := BtoW b;
     wrap_inj := BtoW_inj |}.

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

Lemma whd_wtl {n} :
  forall w: word (S n), w = WS (whd w) (wtl w).
Proof.
  intros.
  destruct (shatter_word_S w) as (b & w' & p).
  rewrite p; reflexivity.
Qed.

Lemma ByteToAscii_AsciiToByte :
  forall b, (AsciiToByte (ByteToAscii b)) = b.
Proof.
  intros; unfold ByteToAscii.
  shatter_word b; reflexivity.
Qed.

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

Lemma WrapListByte_inj {capacity} :
  forall v v' : byteString,
    ByteString capacity v = ByteString capacity v' ->
    v = v'.
Proof.
  inversion 1; eauto.
Qed.

Instance WrapListByte {capacity: W} : FacadeWrapper ADTValue byteString | 0 :=
  {| wrap bs := ByteString capacity bs;
     wrap_inj := WrapListByte_inj |}.

Open Scope nat_scope.

Lemma pow2_weakly_monotone : forall n m: nat,
    (n <= m)
    -> (pow2 n <= pow2 m).
Proof.
  induction 1; simpl; try change (pow2 (S m)) with (2 * pow2 m); intuition.
Qed.

Arguments pow2: simpl never.

Lemma BoundedN_below_pow2__le32 {size}:
  (size <= 32) ->
  forall v : BoundedN size,
    N.to_nat (proj1_sig v) < (pow2 32).
Proof.
  intros; destruct v; simpl; eapply Lt.lt_le_trans;
    eauto using N_below_pow2_nat, pow2_weakly_monotone.
Qed.

Lemma WrapN_le32_inj {av} {size}:
  (size <= 32) ->
  forall v v' : BoundedN size,
    wrap (FacadeWrapper := @FacadeWrapper_SCA av) (NToWord 32 (` v)) =
    wrap (FacadeWrapper := @FacadeWrapper_SCA av) (NToWord 32 (` v')) ->
    v = v'.
Proof.
  intros; rewrite !NToWord_nat in H0.
  apply wrap_inj, natToWord_inj, N2Nat.inj in H0;
  eauto using exist_irrel', UipComparison.UIP, BoundedN_below_pow2__le32.
Qed.

Definition WrapN_le32 {av} (n: nat) (p: n <= 32) : FacadeWrapper (Value av) (BoundedN n) :=
  {| wrap x := wrap (NToWord 32 (` x));
     wrap_inj := WrapN_le32_inj p |}.

Definition WrapN_error {av} (n: nat) : (if Compare_dec.le_dec n 32 then
                                        FacadeWrapper (Value av) (BoundedN n)
                                      else True).
  destruct (Compare_dec.le_dec n 32); auto using WrapN_le32.
Defined.

Instance WrapN8 : FacadeWrapper (Value ADTValue) (BoundedN 8) := WrapN_error 8.
Instance WrapN16 : FacadeWrapper (Value ADTValue) (BoundedN 16) := WrapN_error 16.

Lemma BoundedNat_below_pow2__le32 {size}:
  (size <= 32) ->
  forall v : BoundedNat size,
    (proj1_sig v) < (pow2 32).
Proof.
  intros; destruct v; simpl; eapply Lt.lt_le_trans;
    eauto using pow2_weakly_monotone.
Qed.

Theorem lt_uniqueness_proof : forall (n m : nat) (p q : n < m), p = q.
Proof.
  unfold lt.
  intros; apply Core.le_uniqueness_proof.
Qed.

Lemma WrapNatIntoW_le32_inj {size}:
  (size <= 32) ->
  forall v v' : BoundedNat size,
    (natToWord 32 (` v)) = (natToWord 32 (` v')) ->
    v = v'.
Proof.
  intros; apply natToWord_inj in H0;
    eauto using exist_irrel', lt_uniqueness_proof, BoundedNat_below_pow2__le32.
Qed.

Lemma WrapNat_le32_inj {av} {size}:
  (size <= 32) ->
  forall v v' : BoundedNat size,
    wrap (FacadeWrapper := @FacadeWrapper_SCA av) (natToWord 32 (` v)) =
    wrap (FacadeWrapper := @FacadeWrapper_SCA av) (natToWord 32 (` v')) ->
    v = v'.
Proof.
  intros * ? * H; apply wrap_inj in H.
  apply WrapNatIntoW_le32_inj; assumption.
Qed.

Definition WrapNatIntoW_le32 (n: nat) (p: n <= 32) : FacadeWrapper W (BoundedNat n) :=
  {| wrap x := (natToWord 32 (` x));
     wrap_inj := WrapNatIntoW_le32_inj p |}.

Definition WrapNat_le32 {av} (n: nat) (p: n <= 32) : FacadeWrapper (Value av) (BoundedNat n) :=
  {| wrap x := wrap (natToWord 32 (` x));
     wrap_inj := WrapNat_le32_inj p |}.

Definition WrapNatIntoW_error (n: nat) : (if Compare_dec.le_dec n 32 then
                                        FacadeWrapper W (BoundedNat n)
                                      else True).
  destruct (Compare_dec.le_dec n 32); auto using WrapNatIntoW_le32.
Defined.

(* Definition WrapNat_error {av} (n: nat) : (if Compare_dec.le_dec n 32 then *)
(*                                         FacadeWrapper (Value av) (BoundedNat n) *)
(*                                       else True). *)
(*   destruct (Compare_dec.le_dec n 32); auto using WrapNat_le32. *)
(* Defined. *)

Instance WrapNatIntoW8 : FacadeWrapper W (BoundedNat 8) := WrapNatIntoW_error 8.
Instance WrapNatIntoW16 : FacadeWrapper W (BoundedNat 16) := WrapNatIntoW_error 16.

(* Instance WrapNat8 : FacadeWrapper (Value ADTValue) (BoundedNat 8) := WrapNat_error 8. *)
(* Instance WrapNat16 : FacadeWrapper (Value ADTValue) (BoundedNat 16) := WrapNat_error 16. *)

Lemma WrapByte_BoundedNat8ToByte_WrapNat8_compat_1 :
  forall w,
    (wrap (BoundedNat8ToByte w) : W) = (wrap w : W).
Proof.
  intros.
  unfold wrap, WrapByteIntoW.
  rewrite BtoW_BoundedNat8ToByte_natToWord; reflexivity.
Qed.

Lemma WrapByte_BoundedNat8ToByte_WrapNat8_compat:
  forall w : BoundedNat 8,           (* Same as above, but wrapping into (Value …) instead of W  *)
    @wrap (Value ADTValue) byte (@WrapSCA byte WrapByteIntoW) (BoundedNat8ToByte w) =
    @wrap (Value ADTValue) (BoundedNat 8) (@WrapSCA (BoundedNat 8) WrapNatIntoW8) w.
Proof.
  unfold wrap, WrapSCA; intros; rewrite WrapByte_BoundedNat8ToByte_WrapNat8_compat_1; reflexivity.
Qed.

(* Instance WrapList {A B} {Wrp: FacadeWrapper A B} : FacadeWrapper (list A) (list B). *)
(* Proof. *)
(*   refine {| wrap x := map wrap x |}. *)
(*   abstract (eauto using map_inj, wrap_inj). *)
(* Defined. *)

Lemma WrapBoundedList_inj_1:
  forall (B : Type) (size : nat) (v v' : BoundedList B size), ` v = ` v' -> v = v'.
Proof.
  intros.
  apply exist_irrel'.
  - intros; apply lt_uniqueness_proof.
  - eassumption.
Qed.

Lemma WrapBoundedList_inj {A B : Type} {size : nat} {Wrp : FacadeWrapper A (list B)}:
  forall (v v' : BoundedList B size),
    wrap (` v) = wrap (` v') ->
    v = v'.
Proof.
  intros * H; apply wrap_inj, WrapBoundedList_inj_1 in H; assumption.
Qed.

Instance WrapBoundedList {A B size} {Wrp: FacadeWrapper A (list B)} : FacadeWrapper A (BoundedList B size) :=
  {| wrap bl := wrap (`bl);
     wrap_inj := WrapBoundedList_inj |}.

(* Lemma WrapTransitive {A A' A''} *)
(*       {WrpVal: FacadeWrapper A A'} *)
(*       {WrpList: FacadeWrapper A' A''} *)
(*   : FacadeWrapper A A''. *)
(* Proof. *)
(*   refine {| wrap a'' := wrap (wrap a''); *)
(*             wrap_inj := _ |}. *)
(*   abstract (intros * H; repeat apply wrap_inj in H; assumption). *)
(* Defined. *)

(* Typeclasses eauto := 10. *)

(* (* This one breaks TC resolution everywhere else *) *)
(* Definition WrapBoundedListOfBoundedNat {sl} : FacadeWrapper (Value ADTValue) (BoundedList (BoundedNat 8) sl). *)
(* Proof. *)
(*   eapply @WrapTransitive. *)
(*   - apply @WrapInstance. *)
(*     apply @WrapWordList. *)
(*   - apply @WrapBoundedList. *)
(*     apply @WrapList. *)
(*     apply @WrapNatIntoW8. *)
(* Defined. *)

(* Instance WrapListOfBoundedNat: FacadeWrapper (Value ADTValue) (list (BoundedNat 8)). *)
(* Proof. *)
(*   eapply @WrapTransitive. *)
(*   - apply @WrapInstance. *)
(*     apply @WrapWordList. *)
(*   - apply @WrapList. *)
(*     apply @WrapNatIntoW8. *)
(* Defined. *)
