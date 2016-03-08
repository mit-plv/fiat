Require Export Coq.Strings.Ascii.
Require Import Coq.omega.Omega
               Fiat.BinEncoders.NoEnv.Specs
               Fiat.BinEncoders.NoEnv.Libraries.BinCore
               Fiat.BinEncoders.NoEnv.Libraries.FixInt.

Section CharBinEncoder.
  Definition Char_encode_inner (c : ascii) : bin_t.
    refine (@FixInt_encode_inner 8 (exist _ (N_of_ascii c) _)).
    unfold exp2; unfold exp2'.
    induction c.
    repeat (match goal with
              | B : bool |- _ => destruct B
            end); simpl; unfold Nlt; auto.
  Defined.

  Definition Char_decode b :=
    let (n, ext) := FixInt_decode 8 b
    in  (ascii_of_N (proj1_sig n), ext).

  Theorem Char_encode_correct : bin_encode_correct Char_encode_inner Char_decode.
  Proof.
    unfold bin_encode_correct, Char_encode_inner, Char_decode.
    intros c ext.
    rewrite FixInt_encode_correct; simpl.
    rewrite ascii_N_embedding. reflexivity.
  Qed.
End CharBinEncoder.

Definition Char_encode :=
  bin_encode_transform_pair Char_encode_inner.

Global Instance Char_decoder
  : decoder (fun _ => True) Char_encode :=
  bin_encode_transform_pair_decoder Char_encode_correct.