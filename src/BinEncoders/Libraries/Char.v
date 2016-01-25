Require Export Coq.Strings.Ascii.
Require Import Coq.omega.Omega
               Fiat.BinEncoders.Specs
               Fiat.BinEncoders.Libraries.BinCore
               Fiat.BinEncoders.Libraries.FixInt.

Section CharBinEncoder.
  Definition Char_encode (c : ascii) : bin_t.
    refine (@FixInt_encode 8 (exist _ (N_of_ascii c) _)).
    unfold exp2; unfold exp2'.
    induction c.
    repeat (match goal with
              | B : bool |- _ => destruct B
            end); simpl; unfold Nlt; auto.
  Defined.

  Definition Char_decode b :=
    let (n, ext) := FixInt_decode 8 b
    in  (ascii_of_N (proj1_sig n), ext).

  Theorem Char_encode_correct : bin_encode_correct Char_encode Char_decode.
  Proof.
    unfold bin_encode_correct, Char_encode, Char_decode.
    intros c ext.
    rewrite FixInt_encode_correct; simpl.
    rewrite ascii_N_embedding. reflexivity.
  Qed.
End CharBinEncoder.
