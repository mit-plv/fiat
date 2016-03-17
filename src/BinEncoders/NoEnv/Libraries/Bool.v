Require Import Fiat.BinEncoders.NoEnv.Specs
               Fiat.BinEncoders.NoEnv.Libraries.BinCore.

Section BoolBinEncoder.
  Definition Bool_encode_inner (b : bool) : bin_t := b :: nil.

  Definition Bool_decode (b : bin_t) : bool * bin_t :=
    match b with
    | nil => (false, nil) (* bogus *)
    | x :: xs => (x, xs)
    end.

  Theorem Bool_encode_correct : bin_encode_correct Bool_encode_inner Bool_decode.
  Proof.
    unfold bin_encode_correct, Bool_encode_inner, Bool_decode.
    eauto.
  Qed.
End BoolBinEncoder.

Definition Bool_encode :=
  bin_encode_transform_pair Bool_encode_inner.

Global Instance Bool_decoder
  : decoder (fun _ => True) Bool_encode :=
  bin_encode_transform_pair_decoder Bool_encode_correct.