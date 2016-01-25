Require Import Fiat.BinEncoders.Specs
               Fiat.BinEncoders.Libraries.BinCore.

Section BoolBinEncoder.
  Definition Bool_encode (b : bool) : bin_t := b :: nil.

  Definition Bool_decode (b : bin_t) : bool * bin_t :=
    match b with
    | nil => (false, nil) (* bogus *)
    | x :: xs => (x, xs)
    end.

  Theorem Bool_encode_correct : bin_encode_correct Bool_encode Bool_decode.
  Proof.
    unfold bin_encode_correct, Bool_encode, Bool_decode.
    eauto.
  Qed.
End BoolBinEncoder.
