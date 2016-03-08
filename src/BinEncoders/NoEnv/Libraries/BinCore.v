Require Import Fiat.BinEncoders.NoEnv.Specs.

Set Implicit Arguments.

Definition bin_t := list bool.

Definition bin_encode_correct
           (data_t : Type)
           (encode : data_t -> bin_t)
           (decode : bin_t -> data_t * bin_t) :=
    forall data ext, decode (encode data ++ ext) = (data, ext).

Global Instance bin_encode_decoder
       (data_t : Type)
       (encode : data_t -> bin_t)
       (decode : bin_t -> data_t * bin_t)
       (encode_correct : bin_encode_correct encode decode)
  : decoder (fun _ => True) encode :=
  { decode := fun bin => fst (decode bin) }.
Proof.
  unfold encode_decode_correct.
  intros data pred.
  rewrite <- app_nil_r with (l:=encode data).
  rewrite encode_correct; eauto.
Defined.

Definition bin_encode_transform_pair
           (data_t : Type)
           (encode : data_t -> bin_t) :=
  fun bundle : data_t * bin_t => let (_data, _bin) := bundle
                                 in  encode _data ++ _bin.

Global Instance bin_encode_transform_pair_decoder
       (data_t : Type)
       (encode : data_t -> bin_t)
       (decode : bin_t -> data_t * bin_t)
       (encode_correct : bin_encode_correct encode decode)
  : decoder (fun _ => True) (bin_encode_transform_pair encode) :=
  { decode := decode }.
Proof.
  unfold encode_decode_correct, bin_encode_transform_pair.
  intros [data bin] pred.
  rewrite encode_correct; eauto.
Defined.
